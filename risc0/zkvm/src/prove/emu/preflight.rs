// Copyright 2022 Risc0, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::collections::BTreeMap;
use std::vec::Vec;

use anyhow::{anyhow, bail, Result};
use log::debug;
use risc0_zkp::{core::fp::Fp, field::Elem, ZK_CYCLES};
use risc0_zkvm_platform::memory::SYSTEM;

use crate::prove::{
    loader::ControlIndex,
    opcode::{ImmType, InsnKind, MajorType},
};

pub struct Preflight {
    po2: usize,
    max_po2: usize,
    steps: usize,
    cycle: usize,
    out: Vec<u32>,
    mem: BTreeMap<u32, u32>,
    halted: bool,
    pc: u32,
    next_major: MajorType,
}

const PREFLIGHT_SIZE: usize = 10;

const IDX_PC: usize = 0;
const IDX_NEXT_MAJOR: usize = 1;
const IDX_MEM1: usize = 2;
const IDX_MEM2: usize = 3;
const IDX_MEM3: usize = 4;
const IDX_MEM4: usize = 5;
const IDX_MEM5: usize = 6;
const IDX_VAL2: usize = 6;

const REG_OFFSET: u32 = (SYSTEM.start() / 4) as u32;

impl Preflight {
    pub fn new(min_po2: usize, max_po2: usize) -> Self {
        let steps = 1 << min_po2;
        Self {
            po2: min_po2,
            max_po2,
            steps,
            cycle: 0,
            out: vec![0; steps * PREFLIGHT_SIZE],
            mem: BTreeMap::new(),
            halted: false,
            pc: 0,
            next_major: MajorType::Decode,
        }
    }

    fn expand(&mut self) -> Result<()> {
        if self.po2 >= self.max_po2 {
            bail!("Unable to expand, hit max po2")
        }
        let mut new_out = vec![0 as u32; self.out.len() * 2];
        for i in 0..PREFLIGHT_SIZE {
            let idx = i * self.steps;
            let src = &self.out[idx..idx + self.cycle];
            let tgt = &mut new_out[idx * 2..idx * 2 + self.cycle];
            tgt.copy_from_slice(src);
        }
        self.out = new_out;
        self.po2 += 1;
        self.steps *= 2;
        Ok(())
    }

    fn set_out(&mut self, idx: usize, val: u32) {
        self.out[self.steps * idx + self.cycle] = val;
    }

    fn do_compute(&mut self, kind: InsnKind, inst: u32) -> Result<()> {
        // Decode source + dest registers + imm
        let rd = match kind.get_imm_type() {
            ImmType::S | ImmType::B => 0,
            _ => (inst & 0x00000f80) >> 7,
        };
        let rs1 = (inst & 0x000f8000) >> 15;
        let rs2 = (inst & 0x01f00000) >> 20;

        // Get imm value
        let imm = kind.get_imm_type().get_imm(inst) as u32;

        // We always read 'rs1' and 'rs2' even if they don't make sense for this opcode
        let rs1_val = *self.mem.get(&(REG_OFFSET + rs1)).unwrap();
        self.set_out(IDX_MEM2, rs1_val);
        let rs2_val = *self.mem.get(&(REG_OFFSET + rs2)).unwrap();
        self.set_out(IDX_MEM3, rs2_val);
        debug!(
            "    imm = 0x{:08x}, rs1=x{} -> 0x{:x}, rs2=x{} -> 0x{:x}",
            imm, rs1, rs1_val, rs2, rs2_val
        );

        // Bitwise ops also need the val2 (i.e. IMM or RS2)
        let val2 = match kind.get_imm_type() {
            ImmType::I => imm,
            _ => rs2_val,
        };
        self.set_out(IDX_VAL2, val2);

        // Instructions can set new pc or reg output, and also next major
        let mut out = 0;
        let mut new_pc = self.pc + 4;
        let mut next_major = MajorType::Decode;
        let branch_pc = self.pc.wrapping_add(imm);

        // Now, we switch on the actual instruction and compute
        match kind {
            InsnKind::ADD | InsnKind::ADDI => {
                out = rs1_val.wrapping_add(val2);
            }
            InsnKind::SUB => {
                out = rs1_val.wrapping_sub(rs2_val);
            }
            InsnKind::XOR | InsnKind::XORI => {
                out = rs1_val ^ val2;
                next_major = MajorType::VerifyAnd;
            }
            InsnKind::OR | InsnKind::ORI => {
                out = rs1_val | val2;
                next_major = MajorType::VerifyAnd;
            }
            InsnKind::AND | InsnKind::ANDI => {
                out = rs1_val & val2;
                next_major = MajorType::VerifyAnd;
            }
            InsnKind::SLT | InsnKind::SLTI => {}
            InsnKind::SLTU | InsnKind::SLTIU => {}
            InsnKind::BEQ => {
                if rs1_val == rs2_val {
                    new_pc = branch_pc;
                }
            }
            InsnKind::BNE => {
                if rs1_val != rs2_val {
                    new_pc = branch_pc;
                }
            }
            InsnKind::BLT => {
                if (rs1_val as i32) < (rs2_val as i32) {
                    new_pc = branch_pc;
                }
            }
            InsnKind::BGE => {
                if (rs1_val as i32) >= (rs2_val as i32) {
                    new_pc = branch_pc;
                }
            }
            InsnKind::BLTU => {
                if rs1_val < rs2_val {
                    new_pc = branch_pc;
                }
            }
            InsnKind::BGEU => {
                if rs1_val >= rs2_val {
                    new_pc = branch_pc;
                }
            }
            InsnKind::JAL => {
                out = new_pc;
                new_pc = branch_pc;
            }
            InsnKind::JALR => {
                out = new_pc;
                new_pc = rs1_val.wrapping_add(imm);
            }
            InsnKind::LUI => {
                out = imm;
            }
            InsnKind::AUIPC => {
                out = self.pc.wrapping_add(imm);
            }
            _ => unreachable!(),
        }
        self.pc = new_pc;
        self.next_major = next_major;
        if rd != 0 {
            debug!("    Writing to rd=x{}, val = 0x{:x}", rd, out);
            self.mem.insert(REG_OFFSET + rd, out);
        }

        Ok(())
    }

    fn do_mem_io(&mut self, inst: u32) -> Result<()> {
        bail!("Unimplemented");
    }

    fn do_multiply(&mut self, inst: u32) -> Result<()> {
        bail!("Unimplemented");
    }

    fn do_divide(&mut self, inst: u32) -> Result<()> {
        bail!("Unimplemented");
    }

    fn do_verify_and(&mut self) -> Result<()> {
        bail!("Unimplemented");
    }

    fn do_verify_divide(&mut self) -> Result<()> {
        bail!("Unimplemented");
    }

    fn do_ecall(&mut self, inst: u32) -> Result<()> {
        // TODO: Actually properly implement ECALL, right now we just go into
        // a pretend halted state via failing to update the PC
        self.halted = true;
        Ok(())
    }

    fn do_sha(&mut self, major: MajorType) -> Result<()> {
        bail!("Unimplemented");
    }

    fn do_decode(&mut self) -> Result<()> {
        let inst = *self
            .mem
            .get(&(self.pc / 4))
            .ok_or(anyhow!("Failed to load instruction"))?;
        debug!(
            "{}: BODY @0x{:08x}: loaded 0x{:08x}",
            self.cycle, self.pc, inst
        );
        self.set_out(IDX_MEM1, inst);
        let kind = InsnKind::decode(inst).ok_or(anyhow!("Failed to decode instruction"))?;
        match kind.get_major() {
            MajorType::Compute0 | MajorType::Compute1 | MajorType::Compute2 => {
                self.do_compute(kind, inst)
            }
            MajorType::MemIO => self.do_mem_io(inst),
            MajorType::Multiply => self.do_multiply(inst),
            MajorType::Divide => self.do_divide(inst),
            MajorType::ECALL => self.do_ecall(inst),
            _ => unreachable!(),
        }
    }

    fn do_body(&mut self) -> Result<()> {
        match self.next_major {
            MajorType::Decode => self.do_decode(),
            MajorType::VerifyAnd => self.do_verify_and(),
            MajorType::VerifyDivide => self.do_verify_divide(),
            MajorType::ShaInit | MajorType::ShaLoad | MajorType::ShaMain => {
                self.do_sha(self.next_major)
            }
            _ => unreachable!(),
        }
    }

    pub fn step(&mut self, code: &[Fp], needed_fini: usize) -> Result<bool> {
        if self.cycle + needed_fini + ZK_CYCLES >= self.steps {
            if self.halted {
                return Ok(false);
            }
            self.expand()?;
        }
        if code[ControlIndex::Body as usize] != Fp::ZERO {
            self.do_body()?;
        } else if code[ControlIndex::RamLoad as usize] != Fp::ZERO {
            let addr = u32::from(code[ControlIndex::Info as usize]);
            let data1 = u32::from(code[ControlIndex::Data1Lo as usize])
                | (u32::from(code[ControlIndex::Data1Hi as usize]) << 16);
            let data2 = u32::from(code[ControlIndex::Data2Lo as usize])
                | (u32::from(code[ControlIndex::Data2Hi as usize]) << 16);
            let data3 = u32::from(code[ControlIndex::Data3Lo as usize])
                | (u32::from(code[ControlIndex::Data3Hi as usize]) << 16);
            self.mem.insert(addr, data1);
            self.mem.insert(addr + 1, data2);
            self.mem.insert(addr + 2, data3);
            // debug!("{}: RAMLOAD, addr = 0x{:08x}: 0x{:08x}, 0x{:08x},
            // 0x{:08x}", self.cycle, addr * 4, data1, data2, data3);
        } else if code[ControlIndex::Reset as usize] != Fp::ZERO {
            self.pc = u32::from(code[ControlIndex::Info as usize]);
            debug!("{}: RESET, PC = 0x{:08x}", self.cycle, self.pc);
        }
        self.set_out(IDX_PC, self.pc);
        self.set_out(IDX_NEXT_MAJOR, self.next_major as u32);
        self.cycle += 1;
        return Ok(true);
    }
}

#[cfg(test)]

mod tests {
    use std::path::Path;

    use anyhow::Result;
    use log::debug;
    use risc0_zkp::{core::log2_ceil, MAX_CYCLES_PO2, ZK_CYCLES};
    use risc0_zkvm_platform::memory::MEM_SIZE;
    use test_log::test;

    use super::Preflight;
    use crate::elf::Program;
    use crate::prove::loader::load_code;

    fn run_one_test(path: &Path) -> Result<()> {
        debug!("Running {}", path.display());
        let elf_contents = std::fs::read(path)?;
        let elf = Program::load_elf(&elf_contents, MEM_SIZE as u32)?;
        let min_po2 = log2_ceil(1570 + elf.image.len() / 3 + ZK_CYCLES);
        let mut preflight = Preflight::new(min_po2, MAX_CYCLES_PO2);
        load_code(elf.entry, &elf.image, |code, fini| {
            preflight.step(code, fini)
        })?;
        Ok(())
    }

    #[test]
    fn run_tests() -> Result<()> {
        let mut bins_path = std::env::current_dir()?;
        bins_path.push("../../riscv-test-bins");
        let read_dir = bins_path.read_dir()?;
        for entry in read_dir {
            if let Ok(entry) = entry {
                if entry.file_name() != "jalr" {
                    continue;
                }
                run_one_test(&entry.path())?;
            }
        }
        Ok(())
    }
}
