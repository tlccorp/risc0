use num_derive::FromPrimitive;

// This must match the mux in BodyStepImpl
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq, FromPrimitive)]
pub enum MajorType {
    Compute0 = 0,
    Compute1 = 1,
    Compute2 = 2,
    MemIO = 3,
    Multiply = 4,
    Divide = 5,
    VerifyAnd = 6,
    VerifyDivide = 7,
    ECALL = 8,
    ShaInit = 9,
    ShaLoad = 10,
    ShaMain = 11,
    Decode = 12,
}

#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq, FromPrimitive)]
pub enum ImmType {
    R,
    I,
    S,
    B,
    J,
    U,
}

// This must match rv32im.inl
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq, FromPrimitive)]
pub enum InsnKind {
    ADD = 0,    // add
    SUB = 1,    // sub
    XOR = 2,    // xor
    OR = 3,     // or
    AND = 4,    // and
    SLT = 5,    // set less than
    SLTU = 6,   // set less than (U)
    ADDI = 7,   // add immediate
    XORI = 8,   // xor immediate
    ORI = 9,    // or immediate
    ANDI = 10,  // and immediate
    SLTI = 11,  // set less than immediate
    SLTIU = 12, // set less than immediate (U)
    BEQ = 13,   // branch ==
    BNE = 14,   // branch !=
    BLT = 15,   // branch <
    BGE = 16,   // branch >=
    BLTU = 17,  // branch < (U)
    BGEU = 18,  // branch >= (U)
    JAL = 19,   // jump and link
    JALR = 20,  // jump and link reg
    LUI = 21,   // load upper immediate
    AUIPC = 22, // add upper immediate to PC
    LB = 24,    // load byte
    LH = 25,    // load half
    LW = 26,    // load word
    LBU = 27,   // load byte (U)
    LHU = 28,   // load half (U)
    SB = 29,    // store byte
    SH = 30,    // store half
    SW = 31,    // store word
    MUL = 32,   // mul
    MULH = 33,  // mul high
    MULSU = 34, // mul high (S) (U)
    MULU = 35,  // mul high (U)
    SLL = 36,   // shift left logical
    SLLI = 37,  // shift left logical immediate
    DIV = 40,   // div
    DIVU = 41,  // div (U)
    REM = 42,   // rem
    REMU = 43,  // rem (U)
    SRL = 44,   // shift right logical
    SRA = 45,   // shift right arthmetic
    SRLI = 46,  // shift right logical immediate
    SRAI = 47,  // shift right arthmetic immediate
    ECALL = 64, // environment call
}

impl InsnKind {
    pub fn get_major(&self) -> MajorType {
        use num_traits::FromPrimitive;
        FromPrimitive::from_u32((*self as u32) / 8).unwrap()
    }

    pub fn get_minor(&self) -> u32 {
        (*self as u32) % 8
    }

    pub fn get_imm_type(&self) -> ImmType {
        match *self {
            Self::ADD
            | Self::SUB
            | Self::XOR
            | Self::OR
            | Self::AND
            | Self::SLL
            | Self::SRL
            | Self::SRA
            | Self::SLT
            | Self::SLTU
            | Self::MUL
            | Self::MULH
            | Self::MULSU
            | Self::MULU
            | Self::DIV
            | Self::DIVU
            | Self::REM
            | Self::REMU => ImmType::R,
            Self::ADDI
            | Self::XORI
            | Self::ORI
            | Self::ANDI
            | Self::SLLI
            | Self::SRLI
            | Self::SRAI
            | Self::SLTI
            | Self::SLTIU
            | Self::LB
            | Self::LH
            | Self::LW
            | Self::LBU
            | Self::LHU
            | Self::JALR
            | Self::ECALL => ImmType::I,
            Self::SB | Self::SH | Self::SW => ImmType::S,
            Self::BEQ | Self::BNE | Self::BLT | Self::BGE | Self::BLTU | Self::BGEU => ImmType::B,
            Self::JAL => ImmType::J,
            Self::LUI | Self::AUIPC => ImmType::U,
        }
    }

    pub fn decode(inst: u32) -> Option<Self> {
        let opcode = inst & 0x0000007f;
        let funct3 = (inst & 0x00007000) >> 12;
        let funct7 = (inst & 0xfe000000) >> 25;
        // debug!("decode: 0x{word:08X}");

        match opcode {
            0b0000011 => match funct3 {
                0x0 => Some(Self::LB),
                0x1 => Some(Self::LH),
                0x2 => Some(Self::LW),
                0x4 => Some(Self::LBU),
                0x5 => Some(Self::LHU),
                _ => None,
            },
            0b0010011 => match funct3 {
                0x0 => Some(Self::ADDI),
                0x1 => Some(Self::SLLI),
                0x2 => Some(Self::SLTI),
                0x3 => Some(Self::SLTIU),
                0x4 => Some(Self::XORI),
                0x5 => match funct7 {
                    0x00 => Some(Self::SRLI),
                    0x20 => Some(Self::SRAI),
                    _ => None,
                },
                0x6 => Some(Self::ORI),
                0x7 => Some(Self::ANDI),
                _ => None,
            },
            0b0010111 => Some(Self::AUIPC),
            0b0100011 => match funct3 {
                0x0 => Some(Self::SB),
                0x1 => Some(Self::SH),
                0x2 => Some(Self::SW),
                _ => None,
            },
            0b0110011 => match (funct3, funct7) {
                (0x0, 0x00) => Some(Self::ADD),
                (0x0, 0x20) => Some(Self::SUB),
                (0x1, 0x00) => Some(Self::SLL),
                (0x2, 0x00) => Some(Self::SLT),
                (0x3, 0x00) => Some(Self::SLTU),
                (0x4, 0x00) => Some(Self::XOR),
                (0x5, 0x00) => Some(Self::SRL),
                (0x5, 0x20) => Some(Self::SRA),
                (0x6, 0x00) => Some(Self::OR),
                (0x7, 0x00) => Some(Self::AND),
                (0x0, 0x01) => Some(Self::MUL),
                (0x1, 0x01) => Some(Self::MULH),
                (0x2, 0x01) => Some(Self::MULSU),
                (0x3, 0x01) => Some(Self::MULU),
                (0x4, 0x01) => Some(Self::DIV),
                (0x5, 0x01) => Some(Self::DIVU),
                (0x6, 0x01) => Some(Self::REM),
                (0x7, 0x01) => Some(Self::REMU),
                _ => None,
            },
            0b0110111 => Some(Self::LUI),
            0b1100011 => match funct3 {
                0x0 => Some(Self::BEQ),
                0x1 => Some(Self::BNE),
                0x4 => Some(Self::BLT),
                0x5 => Some(Self::BGE),
                0x6 => Some(Self::BLTU),
                0x7 => Some(Self::BGEU),
                _ => None,
            },
            0b1100111 => match funct3 {
                0x0 => Some(Self::JALR),
                _ => None,
            },
            0b1101111 => Some(Self::JAL),
            0b1110011 => match (funct3, funct7) {
                (0x0, 0x0) => Some(Self::ECALL),
                _ => None,
            },
            _ => None,
        }
    }
}

impl ImmType {
    pub fn get_imm(&self, inst: u32) -> i32 {
        match self {
            Self::R => 0,
            Self::I => (inst as i32) >> 20,
            Self::S => ((inst & 0xfe000000) as i32 >> 20) | ((inst >> 7) & 0x1f) as i32,
            Self::B => {
                (
                    (((inst & 0x80000000) as i32 >> 19) as u32)
                    | ((inst & 0x80) << 4)   // imm[11]
                    | ((inst >> 20) & 0x7e0) // imm[10:5]
                    | ((inst >> 7) & 0x1e)
                    // imm[4:1]
                ) as i32
            }
            Self::J => {
                (
                    (((inst & 0x80000000) as i32  >> 11) as u32) // imm[20]
                    | (inst & 0xff000)        // imm[19:12]
                    | ((inst >> 9) & 0x800)   // imm[11]
                    | ((inst >> 20) & 0x7fe)
                    // imm[10:1]
                ) as i32
            }
            Self::U => (inst & 0xfffff000) as i32,
        }
    }
}
