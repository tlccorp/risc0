use risc0_build::{embed_methods_with_options, GuestOptions};
use std::collections::HashMap;

fn main() {
    let inner_pkg_options = GuestOptions {
        code_limit: 10,
    };

    let map = HashMap::from([("risc0-zkvm-methods-inner", inner_pkg_options)]);

    embed_methods_with_options(map);
}
