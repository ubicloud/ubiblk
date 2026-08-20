use std::env;
use std::path::{Path, PathBuf};

fn main() {
    // Link to the static version of isa-l_crypto
    println!("cargo:rustc-link-lib=static=isal_crypto");
    println!("cargo:rustc-link-search=native=/usr/lib");

    // The header file for ISA-L Crypto
    let header = "/usr/include/isa-l_crypto.h";
    if !Path::new(header).exists() {
        panic!("ISA-L Crypto header not found at {header}");
    }

    // Generate Rust bindings
    let bindings = bindgen::Builder::default()
        .header(header)
        // Don't emit bindings for libc runtime symbols pulled in via string.h;
        // they are provided by the standard library and redefining them trips
        // rustc's suspicious_runtime_symbol_definitions lint.
        .blocklist_function("memcpy|memmove|memset|memcmp|strlen|bcmp")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate ISA-L Crypto bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
