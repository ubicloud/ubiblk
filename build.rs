// build.rs
use std::env;
use std::path::PathBuf;

fn main() {
    // Tell cargo to tell rustc to link the ISA-L Crypto library.
    println!("cargo:rustc-link-lib=dylib=isal_crypto");
    println!("cargo:rustc-link-search=/usr/lib");

    // The header file for ISA-L Crypto
    let header = "/usr/include/isa-l_crypto.h";

    // Generate the bindings.
    let bindings = bindgen::Builder::default()
        .header(header)
        // Depending on your needs, you might want to whitelist functions/types:
        // .whitelist_function("crypto_.*")
        // .whitelist_type("crypto_.*")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate ISA-L Crypto bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
