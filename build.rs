use std::env;
use std::path::PathBuf;

const LIB_DIRS: [&str; 4] = [
    "/usr/lib64",
    "/usr/lib",
    "/usr/local/lib64",
    "/usr/local/lib",
];

const INCLUDE_DIRS: [&str; 2] = ["/usr/include", "/usr/local/include"];

fn find(env_var: &str, candidates: &[&str], file: &str) -> PathBuf {
    println!("cargo:rerun-if-env-changed={env_var}");
    let dirs: Vec<PathBuf> = match env::var_os(env_var) {
        Some(dir) => vec![PathBuf::from(dir)],
        None => candidates.iter().map(PathBuf::from).collect(),
    };
    for dir in &dirs {
        if dir.join(file).exists() {
            return dir.clone();
        }
    }
    panic!(
        "isa-l_crypto's {file} was not found in {}. Install isa-l_crypto, or set {env_var}.",
        dirs.iter()
            .map(|dir| dir.display().to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );
}

fn main() {
    let lib_dir = find("ISA_L_CRYPTO_LIB_DIR", &LIB_DIRS, "libisal_crypto.a");
    println!("cargo:rustc-link-lib=static=isal_crypto");
    println!("cargo:rustc-link-search=native={}", lib_dir.display());

    let include_dir = find("ISA_L_CRYPTO_INCLUDE_DIR", &INCLUDE_DIRS, "isa-l_crypto.h");
    let header = include_dir.join("isa-l_crypto.h");

    // Generate Rust bindings
    let bindings = bindgen::Builder::default()
        .header(header.to_str().expect("header path is not utf-8"))
        // isa-l_crypto.h includes <isa-l_crypto/*.h>, which clang finds only if
        // the chosen directory is on its search path.
        .clang_arg(format!("-I{}", include_dir.display()))
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
