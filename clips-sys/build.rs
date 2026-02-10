use std::path::PathBuf;
use std::{env, fs};

fn main() {
    // Check for the CLIPS_SOURCE_DIR environment variable
    println!("cargo:rerun-if-env-changed=CLIPS_SOURCE_DIR");
    let clips_source_dir = env::var("CLIPS_SOURCE_DIR").expect("Environment variable CLIPS_SOURCE_DIR is not set. Please set it to the path of the CLIPS source code directory.");
    let clips_source_path = PathBuf::from(&clips_source_dir);

    // 1. Compile CLIPS using the 'cc' crate
    let mut build = cc::Build::new();

    // Add all .c files in the clips_source directory
    let paths = fs::read_dir(&clips_source_path).unwrap_or_else(|e| panic!("Could not read clips_source directory at '{}': {}", clips_source_dir, e));

    for path in paths {
        let p = path.unwrap().path();
        if p.extension().map_or(false, |ext| ext == "c") {
            // Exclude main.c to avoid "multiple main functions" errors
            if p.file_name().unwrap() != "main.c" {
                build.file(&p);
            }
        }
    }
    build.include(&clips_source_path).warnings(false).compile("clips");

    // 2. Generate Bindings
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());

    // Construct the header path
    let header_path = clips_source_path.join("clips.h");

    let bindings = bindgen::Builder::default().header(header_path.to_string_lossy()).clang_arg(format!("-I{}", clips_source_dir)).parse_callbacks(Box::new(bindgen::CargoCallbacks::new())).generate().expect("Unable to generate bindings");
    bindings.write_to_file(out_path.join("bindings.rs")).expect("Couldn't write bindings!");

    // Tell Cargo to rerun if the C files change
    println!("cargo:rerun-if-changed={}", clips_source_dir);
}
