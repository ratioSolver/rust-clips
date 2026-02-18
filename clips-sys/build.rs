use std::path::PathBuf;
use std::{env, fs};

fn main() {
    println!("cargo:rerun-if-env-changed=CLIPS_SOURCE_DIR");
    let clips_source_dir = env::var("CLIPS_SOURCE_DIR").expect("Environment variable CLIPS_SOURCE_DIR is not set.");
    let clips_source_path = PathBuf::from(&clips_source_dir);

    // 1. Compile CLIPS
    let mut build = cc::Build::new();
    let paths = fs::read_dir(&clips_source_path).expect("Could not read clips_source directory");

    for path in paths {
        let p = path.unwrap().path();
        if p.extension().map_or(false, |ext| ext == "c") {
            if p.file_name().unwrap() != "main.c" {
                build.file(&p);
            }
        }
    }

    build.include(&clips_source_path).warnings(false).compile("clips"); // This automatically tells cargo to link libclips.a

    // 2. Generate Bindings
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    println!("cargo:rustc-link-search=native={}", out_path.display());

    let header_path = clips_source_path.join("clips.h");
    let bindings = bindgen::Builder::default().header(header_path.to_string_lossy()).clang_arg(format!("-I{}", clips_source_dir)).parse_callbacks(Box::new(bindgen::CargoCallbacks::new())).generate().expect("Unable to generate bindings");

    bindings.write_to_file(out_path.join("bindings.rs")).expect("Couldn't write bindings!");

    println!("cargo:rerun-if-changed={}", clips_source_dir);
}
