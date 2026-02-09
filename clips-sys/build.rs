use std::path::PathBuf;
use std::{env, fs};

fn main() {
    // 1. Compile CLIPS using the 'cc' crate
    let mut build = cc::Build::new();

    // Add all .c files in the ../clips_source directory
    let paths = fs::read_dir("../clips_source").expect("Could not read /clips directory");
    for path in paths {
        let p = path.unwrap().path();
        if p.extension().map_or(false, |ext| ext == "c") {
            // Exclude main.c to avoid "multiple main functions" errors
            if p.file_name().unwrap() != "main.c" {
                build.file(&p);
            }
        }
    }

    build
        .include("clips")
        .warnings(false) // CLIPS has many legacy C warnings we can ignore
        .compile("clips"); // This creates libclips.a and links it automatically

    // 2. Generate Bindings
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    let bindings = bindgen::Builder::default()
        .header("../clips_source/clips.h")
        .clang_arg("-Iclips")
        // Useful for build.rs to notify cargo when to rerun
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate bindings");

    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");

    // Tell Cargo to rerun if the C files change
    println!("cargo:rerun-if-changed=clips_source/");
}
