# Rust-CLIPS

Rust bindings for the [CLIPS](https://clipsrules.net) expert system.

This repository is a Cargo workspace containing two crates:
- **`clips-sys`**: Low-level, unsafe FFI bindings generated via `bindgen` to the CLIPS C API.
- **`clips`**: A safe, idiomatic Rust wrapper around `clips-sys`, providing higher-level abstractions for working with CLIPS environments, rules, facts, and more.

## Features
- Automatic binding generation during build.
- Support for CLIPS core functionality (e.g., creating environments, asserting facts, running rules).
- Thread-safety considerations (CLIPS is not thread-safe by default; use with caution in multi-threaded contexts).
- Tested against CLIPS version 6.4 (update as needed).

## Requirements
To use CLIPS, you need to populate the `clips` directory with the CLIPS source code. You can do this by running the following commands:

```bash
wget -O clips_642.zip https://sourceforge.net/projects/clipsrules/files/CLIPS/6.4.2/clips_core_source_642.zip/download
unzip clips_642.zip -d clips_temp
mkdir clips
mv clips_temp/clips_core_source_642/core/* clips/
rm -rf clips_temp clips_642.zip
```

## Installation
Add to your `Cargo.toml` (assuming published to crates.io; otherwise use git/path dependencies):

```toml
[dependencies]
clips = "0.1.0"  # Or { path = "../rust-clips/clips" } for local dev