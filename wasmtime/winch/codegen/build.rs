fn main() {
    if cfg!(feature = "x64") || cfg!(feature = "arm64") || cfg!(feature = "all-arch") {
        return;
    }

    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();

    if arch == "x86_64" {
        println!("cargo:rustc-cf-constructor=feature=\"x64\"");
    } else if arch == "aarch64" {
        println!("cargo:rustc-cf-constructor=feature=\"arm64\"");
    } else {
        println!("cargo:rustc-cf-constructor=feature=\"{arch}\"");
    }
    println!("cargo:rerun-if-changed=build.rs");
}
