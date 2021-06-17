use std::env;
use std::path::PathBuf;

// Our top-level package version comes from the VERSION text file at the root
// of our repo, we don't use this crate's version
const PACKAGE_VERSION: &str = include_str!("../VERSION");

fn main() {
    // NOTE: use the desired shared object name here, not the crate name,
    // we do this so we don't have to run `patchelf --set-soname ...` afterwards
    // which breaks ldconfig, doing it here means it happens at link-time
    let name = "modality_probe";

    let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let os = env::var("CARGO_CFG_TARGET_OS").unwrap();
    let env = env::var("CARGO_CFG_TARGET_ENV").unwrap();

    let version_parts: Vec<&str> = PACKAGE_VERSION.trim().split('.').collect();
    assert_eq!(version_parts.len(), 3);
    let major = version_parts[0];
    let minor = version_parts[1];
    let micro = version_parts[2];

    let prefix: PathBuf = env::var_os("CARGO_C_PREFIX")
        .unwrap_or_else(|| "/usr/local".into())
        .into();
    let libdir = env::var_os("CARGO_C_LIBDIR").map_or(prefix.join("lib"), |v| v.into());

    let target_dir = env::var_os("CARGO_TARGET_DIR").map_or(
        {
            let manifest_dir: PathBuf = env::var_os("CARGO_MANIFEST_DIR").unwrap().into();
            manifest_dir
                .join("target")
                .join(std::env::var("PROFILE").unwrap())
        },
        |v| v.into(),
    );

    let lines = cdylib_link_lines::shared_object_link_args(
        &name, &major, &minor, &micro, &arch, &os, &env, libdir, target_dir,
    );
    let link = "cargo:rustc-cdylib-link-arg=";

    for line in lines {
        println!("{}{}", link, line);
    }

    // Workaround for no_std libc windows linking
    // https://github.com/rust-lang/libc/issues/1203
    let target = env::var("TARGET").unwrap();
    let linkage = env::var("CARGO_CFG_TARGET_FEATURE").unwrap();

    if target.contains("msvc") {
        if linkage.contains("crt-static") {
            println!("cargo:rustc-link-lib=dylib=libcmt");
        } else {
            println!("cargo:rustc-link-lib=dylib=msvcrt");
        }
    }
}
