use std::env;
use std::path::PathBuf;

fn main() {
    // NOTE: use the desired shared object name here, not the crate name,
    // we do this so we don't have to run `patchelf --set-soname ...` afterwards
    // which breaks ldconfig, doing it here means it happens at link-time
    let name = "ekotrace";

    let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let os = env::var("CARGO_CFG_TARGET_OS").unwrap();
    let env = env::var("CARGO_CFG_TARGET_ENV").unwrap();

    let major = env::var("CARGO_PKG_VERSION_MAJOR").unwrap();
    let minor = env::var("CARGO_PKG_VERSION_MINOR").unwrap();
    let micro = env::var("CARGO_PKG_VERSION_PATCH").unwrap();

    let prefix: PathBuf = env::var_os("CARGO_C_PREFIX")
        .unwrap_or("/usr/local".into())
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
}
