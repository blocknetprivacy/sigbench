use std::path::{Path, PathBuf};

fn main() {
    let here = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let root = ["../spend", "../../spend"]
        .iter()
        .map(|p| here.join(p))
        .find(|p| p.join("src/tx/capi.cpp").exists())
        .expect("the spend/ prover source must sit at the repo root")
        .canonicalize()
        .unwrap();
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let os = std::env::var("CARGO_CFG_TARGET_OS").unwrap();
    println!("cargo:rerun-if-changed={}", root.join("src").display());
    println!("cargo:rerun-if-changed={}", root.join("lib").display());

    let x = root.join("subprojects/xkcp");
    let mut xinc: Vec<PathBuf> = ["", "lib/common", "lib/high/Keccak", "lib/high/Keccak/FIPS202", "lib/low/common"]
        .iter()
        .map(|d| x.join(d))
        .collect();
    let mut xsrc: Vec<PathBuf> = vec![
        x.join("lib/high/Keccak/FIPS202/KeccakHash.c"),
        x.join("lib/high/Keccak/KeccakSponge.c"),
    ];
    let arch_flags: Vec<&str>;
    let aes_impl;
    match arch.as_str() {
        "x86_64" => {
            let keccak_asm = os != "windows";
            for d in [
                if keccak_asm { "lib/low/KeccakP-1600/AVX2" } else { "lib/low/KeccakP-1600/plain-64bits" },
                "lib/low/KeccakP-1600/common",
                "lib/low/KeccakP-1600-times2/SIMD128",
                "lib/low/KeccakP-1600-times2/SIMD128/SSSE3-u2",
                "lib/low/KeccakP-1600-times4/AVX2",
                "lib/low/KeccakP-1600-times4/AVX2/u12",
                "lib/low/KeccakP-1600-times8/fallback-on4",
            ] {
                xinc.push(x.join(d));
            }
            if keccak_asm {
                xsrc.push(x.join("lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.s"));
            } else {
                xinc.push(x.join("lib/low/KeccakP-1600/plain-64bits/u6"));
                xsrc.push(x.join("lib/low/KeccakP-1600/plain-64bits/KeccakP-1600-opt64.c"));
                println!("cargo:rustc-link-lib=bcrypt");
            }
            xsrc.push(x.join("lib/low/KeccakP-1600-times2/SIMD128/KeccakP-1600-times2-SIMD128.c"));
            xsrc.push(x.join("lib/low/KeccakP-1600-times4/AVX2/KeccakP-1600-times4-SIMD256.c"));
            let zig = cc::Build::new().get_compiler().path().to_string_lossy().contains("zig");
            let level = if zig { "-mcpu=x86_64_v3" } else { "-march=x86-64-v3" };
            arch_flags = vec![level, "-maes", "-mpclmul"];
            aes_impl = root.join("src/avx2/aes_impl.cpp");
        }
        "aarch64" => {
            for d in [
                "lib/low/KeccakP-1600/common",
                "lib/low/KeccakP-1600-times4/fallback-on1",
                "lib/low/KeccakP-1600/plain-64bits",
                "lib/low/KeccakP-1600/plain-64bits/u6",
            ] {
                xinc.push(x.join(d));
            }
            xsrc.push(x.join("lib/low/KeccakP-1600-times4/fallback-on1/KeccakP-1600-times4-on1.c"));
            xsrc.push(x.join("lib/low/KeccakP-1600/plain-64bits/KeccakP-1600-opt64.c"));
            arch_flags = if os == "macos" { vec!["-mcpu=apple-m1"] } else { vec!["-march=armv8.2-a+crypto"] };
            aes_impl = root.join("src/aarch64/aes_impl.cpp");
        }
        other => panic!("the spend proof needs x86_64 (AVX2, AES, VPCLMULQDQ) or aarch64; got {other}"),
    }

    let inc = |b: &mut cc::Build| {
        for d in &xinc {
            b.include(d);
        }
        b.include(&root).include(root.join("src")).include(root.join("lib")).include(root.join("lib/sha3"));
        for f in &arch_flags {
            b.flag(f);
        }
        b.opt_level(3).warnings(false);
    };

    let mut c = cc::Build::new();
    inc(&mut c);
    c.flag("-std=c2x");
    for s in &xsrc {
        c.file(s);
    }
    for s in ["src/randomness.c", "lib/drng.c", "lib/sha3/KeccakHashtimes4.c", "lib/sha3/KeccakSpongetimes4.c"] {
        c.file(root.join(s));
    }
    c.compile("fastpq_c");

    let mut cpp = cc::Build::new();
    inc(&mut cpp);
    cpp.cpp(true)
        .flag("-std=c++23")
        .flag("-Wno-psabi")
        .flag("-U_GLIBCXX_ASSERTIONS")
        .define("SDSIGN_XOF_SHAKE", None)
        .define("SDSIGN_RING_TRANSCRIPT_PRECOMPUTE", "1");
    cpp.file(aes_impl);
    for s in [
        "src/polynomials_constants.cpp",
        "src/small_vole.cpp",
        "src/vector_com.cpp",
        "src/vole_commit.cpp",
        "src/tx/tx.cpp",
        "src/tx/capi.cpp",
    ] {
        cpp.file(root.join(s));
    }
    cpp.compile("fastpq_tx");
    let _ = Path::new("");
}
