use std::time::Duration;

fn zero() -> Duration {
    Duration::ZERO
}

#[test]
fn every_shape_proves_and_verifies() {
    let prep = vole::prepare();
    vole::self_check(&prep).expect("gate");
    for &n in &vole::SHAPES {
        let m = vole::run_one(&prep, n, 5, zero);
        assert_eq!(m.proof_bytes, vole::proof_bytes(n));
        println!(
            "{n} in / {n} out: {} B, prove {:.1} ms, verify {:.1} ms",
            m.proof_bytes,
            m.prove_wall.as_secs_f64() * 1e3,
            m.verify_wall.as_secs_f64() * 1e3
        );
    }
}
