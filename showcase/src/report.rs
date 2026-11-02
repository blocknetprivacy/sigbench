use std::fmt::Write as _;

use crate::pipeline::{self, Live, ReportRes};
use crate::pow;

fn utc_now() -> (String, String) {
    let secs = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs()) as i64;
    let days = secs.div_euclid(86_400);
    let rem = secs.rem_euclid(86_400);
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + if m <= 2 { 1 } else { 0 };
    (format!("{y:04}-{m:02}-{d:02}"), format!("{:02}:{:02}:{:02}", rem / 3600, rem % 3600 / 60, rem % 60))
}

fn run(cmd: &str, args: &[&str]) -> Option<String> {
    let o = std::process::Command::new(cmd).args(args).output().ok()?;
    let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
    (!s.is_empty()).then_some(s)
}

fn file_line(path: &str, key: &str) -> Option<String> {
    std::fs::read_to_string(path).ok()?.lines().find(|l| l.starts_with(key)).and_then(|l| l.split_once([':', '='])).map(|(_, v)| v.trim().trim_matches('"').to_string())
}

fn cpu_name() -> String {
    run("sysctl", &["-n", "machdep.cpu.brand_string"]).or_else(|| file_line("/proc/cpuinfo", "model name")).unwrap_or_else(|| "unknown".into())
}

fn physical_cores() -> Option<String> {
    run("sysctl", &["-n", "hw.physicalcpu"])
}

fn ram_bytes() -> Option<u64> {
    run("sysctl", &["-n", "hw.memsize"])
        .and_then(|s| s.parse().ok())
        .or_else(|| file_line("/proc/meminfo", "MemTotal").and_then(|v| v.trim_end_matches("kB").trim().parse::<u64>().ok()).map(|k| k * 1024))
}

fn os_version() -> String {
    if cfg!(target_os = "macos") {
        format!("macOS {}", run("sw_vers", &["-productVersion"]).unwrap_or_default())
    } else {
        file_line("/etc/os-release", "PRETTY_NAME").unwrap_or_else(|| std::env::consts::OS.into())
    }
}

fn kernel() -> String {
    run("uname", &["-r"]).unwrap_or_default()
}

fn power() -> &'static str {
    if let Some(s) = run("pmset", &["-g", "batt"]) {
        return if s.contains("AC Power") { "ac" } else if s.contains("Battery Power") { "battery" } else { "unknown" };
    }
    match std::fs::read_to_string("/sys/class/power_supply/AC/online").map(|s| s.trim().to_string()).as_deref() {
        Ok("1") => "ac",
        Ok("0") => "battery",
        _ => "unknown",
    }
}

fn cpu_features() -> Vec<&'static str> {
    let mut v = Vec::new();
    #[cfg(target_arch = "aarch64")]
    {
        if std::arch::is_aarch64_feature_detected!("aes") {
            v.push("aes");
        }
        if std::arch::is_aarch64_feature_detected!("sha3") {
            v.push("sha3");
        }
        if std::arch::is_aarch64_feature_detected!("neon") {
            v.push("neon");
        }
    }
    #[cfg(target_arch = "x86_64")]
    {
        if std::arch::is_x86_feature_detected!("aes") {
            v.push("aes");
        }
        if std::arch::is_x86_feature_detected!("pclmulqdq") {
            v.push("pclmulqdq");
        }
        if std::arch::is_x86_feature_detected!("avx2") {
            v.push("avx2");
        }
        if std::arch::is_x86_feature_detected!("vaes") {
            v.push("vaes");
        }
        if std::arch::is_x86_feature_detected!("avx512f") {
            v.push("avx512f");
        }
    }
    v
}

fn peak_rss() -> Option<u64> {
    #[cfg(unix)]
    {
        let mut u: libc::rusage = unsafe { std::mem::zeroed() };
        if unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut u) } == 0 {
            let v = u.ru_maxrss as u64;
            return Some(if cfg!(target_os = "macos") { v } else { v * 1024 });
        }
    }
    None
}

fn spread(v: &[f64]) -> (f64, f64, f64, f64) {
    if v.is_empty() {
        return (0.0, 0.0, 0.0, 0.0);
    }
    let mut s = v.to_vec();
    s.sort_by(|a, b| a.total_cmp(b));
    let at = |p: f64| s[((p * s.len() as f64).ceil() as usize).clamp(1, s.len()) - 1];
    (s[0], at(0.5), at(0.95), s[s.len() - 1])
}

pub fn text(g: &Live) -> String {
    let mut t = String::new();
    let (date, time) = utc_now();
    let q = |s: &str| format!("\"{}\"", s.replace('"', "'"));
    let _ = writeln!(t, "[bench]");
    let _ = writeln!(t, "name = \"blocknet-bench3\"");
    let _ = writeln!(t, "version = {}", q(env!("CARGO_PKG_VERSION")));
    let _ = writeln!(t, "build = {}", q(if cfg!(debug_assertions) { "debug" } else { "release" }));
    let _ = writeln!(t, "time_utc = \"{date}T{time}Z\"");
    let _ = writeln!(t, "share = \"https://{}\"", crate::SHARE_URL);
    let _ = writeln!(t);
    let _ = writeln!(t, "[machine]");
    let _ = writeln!(t, "cpu = {}", q(&cpu_name()));
    let _ = writeln!(t, "arch = {}", q(std::env::consts::ARCH));
    let _ = writeln!(t, "logical_cores = {}", std::thread::available_parallelism().map_or(1, |n| n.get()));
    if let Some(p) = physical_cores() {
        let _ = writeln!(t, "physical_cores = {p}");
    }
    if let Some(r) = ram_bytes() {
        let _ = writeln!(t, "ram_bytes = {r}");
        let _ = writeln!(t, "ram_gb = {:.1}", r as f64 / 1_073_741_824.0);
    }
    let _ = writeln!(t, "os = {}", q(&os_version()));
    let _ = writeln!(t, "kernel = {}", q(&kernel()));
    let _ = writeln!(t, "gpu = {}", q(g.gpu.as_deref().unwrap_or("none")));
    let _ = writeln!(t, "power = {}", q(power()));
    let _ = writeln!(t, "cpu_features = [{}]", cpu_features().iter().map(|f| q(f)).collect::<Vec<_>>().join(", "));
    let _ = writeln!(t);
    if let Some(s) = &g.set {
        let _ = writeln!(t, "[set]");
        let _ = writeln!(t, "outputs = {}", pipeline::NSET);
        let _ = writeln!(t, "sender_coins = {}", pipeline::POOL);
        let _ = writeln!(t, "build_ms = {:.1}", s.ms);
        let _ = writeln!(t);
    }
    for (i, st) in g.stats.iter().enumerate() {
        let n = pipeline::SHAPES[i];
        let (pmin, pmed, p95, pmax) = spread(&st.prove);
        let (vmin, vmed, v95, vmax) = spread(&st.verify);
        let _ = writeln!(t, "[send.{n}x{n}]");
        let _ = writeln!(t, "runs = {}", st.runs);
        let _ = writeln!(t, "proof_bytes = {}", st.proof_bytes);
        let _ = writeln!(t, "create_ms = {{ min = {pmin:.2}, median = {pmed:.2}, p95 = {p95:.2}, max = {pmax:.2} }}");
        let _ = writeln!(t, "check_ms = {{ min = {vmin:.2}, median = {vmed:.2}, p95 = {v95:.2}, max = {vmax:.2} }}");
        let _ = writeln!(t);
    }
    if let Some(s) = &g.scan {
        let _ = writeln!(t, "[scan]");
        let _ = writeln!(t, "outputs = {}", s.marks.len());
        let _ = writeln!(t, "ms = {:.2}", s.ms);
        let _ = writeln!(t, "outputs_per_s = {:.0}", s.rate());
        let _ = writeln!(t, "found = {}", s.mine);
        let _ = writeln!(t, "expected = {}", s.expected);
        let _ = writeln!(t, "false_tag_hits = {}", s.tag_only);
        let _ = writeln!(t);
    }
    if let Some(b) = &g.block {
        let _ = writeln!(t, "[block]");
        let _ = writeln!(t, "tx = {}", b.txs.len());
        let _ = writeln!(t, "bytes = {}", b.bytes);
        let _ = writeln!(t, "check_ms = {:.1}", b.check_ms.unwrap_or(0.0));
        let _ = writeln!(t, "pruned_bytes = {}", b.pruned);
        let _ = writeln!(t);
    }
    for r in &g.mine {
        let key = match r.place {
            "GPU" => "gpu",
            "one core" => "cpu_1",
            _ => "cpu_all",
        };
        let _ = writeln!(t, "[mining.{key}]");
        let _ = writeln!(t, "threads = {}", r.threads);
        let _ = writeln!(t, "hashes = {}", r.hashes);
        let _ = writeln!(t, "seconds = {:.3}", r.secs);
        let _ = writeln!(t, "hashes_per_s = {:.0}", r.rate());
        let _ = writeln!(t, "best_zero_bits = {}", pow::zero_bits(&r.best));
        let _ = writeln!(t);
    }
    let _ = writeln!(t, "[checks]");
    let _ = writeln!(t, "scan = {}", g.scan.as_ref().is_some_and(|s| s.ok));
    let _ = writeln!(t, "block = {}", g.block.as_ref().is_some_and(|b| b.ok));
    let _ = writeln!(t, "gpu_matches_cpu = {}", g.mine.iter().all(|r| r.ok));
    if let Some(m) = peak_rss() {
        let _ = writeln!(t, "peak_rss_bytes = {m}");
    }
    t
}

pub fn write(g: &Live) -> ReportRes {
    let text = text(g);
    let (date, time) = utc_now();
    let dir = std::env::current_dir().unwrap_or_default().join("reports");
    let path = dir.join(format!("blocknet-bench3-{date}-{}.toml", time.replace(':', "")));
    let saved = std::fs::create_dir_all(&dir).and_then(|_| std::fs::write(&path, &text));
    ReportRes { path: if saved.is_ok() { path.display().to_string() } else { String::new() } }
}
