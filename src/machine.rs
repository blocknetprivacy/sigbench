#![allow(dead_code)]

use std::process::{Command, Stdio};

pub struct Machine {
    pub cpu: String,
    pub physical: Option<usize>,
    pub threads: usize,
    pub split: Option<(usize, usize)>,
    pub max_ghz: Option<f64>,
    pub cache: Option<String>,
    pub ram_gb: Option<f64>,
    pub os: String,
    pub arch: &'static str,
    pub simd_cpu: Vec<&'static str>,
    pub simd_build: Vec<&'static str>,
}

pub fn cmd(prog: &str, args: &[&str]) -> Option<String> {
    let o = Command::new(prog).args(args).stderr(Stdio::null()).output().ok()?;
    let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
    (!s.is_empty()).then_some(s)
}

pub fn sysctl(key: &str) -> Option<String> {
    cmd("sysctl", &["-n", key])
}

pub fn read(path: &str) -> Option<String> {
    std::fs::read_to_string(path).ok().map(|s| s.trim().to_string()).filter(|s| !s.is_empty())
}

#[allow(unused_mut, unused_macros)]
pub fn simd() -> (Vec<&'static str>, Vec<&'static str>) {
    let (mut cpu, mut build) = (Vec::new(), Vec::new());
    #[cfg(target_arch = "x86_64")]
    {
        macro_rules! f { ($($name:tt),*) => { $(
            if std::arch::is_x86_feature_detected!($name) { cpu.push($name); }
            if cfg!(target_feature = $name) { build.push($name); }
        )* } }
        f!("sse4.2", "avx", "avx2", "fma", "bmi2", "adx", "aes", "sha", "vaes", "vpclmulqdq",
           "avx512f", "avx512vl", "avx512bw", "avx512dq", "avx512ifma", "avx512vbmi");
    }
    #[cfg(target_arch = "aarch64")]
    {
        macro_rules! f { ($($name:tt),*) => { $(
            if std::arch::is_aarch64_feature_detected!($name) { cpu.push($name); }
            if cfg!(target_feature = $name) { build.push($name); }
        )* } }
        f!("neon", "aes", "sha2", "sha3", "crc", "dotprod", "sve", "sve2");
    }
    (cpu, build)
}

fn sysfs_size(s: String) -> Option<u64> {
    let s = s.trim();
    let (n, mult) = match s.chars().last()? {
        'K' => (&s[..s.len() - 1], 1024),
        'M' => (&s[..s.len() - 1], 1 << 20),
        _ => (s, 1),
    };
    n.parse::<u64>().ok().map(|v| v * mult)
}

pub fn bytes_size(b: u64) -> String {
    if b >= 1 << 20 {
        let m = b as f64 / (1u64 << 20) as f64;
        if m.fract() == 0.0 { format!("{m:.0} MiB") } else { format!("{m:.2} MiB") }
    } else {
        format!("{} KiB", b >> 10)
    }
}

pub fn machine() -> Machine {
    let cpuinfo = read("/proc/cpuinfo").unwrap_or_default();
    let cpu = sysctl("machdep.cpu.brand_string")
        .or_else(|| cpuinfo.lines().find(|l| l.starts_with("model name")).and_then(|l| l.split(':').nth(1)).map(|s| s.trim().to_string()))
        .or_else(|| std::env::var("PROCESSOR_IDENTIFIER").ok())
        .unwrap_or_else(|| "unknown".into());
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let physical = sysctl("hw.physicalcpu").and_then(|s| s.parse().ok()).or_else(|| {
        let (mut pkg, mut set) = (String::new(), std::collections::HashSet::new());
        for l in cpuinfo.lines() {
            if let Some(v) = l.strip_prefix("physical id") {
                pkg = v.trim_start_matches([' ', '\t', ':']).to_string();
            }
            if let Some(v) = l.strip_prefix("core id") {
                set.insert((pkg.clone(), v.trim_start_matches([' ', '\t', ':']).to_string()));
            }
        }
        (!set.is_empty()).then_some(set.len())
    });
    let split = match (sysctl("hw.perflevel0.physicalcpu"), sysctl("hw.perflevel1.physicalcpu")) {
        (Some(p), Some(e)) => p.parse().ok().zip(e.parse().ok()),
        _ => None,
    };
    let max_ghz = read("/sys/devices/system/cpu/cpu0/cpufreq/cpuinfo_max_freq")
        .and_then(|k| k.parse::<f64>().ok())
        .map(|k| k / 1e6)
        .or_else(|| sysctl("hw.cpufrequency_max").and_then(|h| h.parse::<f64>().ok()).map(|h| h / 1e9));
    let l2 = sysctl("hw.perflevel0.l2cachesize").or_else(|| sysctl("hw.l2cachesize")).and_then(|b| b.parse::<u64>().ok()).map(bytes_size)
        .or_else(|| read("/sys/devices/system/cpu/cpu0/cache/index2/size").and_then(sysfs_size).map(bytes_size));
    let l3 = sysctl("hw.l3cachesize").and_then(|b| b.parse::<u64>().ok()).filter(|b| *b > 0).map(bytes_size)
        .or_else(|| read("/sys/devices/system/cpu/cpu0/cache/index3/size").and_then(sysfs_size).map(bytes_size));
    let cache = match (l2, l3) {
        (Some(a), Some(b)) => Some(format!("L2 {a} · L3 {b}")),
        (Some(a), None) => Some(format!("L2 {a}")),
        (None, Some(b)) => Some(format!("L3 {b}")),
        _ => None,
    };
    let ram_gb = sysctl("hw.memsize")
        .and_then(|s| s.parse::<u64>().ok())
        .or_else(|| {
            read("/proc/meminfo")
                .and_then(|s| s.lines().find(|l| l.starts_with("MemTotal:")).and_then(|l| l.split_whitespace().nth(1)?.parse::<u64>().ok()))
                .map(|k| k * 1024)
        })
        .or_else(|| {
            cmd("powershell", &["-NoProfile", "-Command", "(Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory"]).and_then(|s| s.parse().ok())
        })
        .map(|b| b as f64 / (1u64 << 30) as f64);
    let os = sysctl("kern.osproductversion")
        .or_else(|| cmd("sw_vers", &["-productVersion"]))
        .map(|v| format!("macOS {v}"))
        .or_else(|| {
            let rel = read("/etc/os-release")?;
            rel.lines().find(|l| l.starts_with("PRETTY_NAME=")).map(|l| l[12..].trim_matches('"').to_string())
        })
        .or_else(|| cmd("cmd", &["/c", "ver"]))
        .unwrap_or_else(|| std::env::consts::OS.to_string());
    let kernel = cmd("uname", &["-r"]).filter(|_| cfg!(target_os = "linux"));
    let os = match kernel {
        Some(k) => format!("{os} (kernel {k})"),
        None => os,
    };
    let (simd_cpu, simd_build) = simd();
    Machine { cpu, physical, threads, split, max_ghz, cache, ram_gb, os, arch: std::env::consts::ARCH, simd_cpu, simd_build }
}

impl Machine {
    pub fn ram(&self) -> String {
        self.ram_gb.map(|g| format!("{g:.0} GB")).unwrap_or_else(|| "unknown".into())
    }
    pub fn cores(&self) -> String {
        let mut s = match self.physical {
            Some(p) => format!("{p} cores, {} threads", self.threads),
            None => format!("{} threads", self.threads),
        };
        if let Some((p, e)) = self.split {
            s.push_str(&format!(" ({p} performance + {e} efficiency)"));
        }
        s
    }
    pub fn has(&self, f: &str) -> bool {
        self.simd_cpu.contains(&f)
    }
    pub fn simd_rows(&self) -> Vec<(&'static str, String)> {
        let yes = |b: bool| if b { "yes" } else { "no" }.to_string();
        let upper = |v: &[&str]| v.iter().map(|f| f.to_uppercase()).collect::<Vec<_>>().join(" ");
        let mut rows = Vec::new();
        if self.arch == "x86_64" {
            rows.push(("AVX2", yes(self.has("avx2"))));
            let sub: Vec<&str> = self.simd_cpu.iter().filter_map(|f| f.strip_prefix("avx512")).collect();
            rows.push(("AVX-512", if sub.is_empty() { "no".into() } else { format!("yes ({})", upper(&sub)) }));
            let other: Vec<&str> = self.simd_cpu.iter().copied().filter(|f| !f.starts_with("avx")).collect();
            rows.push(("other", upper(&other)));
        } else if self.arch == "aarch64" {
            rows.push(("NEON", yes(self.has("neon"))));
            rows.push(("SVE", if self.has("sve2") { "yes (SVE2)".into() } else { yes(self.has("sve")) }));
            let other: Vec<&str> = self.simd_cpu.iter().copied().filter(|f| *f != "neon" && !f.starts_with("sve")).collect();
            rows.push(("other", upper(&other)));
        }
        let built: Vec<&str> = self.simd_build.iter().copied().filter(|f| *f != "neon").collect();
        let base = if self.arch == "aarch64" { "NEON" } else { "baseline SSE2" };
        rows.push(("this build uses", if built.is_empty() { base.into() } else { format!("{base} + {}", upper(&built)) }));
        rows
    }
    pub fn simd_short(&self) -> String {
        if self.arch == "x86_64" {
            let mut v = vec![];
            if self.has("avx2") {
                v.push("AVX2");
            }
            if self.has("avx512f") {
                v.push("AVX-512");
            }
            if v.is_empty() { "no AVX2".into() } else { v.join(" · ") }
        } else if self.has("sve") {
            "NEON · SVE".into()
        } else {
            "NEON".into()
        }
    }
}

pub fn machine_sections(m: &Machine) -> Vec<(&'static str, Vec<(&'static str, String)>)> {
    vec![
        (
            "Machine",
            vec![
                ("cpu", m.cpu.clone()),
                ("cores", m.cores()),
                ("max clock", m.max_ghz.map(|g| format!("{g:.2} GHz")).unwrap_or_else(|| "not reported".into())),
                ("cache", m.cache.clone().unwrap_or_else(|| "not reported".into())),
                ("memory", m.ram()),
                ("os", m.os.clone()),
                ("arch", m.arch.to_string()),
            ],
        ),
        ("Vector units", m.simd_rows()),
    ]
}
