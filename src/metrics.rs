use std::time::Duration;

#[cfg(unix)]
pub fn process_cpu_time() -> Duration {
    use std::mem::MaybeUninit;
    let mut usage = MaybeUninit::<libc::rusage>::uninit();
    let rc = unsafe { libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()) };
    if rc != 0 {
        return Duration::ZERO;
    }
    let u = unsafe { usage.assume_init() };
    let micros = |t: libc::timeval| (t.tv_sec as i64 as u64) * 1_000_000 + (t.tv_usec as i64 as u64);
    Duration::from_micros(micros(u.ru_utime) + micros(u.ru_stime))
}

#[cfg(windows)]
pub fn process_cpu_time() -> Duration {
    use windows_sys::Win32::Foundation::FILETIME;
    use windows_sys::Win32::System::Threading::{GetCurrentProcess, GetProcessTimes};
    let mut creation = FILETIME { dwLowDateTime: 0, dwHighDateTime: 0 };
    let mut exit = creation;
    let mut kernel = creation;
    let mut user = creation;
    let ok = unsafe {
        GetProcessTimes(
            GetCurrentProcess(),
            &mut creation,
            &mut exit,
            &mut kernel,
            &mut user,
        )
    };
    if ok == 0 {
        return Duration::ZERO;
    }
    let to_ns = |f: FILETIME| (((f.dwHighDateTime as u64) << 32) | f.dwLowDateTime as u64) * 100;
    Duration::from_nanos(to_ns(kernel) + to_ns(user))
}

#[cfg(not(any(unix, windows)))]
pub fn process_cpu_time() -> Duration {
    Duration::ZERO
}

#[cfg(target_os = "linux")]
pub fn process_rss_bytes() -> u64 {
    if let Ok(s) = std::fs::read_to_string("/proc/self/statm") {
        let mut it = s.split_whitespace();
        let _total = it.next();
        if let Some(resident) = it.next() {
            if let Ok(pages) = resident.parse::<u64>() {
                let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as u64;
                return pages * page;
            }
        }
    }
    0
}

#[cfg(target_os = "macos")]
pub fn process_rss_bytes() -> u64 {
    use std::mem::{size_of, MaybeUninit};
    let mut info = MaybeUninit::<libc::proc_taskinfo>::uninit();
    let size = size_of::<libc::proc_taskinfo>() as libc::c_int;
    let pid = unsafe { libc::getpid() };
    let n = unsafe {
        libc::proc_pidinfo(
            pid,
            libc::PROC_PIDTASKINFO,
            0,
            info.as_mut_ptr() as *mut libc::c_void,
            size,
        )
    };
    if n == size {
        unsafe { info.assume_init() }.pti_resident_size
    } else {
        0
    }
}

#[cfg(windows)]
pub fn process_rss_bytes() -> u64 {
    use std::mem::{size_of, zeroed};
    use windows_sys::Win32::System::ProcessStatus::{
        GetProcessMemoryInfo, PROCESS_MEMORY_COUNTERS,
    };
    use windows_sys::Win32::System::Threading::GetCurrentProcess;
    let mut pmc: PROCESS_MEMORY_COUNTERS = unsafe { zeroed() };
    let ok = unsafe {
        GetProcessMemoryInfo(
            GetCurrentProcess(),
            &mut pmc,
            size_of::<PROCESS_MEMORY_COUNTERS>() as u32,
        )
    };
    if ok == 0 {
        0
    } else {
        pmc.WorkingSetSize as u64
    }
}

#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
pub fn process_rss_bytes() -> u64 {
    0
}

#[derive(Clone, Copy)]
pub struct Stats {
    pub low: f64,
    pub high: f64,
    pub avg: f64,
    #[allow(dead_code)]
    pub median: f64,
    #[allow(dead_code)]
    pub n: usize,
}

impl Stats {
    pub fn of(vals: &[f64]) -> Stats {
        if vals.is_empty() {
            return Stats { low: 0.0, high: 0.0, avg: 0.0, median: 0.0, n: 0 };
        }
        let mut v = vals.to_vec();
        v.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
        let n = v.len();
        let sum: f64 = v.iter().sum();
        let median = if n % 2 == 1 {
            v[n / 2]
        } else {
            (v[n / 2 - 1] + v[n / 2]) / 2.0
        };
        Stats {
            low: v[0],
            high: v[n - 1],
            avg: sum / n as f64,
            median,
            n,
        }
    }
}

pub fn cpu_pct(cpu: Duration, wall: Duration) -> f64 {
    let w = wall.as_secs_f64();
    if w <= 0.0 {
        0.0
    } else {
        cpu.as_secs_f64() / w * 100.0
    }
}
