use std::sync::atomic::{AtomicBool, Ordering};

static ZH: AtomicBool = AtomicBool::new(false);

pub fn zh() -> bool {
    ZH.load(Ordering::Relaxed)
}

pub fn set_zh(on: bool) {
    ZH.store(on, Ordering::Relaxed);
}

pub fn detect() -> bool {
    sys_locale::get_locale().is_some_and(|l| l.to_ascii_lowercase().starts_with("zh"))
}

pub fn tr(en: &'static str, zh_text: &'static str) -> &'static str {
    if zh() { zh_text } else { en }
}

const STEPS_ZH: [&str; 7] = ["地址", "匿名集", "发送交易", "钱包扫描", "区块", "挖矿", "报告"];

pub fn step(i: usize) -> &'static str {
    if zh() { STEPS_ZH[i] } else { crate::pipeline::STEPS[i] }
}

pub fn cores(n: usize) -> String {
    match (zh(), n) {
        (true, 1) => "单核".into(),
        (true, n) => format!("{n} 核"),
        (false, 1) => "1 core".into(),
        (false, n) => format!("{n} cores"),
    }
}
