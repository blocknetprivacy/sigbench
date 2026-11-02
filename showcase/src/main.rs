#![cfg_attr(windows, windows_subsystem = "windows")]

#[path = "../../src/address.rs"]
#[allow(dead_code)]
mod address;
mod mine;
mod pipeline;
mod report;
mod text;
#[path = "../../src/pow.rs"]
#[allow(dead_code)]
mod pow;

use std::sync::{Arc, MutexGuard};
use std::time::Instant;

use bytemuck::{Pod, Zeroable};
use pipeline::{AddrRes, Live, Shared, ETA, FIELD_H, FIELD_W, LIVE_STEPS, NSET, SEND_RUNS, SHAPES};
use text::{tr, zh};
use vole::wire::Scan;
use winit::application::ApplicationHandler;
use winit::dpi::LogicalSize;
use winit::event::{ElementState, KeyEvent, WindowEvent};
use winit::event_loop::{ActiveEventLoop, ControlFlow, EventLoop};
use winit::keyboard::{Key, NamedKey};
use winit::window::{Fullscreen, Window, WindowId};

const MAX_RECTS: usize = 60_000;
const MAX_GLYPHS: usize = 4096;
const DATA_TEX: u32 = 1024;

const HOLD: [f32; LIVE_STEPS] = [14.0, 15.0, 8.0, 12.0, 26.0, 10.0, f32::INFINITY];

const PACE: f32 = 0.7;

const LABEL: f32 = 13.0;

const BODY: f32 = 18.0;

const BOARD: f32 = 15.0;

const OPEN_REPORT_AFTER: f32 = 4.0;

pub const SHARE_URL: &str = "uproar.chat/invite/blocknet";

type C = [f32; 4];

fn lin(h: u32, a: f32) -> C {
    let f = |v: u32| (v as f32 / 255.0).powf(2.2);
    [f((h >> 16) & 255), f((h >> 8) & 255), f(h & 255), a]
}

fn white(a: f32) -> C {
    lin(0xe9e5dc, a)
}
fn gray(a: f32) -> C {
    lin(0x6e6a63, a)
}
fn dark(a: f32) -> C {
    lin(0x2a2826, a)
}
fn lime(a: f32) -> C {
    lin(0xaaff00, a)
}

fn ease(x: f32) -> f32 {
    let t = x.clamp(0.0, 1.0);
    t * t * (3.0 - 2.0 * t)
}
fn ph(t: f32, a: f32, b: f32) -> f32 {
    ((t - a) / (b - a)).clamp(0.0, 1.0)
}

#[repr(C)]
#[derive(Clone, Copy, Pod, Zeroable)]
struct Rect {
    pos: [f32; 2],
    size: [f32; 2],
    col: C,
}

#[repr(C)]
#[derive(Clone, Copy, Pod, Zeroable)]
struct Glyph {
    pos: [f32; 2],
    size: [f32; 2],
    uv: [f32; 4],
    col: C,
}

#[derive(Clone, Copy)]
struct GInfo {
    uv: [f32; 4],
    size: [f32; 2],
    off: [f32; 2],
    adv: f32,
}

static GLYPHS: std::sync::OnceLock<std::collections::HashMap<char, GInfo>> = std::sync::OnceLock::new();

mod cjk {
    include!(concat!(env!("OUT_DIR"), "/cjk.rs"));
}

#[repr(C)]
#[derive(Clone, Copy, Pod, Zeroable)]
struct DataQuad {
    rect: [f32; 4],
    uvr: [f32; 4],
    prm: [f32; 4],
    dim: [f32; 4],
}

#[repr(C)]
#[derive(Clone, Copy, Pod, Zeroable)]
struct U {
    res: [f32; 4],
    atlas: [f32; 4],
    img: [f32; 4],
    uvr: [f32; 4],
    logo: [f32; 4],
    tint: [f32; 4],
}

struct Frame {
    rects: Vec<Rect>,
    glyphs: Vec<Glyph>,
    adv: f32,
    line: f32,
    image: Option<([f32; 4], [f32; 4], f32)>,
    quads: Vec<DataQuad>,
    logo: Option<[f32; 3]>,
    hot: Vec<([f32; 4], Hot)>,
}

#[derive(Clone, Copy, PartialEq)]
enum Hot {
    Share,
    Lang(bool),
    Start,
}

impl Frame {
    fn rect(&mut self, x: f32, y: f32, w: f32, h: f32, col: C) {
        if self.rects.len() < MAX_RECTS && col[3] > 0.0 {
            self.rects.push(Rect { pos: [x, y], size: [w, h], col });
        }
    }
    fn text(&mut self, x: f32, y: f32, size: f32, s: &str, col: C) {
        let map = GLYPHS.get().expect("glyph atlas");
        let mut cx = x;
        for c in s.chars() {
            match map.get(&c) {
                Some(g) => {
                    if self.glyphs.len() < MAX_GLYPHS {
                        self.glyphs.push(Glyph { pos: [cx + g.off[0] * size, y + g.off[1] * size], size: [g.size[0] * size, g.size[1] * size], uv: g.uv, col });
                    }
                    cx += g.adv * size;
                }
                None => cx += self.adv * size,
            }
        }
    }
    fn width(&self, size: f32, s: &str) -> f32 {
        let map = GLYPHS.get().expect("glyph atlas");
        s.chars().map(|c| map.get(&c).map_or(self.adv, |g| g.adv)).sum::<f32>() * size
    }
}

const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800a, 0x800000008000000a, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];
const RHO: [u32; 25] = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14];

fn keccak_f(a: &mut [u64; 25], trace: &mut Vec<[u64; 25]>) {
    for rc in RC {
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        }
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                a[x + 5 * y] ^= d;
            }
        }
        let mut b = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                b[y + 5 * ((2 * x + 3 * y) % 5)] = a[x + 5 * y].rotate_left(RHO[x + 5 * y]);
            }
        }
        for y in 0..5 {
            for x in 0..5 {
                a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
            }
        }
        a[0] ^= rc;
        trace.push(*a);
    }
}

fn sha3_trace(msg: &[u8]) -> ([u8; 32], Vec<[u64; 25]>) {
    let mut m = msg.to_vec();
    m.push(0x06);
    while m.len() % 136 != 0 {
        m.push(0);
    }
    *m.last_mut().unwrap() |= 0x80;
    let mut a = [0u64; 25];
    let mut trace = Vec::new();
    for block in m.chunks(136) {
        for (i, lane) in block.chunks(8).enumerate() {
            a[i] ^= u64::from_le_bytes(lane.try_into().unwrap());
        }
        keccak_f(&mut a, &mut trace);
    }
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[i * 8..i * 8 + 8].copy_from_slice(&a[i].to_le_bytes());
    }
    (out, trace)
}

fn ball(rank: usize) -> [bool; ETA] {
    let mut v = [false; ETA];
    if rank == 0 {
        return v;
    }
    if rank <= ETA {
        v[rank - 1] = true;
        return v;
    }
    let mut k = ETA + 1;
    for i in 0..ETA {
        for j in i + 1..ETA {
            if k == rank {
                v[i] = true;
                v[j] = true;
                return v;
            }
            k += 1;
        }
    }
    v
}

struct Layout {
    w: f32,
    h: f32,
    s: f32,
    x0: f32,
    y0: f32,
    x1: f32,
    y1: f32,
}

fn layout(w: f32, h: f32, dpi: f32) -> Layout {
    let s = dpi * (h / dpi / 720.0).max(0.6);
    Layout { w, h, s, x0: w * 0.30, y0: h * 0.12, x1: w * 0.95, y1: h * 0.84 }
}

fn overlay(f: &mut Frame, l: &Layout, step: usize, results: &[Option<String>], fps: f32) {
    let size = (BOARD * l.s).round();
    let (x, mut y) = ((24.0 * l.s).round(), (24.0 * l.s).round());
    for i in 0..LIVE_STEPS {
        let name = text::step(i);
        let on = i == step;
        let result = results.get(i).and_then(|r| r.as_deref());
        let (num_c, name_c) = if on {
            (lime(1.0), white(1.0))
        } else if result.is_some() {
            (gray(1.0), white(0.85))
        } else {
            (dark(1.0), gray(0.7))
        };
        f.text(x, y, size, &format!("{}", i + 1), num_c);
        f.text(x + f.adv * size * 2.0, y, size, name, name_c);
        if let Some(r) = result {
            let ax = x + f.adv * size * 3.0 + f.width(size, name);
            f.text(ax, y, size, "->", gray(1.0));
            f.text(ax + f.adv * size * 3.0, y, size, r, lime(1.0));
        }
        y += size * f.line * 1.25;
    }
    let logo = (30.0 * l.s).round();
    let m = (24.0 * l.s).round();
    let word = (17.0 * l.s).round();
    let ww = f.width(word, "Blocknet");
    f.text(l.w - m - logo - word * 0.8 - ww, l.h - m - logo + (logo - word * f.line) * 0.5, word, "Blocknet", white(0.92));
    f.text(m, l.h - m - size * f.line, size * 0.85, &format!("{fps:.0} fps"), dark(1.0));
}

fn results(live: &Live, address_shown: bool) -> Vec<Option<String>> {
    let two = &live.stats[0];
    vec![
        live.addr.as_ref().filter(|_| address_shown).map(|a| format!("{}..{}", &a.wallet.address[..10], &a.wallet.address[a.wallet.address.len() - 8..])),
        live.set.as_ref().map(|s| if zh() { format!("{}，{:.1} 秒", group3(NSET as u64), s.ms / 1000.0) } else { format!("{} in {:.1} s", group3(NSET as u64), s.ms / 1000.0) }),
        live.done(pipeline::SEND).then(|| if zh() { format!("2/2 {:.0} KB {:.0} 毫秒", two.proof_bytes as f64 / 1024.0, two.prove_ms()) } else { format!("2/2 {:.0} KB {:.0} ms", two.proof_bytes as f64 / 1024.0, two.prove_ms()) }),
        live.scan.as_ref().map(|s| match (s.ok, zh()) {
            (true, true) => format!("{}/秒，找到 {}", group3(s.rate() as u64), group3(s.mine as u64)),
            (true, false) => format!("{}/s {} found", group3(s.rate() as u64), group3(s.mine as u64)),
            (false, _) => tr("MISMATCH", "结果不一致").into(),
        }),
        live.block.as_ref().filter(|b| b.check_ms.is_some()).map(|b| match (b.ok, zh()) {
            (true, true) => format!("每 2 MB {} 笔 2/2 交易", b.txs.len()),
            (true, false) => format!("{} tx of 2/2 per 2 MB", b.txs.len()),
            (false, _) => tr("REJECTED", "未通过验证").into(),
        }),
        mining_result(live),
        live.report.as_ref().map(|r| if r.path.is_empty() { tr("not saved", "未保存").into() } else { tr("saved to reports/", "已保存到 reports/").into() }),
    ]
}

fn mhs(r: f64) -> String {
    if r >= 1e6 { format!("{:.1} MH/s", r / 1e6) } else { format!("{:.0} kH/s", r / 1e3) }
}

fn mining_result(live: &Live) -> Option<String> {
    if !live.done(pipeline::MINING) {
        return None;
    }
    if live.mine.iter().any(|r| !r.ok) {
        return Some(tr("GPU MISMATCH", "GPU 结果不一致").into());
    }
    let rate = |place: &str| live.mine.iter().find(|r| r.place == place).map(|r| r.rate());
    Some(match (rate("GPU"), rate("all cores")) {
        (Some(g), Some(c)) => if zh() { format!("GPU {:.0} MH/s，CPU {:.0}", g / 1e6, c / 1e6) } else { format!("{:.0} MH/s GPU, {:.0} CPU", g / 1e6, c / 1e6) },
        (None, Some(c)) => format!("{} CPU", mhs(c)),
        _ => String::new(),
    })
}

const FIELDS: [(usize, &str, &str); 7] = [(0, "version", "版本"), (4, "height", "高度"), (12, "prev hash", "前一区块哈希"), (44, "merkle root", "默克尔根"), (76, "time", "时间"), (84, "difficulty", "难度"), (92, "nonce", "随机数")];

fn bits_row(f: &mut Frame, x: f32, y: f32, w: f32, h: f32, bytes: &[u8], a: f32, zeros_lime: bool) {
    let bw = w / (bytes.len() * 8) as f32;
    let lead = pow_zero_bits(bytes);
    for (i, &byte) in bytes.iter().enumerate() {
        for k in 0..8 {
            let n = i * 8 + k;
            let x0 = x + n as f32 * bw;
            if n < lead as usize && zeros_lime {
                f.rect(x0, y, (bw - 0.5).max(0.5), h, lime(a));
            } else if (byte >> (7 - k)) & 1 == 1 {
                f.rect(x0, y, (bw - 0.5).max(0.5), h, white(a));
            }
        }
    }
}

fn pow_zero_bits(b: &[u8]) -> u32 {
    let mut n = 0;
    for &x in b {
        if x == 0 {
            n += 8;
        } else {
            return n + x.leading_zeros();
        }
    }
    n
}

fn scene_mining(f: &mut Frame, l: &Layout, t: f32, live: &Live) {
    let a = ph(t, 0.0, 0.3);
    let cw = l.x1 - l.x0;
    let Some(input) = live.mine_input else { return };
    let cur = live.mine.last();
    let big = (54.0 * l.s).round();
    let mid = (BODY * l.s).round();
    let y0 = l.y0 - 10.0 * l.s;
    let hashes = cur.map_or(0, |r| r.hashes);
    let count = group3(hashes);
    f.text(l.x0, y0, big, &count, lime(a));
    let after = l.x0 + f.width(big, &count) + 18.0 * l.s;
    if let Some(r) = cur {
        f.text(after, y0 + big * f.line - mid * f.line * 2.1, mid, tr("BLAKE2b-512 hashes of this block's header", "次 BLAKE2b-512 哈希（本区块的区块头）"), white(a));
        let place = if r.place == "GPU" { live.gpu.clone().unwrap_or_default() } else { text::cores(r.threads) };
        let status = if zh() { format!("{}   {}   最佳：{} 个前导零位", place, mhs(r.rate()), pow_zero_bits(&r.best[..32])) } else { format!("{}   {}   best {} zero bits", place, mhs(r.rate()), pow_zero_bits(&r.best[..32])) };
        f.text(after, y0 + big * f.line - mid * f.line * 1.0, mid, &status, gray(a));
    }
    let bar_y = y0 + big * f.line + 10.0 * l.s;
    let n = live.mine_total.max(1);
    let seg = cw / n as f32;
    for i in 0..n {
        let fill = match live.mine.get(i) {
            Some(r) if r.done => 1.0,
            Some(r) => (r.secs / pipeline::MINE_SECS) as f32,
            None => 0.0,
        };
        f.rect(l.x0 + i as f32 * seg, bar_y, seg - 4.0 * l.s, 2.0 * l.s, dark(a));
        f.rect(l.x0 + i as f32 * seg, bar_y, (seg - 4.0 * l.s) * fill.min(1.0), 2.0 * l.s, lime(a));
    }

    let iy = bar_y + 44.0 * l.s;
    let persona = String::from_utf8_lossy(&pow::PERSONAL[..15]).to_string();
    let input_label = if zh() { format!("哈希输入   SerializeForPoW 92 字节 + 随机数 8 字节   个性化字符串 {persona}") } else { format!("hash input   SerializeForPoW 92 B + nonce 8 B   personalization {persona}") };
    label(f, l.x0, iy - 18.0 * l.s, l, &input_label, gray(a));
    let cell = cw / pow::INPUT_LEN as f32;
    let nonce = live.mine_nonce.to_le_bytes();
    for i in 0..pow::INPUT_LEN {
        let (byte, is_nonce) = if i < pow::PREFIX_LEN { (input[i], false) } else { (nonce[i - pow::PREFIX_LEN], true) };
        let lum = 0.2 + 0.8 * byte as f32 / 255.0;
        let col = if is_nonce { lime(a * lum) } else { white(a * lum * 0.8) };
        f.rect(l.x0 + i as f32 * cell, iy, cell - 1.0, 18.0 * l.s, col);
    }
    for (k, (off, en, zh_name)) in FIELDS.iter().enumerate() {
        let name = tr(en, zh_name);
        let x = l.x0 + *off as f32 * cell;
        let dy = if k % 2 == 1 { 14.0 * l.s } else { 0.0 };
        f.rect(x, iy + 20.0 * l.s, 1.0 * l.s, 6.0 * l.s + dy, gray(a));
        label(f, x + 4.0 * l.s, iy + 22.0 * l.s + dy, l, name, gray(a));
    }

    let ry = iy + 78.0 * l.s;
    let rw = cw * 0.6;
    let rh = 5.0 * l.s;
    if let Some(r) = cur {
        label(f, l.x0, ry - 16.0 * l.s, l, tr("best hash so far, first 256 bits", "目前最佳哈希（前 256 位）"), gray(a));
        bits_row(f, l.x0, ry, rw, rh * 2.0, &r.best[..32], a, true);
        label(f, l.x0, ry + rh * 2.0 + 10.0 * l.s, l, tr("latest hashes", "最新哈希"), gray(a));
    }
    let rows = (((l.y1 + 30.0 * l.s) - (ry + rh * 2.0 + 28.0 * l.s)) / rh).max(0.0) as usize;
    for (i, h) in live.rain.iter().take(rows).enumerate() {
        let k = 1.0 - i as f32 / rows.max(1) as f32;
        bits_row(f, l.x0, ry + rh * 2.0 + 28.0 * l.s + i as f32 * rh, rw, rh - 1.0, h, a * 0.6 * k, true);
    }

    let cx = l.x0 + rw + 40.0 * l.s;
    let chart_w = l.x1 - cx;
    let max_rate = live.mine.iter().map(|r| r.rate()).fold(1.0, f64::max);
    let mut y = ry - 16.0 * l.s;
    let name = (14.0 * l.s).round();
    f.text(cx, y, name, "BLAKE2b-512", white(a));
    label(f, cx, y + name * f.line, l, tr("the Faraday proof of work", "Faraday 工作量证明"), gray(a));
    y += name * f.line + 22.0 * l.s;
    for r in &live.mine {
        let w = chart_w * 0.62 * (r.rate() / max_rate) as f32;
        let place = if r.place == "GPU" { "GPU".to_string() } else { text::cores(r.threads) };
        label(f, cx, y, l, &place, gray(a));
        f.rect(cx + 64.0 * l.s, y + 2.0 * l.s, w.max(1.0), 9.0 * l.s, if r.done { lime(a) } else { col_dim(lime(a)) });
        label(f, cx + 64.0 * l.s + w + 8.0 * l.s, y, l, &mhs(r.rate()), lime(a));
        y += 20.0 * l.s;
    }
}

fn scene_report(f: &mut Frame, l: &Layout, t: f32, live: &Live, r: &pipeline::ReportRes) {
    let name = (BODY * l.s).round();
    let detail = (LABEL * l.s).round();
    let row_h = name * f.line + detail * f.line + 22.0 * l.s;
    let mut rows: Vec<(String, String, String)> = Vec::new();
    if let Some(a) = &live.addr {
        rows.push((text::step(0).into(), a.wallet.address.clone(), tr("58 characters, post-quantum", "58 个字符，抗量子").into()));
    }
    if let Some(s) = &live.set {
        let built = if zh() { format!("{} 个输出，用时 {:.1} 秒", group3(NSET as u64), s.ms / 1000.0) } else { format!("{} outputs built in {:.1} s", group3(NSET as u64), s.ms / 1000.0) };
        rows.push((text::step(1).into(), built, text::cores(1)));
    }
    let two = &live.stats[0];
    let (send_v, send_d) = if zh() {
        (format!("2 输入 / 2 输出：证明 {}，生成 {:.0} 毫秒，验证 {:.0} 毫秒", kb(two.proof_bytes), two.prove_ms(), two.verify_ms()), format!("共 {} 笔交易完成证明与验证，单核", live.sends))
    } else {
        (format!("2 in / 2 out: {} proof, {:.0} ms to create, {:.0} ms to check", kb(two.proof_bytes), two.prove_ms(), two.verify_ms()), format!("{} sends proved and checked, one core", live.sends))
    };
    rows.push((text::step(2).into(), send_v, send_d));
    if let Some(s) = &live.scan {
        let (v, d) = if zh() {
            (format!("每秒 {} 个输出", group3(s.rate() as u64)), format!("找到 {} / {} 个，金额全部正确", group3(s.mine as u64), group3(s.expected as u64)))
        } else {
            (format!("{} outputs per second", group3(s.rate() as u64)), format!("found {} of {}, every amount correct", group3(s.mine as u64), group3(s.expected as u64)))
        };
        rows.push((text::step(3).into(), v, d));
    }
    if let Some(b) = &live.block {
        let (v, d) = if zh() {
            (format!("每个 2 MB 区块 {} 笔交易", b.txs.len()), format!("验证用时 {:.1} 秒，修剪后 {}", b.check_ms.unwrap_or(0.0) / 1000.0, kb(b.pruned)))
        } else {
            (format!("{} transactions per 2 MB block", b.txs.len()), format!("checked in {:.1} s, {} after pruning", b.check_ms.unwrap_or(0.0) / 1000.0, kb(b.pruned)))
        };
        rows.push((text::step(4).into(), v, d));
    }
    let rate = |p: &str| live.mine.iter().find(|m| m.place == p).map(|m| m.rate()).unwrap_or(0.0);
    let mining = if zh() { format!("GPU {}，全部核心 {}", mhs(rate("GPU")), mhs(rate("all cores"))) } else { format!("{} on the GPU, {} on all cores", mhs(rate("GPU")), mhs(rate("all cores"))) };
    rows.push((text::step(5).into(), mining, "BLAKE2b-512".into()));
    let pass = live.scan.as_ref().is_some_and(|s| s.ok) && live.block.as_ref().is_some_and(|b| b.ok) && live.mine.iter().all(|m| m.ok);
    for (i, (title, value, sub)) in rows.iter().enumerate() {
        let a = ph(t - i as f32 * 0.35, 0.0, 0.5);
        if a <= 0.0 {
            break;
        }
        let y = l.y0 - 10.0 * l.s + i as f32 * row_h;
        f.text(l.x0, y, name, title, white(a));
        let col_x = l.x0 + f.width(name, text::step(2)) + 28.0 * l.s;
        f.text(col_x, y, name, value, lime(a));
        f.text(col_x, y + name * f.line + 4.0 * l.s, detail, sub, gray(a * 1.3));
    }
    let y = l.y0 - 10.0 * l.s + rows.len() as f32 * row_h + 8.0 * l.s;
    let a = ph(t - rows.len() as f32 * 0.35, 0.0, 0.5);
    f.text(l.x0, y, name, if pass { tr("All checks passed", "所有检查均已通过") } else { tr("A CHECK FAILED", "有检查未通过") }, if pass { lime(a) } else { white(a) });
    let mut sy = y + name * f.line + 10.0 * l.s;
    if !r.path.is_empty() {
        let a2 = ph(t, OPEN_REPORT_AFTER - 1.0, OPEN_REPORT_AFTER - 0.5);
        f.text(l.x0, sy, detail, &format!("{}{}", tr("results file: ", "结果文件："), r.path), gray(a2 * 1.3));
        sy += detail * f.line + 30.0 * l.s;
        let a3 = ph(t, OPEN_REPORT_AFTER, OPEN_REPORT_AFTER + 0.6);
        f.text(l.x0, sy, name, tr("Share your results", "分享您的测试结果"), white(a3));
        sy += name * f.line + 8.0 * l.s;
        let pre = tr("Drag and drop the results file into ", "请将结果文件拖放到 ");
        f.text(l.x0, sy, name, pre, white(a3 * 0.9));
        let lx = l.x0 + f.width(name, pre);
        let lw = f.width(name, SHARE_URL);
        f.text(lx, sy, name, SHARE_URL, lime(a3));
        f.rect(lx, sy + name * f.line + 1.0 * l.s, lw, 1.0 * l.s, lime(a3));
        if a3 > 0.5 {
            f.hot.push(([lx, sy, lw, name * f.line + 4.0 * l.s], Hot::Share));
        }
        sy += name * f.line + 8.0 * l.s;
        f.text(l.x0, sy, name, tr("to send it to the team.", "即可发送给我们的团队。"), white(a3 * 0.9));
        sy += name * f.line + 22.0 * l.s;
        f.text(l.x0, sy, detail, tr("Thank you. Results from many kinds of hardware are a big help to us.", "感谢您的参与！来自各种硬件的测试结果对我们非常有帮助。"), gray(a3 * 1.3));
    }
}

fn scene_title(f: &mut Frame, l: &Layout, t: f32) {
    let a = ph(t, 0.0, 0.8);
    let big = (96.0 * l.s).round();
    let word = "Blocknet";
    let logo = (big * 0.95).round();
    let gap = 28.0 * l.s;
    let total = logo + gap + f.width(big, word);
    let x = ((l.w - total) * 0.5).round();
    let y = (l.h * 0.26).round() - 14.0 * l.s * (1.0 - ease(a));
    f.logo = Some([x, y + (big * f.line - logo) * 0.5, logo]);
    f.text(x + logo + gap, y, big, word, white(a));
    let body = (BODY * l.s).round();
    let lines: [(&str, C); 4] = [
        (tr("This is a benchmark.", "这是一个性能测试工具。"), white(1.0)),
        (tr("It measures how the Faraday v2 circuits perform on this computer.", "它会测量 Faraday v2 电路在这台电脑上的运行表现。"), white(1.0)),
        (tr("Your results help us plan the next stages of development.", "您的测试结果将帮助我们规划下一阶段的开发。"), white(1.0)),
        (tr("It takes about 3 minutes. Every number is measured live on this machine.", "整个测试大约需要 3 分钟，所有数据均在本机实时测得。"), gray(1.4)),
    ];
    let mut ly = y + big * f.line + 48.0 * l.s;
    for (i, (s, c)) in lines.iter().enumerate() {
        let k = ph(t - 0.8 - i as f32 * 0.5, 0.0, 0.6);
        let w = f.width(body, s);
        f.text(((l.w - w) * 0.5).round(), ly, body, s, [c[0], c[1], c[2], c[3] * k]);
        ly += body * f.line * 1.5;
    }
    let k = ph(t, 1.6, 2.2);
    let label_start = tr("Start", "开始");
    let bw = f.width(body, label_start) + 64.0 * l.s;
    let bh = body * f.line + 22.0 * l.s;
    let bx0 = ((l.w - bw) * 0.5).round();
    let by0 = ly + 24.0 * l.s;
    let lw = 1.5 * l.s;
    f.rect(bx0, by0, bw, bh, lime(k * 0.12));
    f.rect(bx0, by0, bw, lw, lime(k));
    f.rect(bx0, by0 + bh - lw, bw, lw, lime(k));
    f.rect(bx0, by0, lw, bh, lime(k));
    f.rect(bx0 + bw - lw, by0, lw, bh, lime(k));
    f.text(bx0 + 32.0 * l.s, by0 + 11.0 * l.s, body, label_start, lime(k));
    if k > 0.5 {
        f.hot.push(([bx0, by0, bw, bh], Hot::Start));
    }
    let hint = tr("or press Enter", "或按回车键");
    let hw = f.width((LABEL * l.s).round(), hint);
    f.text(((l.w - hw) * 0.5).round(), by0 + bh + 10.0 * l.s, (LABEL * l.s).round(), hint, gray(k * 1.3));
    let by = by0 + bh + 10.0 * l.s + LABEL * l.s * f.line;
    let ly2 = by + 40.0 * l.s;
    let opts = [("English", false), ("中文", true)];
    let gap2 = 36.0 * l.s;
    let total2: f32 = opts.iter().map(|o| f.width(body, o.0)).sum::<f32>() + gap2;
    let mut bx = ((l.w - total2) * 0.5).round();
    let ka = ph(t, 0.4, 1.0);
    for (name, is_zh) in opts {
        let w = f.width(body, name);
        let on = zh() == is_zh;
        f.text(bx, ly2, body, name, if on { lime(ka) } else { gray(ka * 1.3) });
        if on {
            f.rect(bx, ly2 + body * f.line + 2.0 * l.s, w, 1.5 * l.s, lime(ka));
        }
        f.hot.push(([bx - 8.0 * l.s, ly2 - 6.0 * l.s, w + 16.0 * l.s, body * f.line + 12.0 * l.s], Hot::Lang(is_zh)));
        bx += w + gap2;
    }
}

fn col_dim(c: C) -> C {
    [c[0], c[1], c[2], c[3] * 0.55]
}

fn label(f: &mut Frame, x: f32, y: f32, l: &Layout, s: &str, col: C) {
    f.text(x, y, (LABEL * l.s).round(), s, col);
}

fn scene_address(f: &mut Frame, l: &Layout, t: f32, d: &AddrRes) {
    let fade = ph(t, 0.0, 0.25);
    let cols = 128usize;
    let rows = d.key_bits.len().div_ceil(cols);
    let area_w = (l.x1 - l.x0) * 0.46;
    let cell = (area_w / cols as f32).min((l.y1 - l.y0) / rows as f32).floor().max(2.0);
    let mx = l.x0;
    let my = l.y0;
    let absorb = ph(t, 2.2, 5.6);
    let total_states = d.trace.len();
    let si = ((absorb * (total_states - 1) as f32) as usize).min(total_states - 1);
    let absorbed_bits = ((si / 24) * 136 * 8) as f32 - 19.0 * 8.0;
    let matrix_on = 1.0 - ph(t, 5.6, 6.2);
    let reveal = ph(t, 0.1, 1.9);
    for (i, &b) in d.key_bits.iter().enumerate() {
        let (cx, cy) = (i % cols, i / cols);
        if cy as f32 > reveal * rows as f32 {
            break;
        }
        let gone = (i as f32) < absorbed_bits;
        let owner = i >= d.wallet.kem_key.len() * 8;
        let a = if gone { 0.12 } else { 1.0 } * matrix_on * fade;
        if b {
            f.rect(mx + cx as f32 * cell, my + cy as f32 * cell, cell - 1.0, cell - 1.0, if owner { white(a) } else { white(a * 0.85) });
        } else if owner {
            f.rect(mx + cx as f32 * cell, my + cy as f32 * cell, cell - 1.0, cell - 1.0, dark(a));
        }
    }
    if reveal > 0.0 && matrix_on > 0.0 {
        label(f, mx, my - 16.0 * l.s, l, &if zh() { format!("ML-KEM-768 {} 字节   所有者密钥 {} 字节", d.wallet.kem_key.len(), d.wallet.owner_key.len()) } else { format!("ML-KEM-768  {} B   owner  {} B", d.wallet.kem_key.len(), d.wallet.owner_key.len()) }, gray(matrix_on * fade));
    }
    let sx = l.x0 + (l.x1 - l.x0) * 0.54;
    let sw = (l.x1 - sx).min((l.y1 - l.y0) * 2.4);
    let sc = (sw / 64.0).floor().max(2.0);
    let sy = l.y0;
    let state_on = ph(t, 2.0, 2.3) * (1.0 - ph(t, 6.6, 7.0));
    if state_on > 0.0 {
        let st = if t < 2.2 { [0u64; 25] } else { d.trace[si] };
        let squeeze = ph(t, 5.6, 6.4);
        for lane in 0..25 {
            let keep = lane < 4;
            let a = state_on * fade * if keep { 1.0 } else { 1.0 - squeeze };
            if a <= 0.01 {
                continue;
            }
            let v = st[lane];
            for bit in 0..64 {
                if (v >> bit) & 1 == 1 {
                    let col = if keep && squeeze > 0.0 { lime(a) } else { white(a) };
                    f.rect(sx + bit as f32 * sc, sy + lane as f32 * sc * 1.6, sc - 1.0, sc * 1.6 - 1.0, col);
                }
            }
        }
        let round = si % 24 + 1;
        let block = si / 24 + 1;
        label(f, sx, sy - 16.0 * l.s, l, &if zh() { format!("keccak-f[1600]  数据块 {block:>2}/{}  轮次 {round:>2}/24", total_states / 24) } else { format!("keccak-f[1600]  block {block:>2}/{}  round {round:>2}/24", total_states / 24) }, gray(state_on * fade));
        let bar_y = sy + 25.0 * sc * 1.6 + 8.0 * l.s;
        f.rect(sx, bar_y, sw, 2.0 * l.s, dark(state_on * fade));
        f.rect(sx, bar_y, sw * absorb, 2.0 * l.s, white(state_on * fade));
    }

    let enc = ph(t, 6.4, 7.6);
    if enc > 0.0 {
        let n = d.groups.len();
        let size = ((l.x1 - l.x0) / (n as f32 * f.adv)).min(34.0 * l.s).floor();
        let cw = f.adv * size;
        let ax = l.x0 + ((l.x1 - l.x0) - n as f32 * cw) * 0.5;
        let ay = l.y0 + (l.y1 - l.y0) * 0.62;
        let bc = (cw * 0.42).floor().max(2.0);
        let title = (size * 0.62).round();
        let stack_top = ay - 5.0 * (bc + 2.0) - 6.0 * l.s;
        f.text(ax, stack_top - title * f.line - 14.0 * l.s, title, tr("Blocknet Faraday Address", "Blocknet Faraday 地址"), white(fade * ph(t, 6.4, 6.9)));
        for (i, &g) in d.groups.iter().enumerate() {
            let check = i >= n - 6;
            let k = ease((enc * (n as f32 + 12.0) - i as f32) / 12.0);
            if k <= 0.0 {
                continue;
            }
            let src_x = sx + ((i * 5) % 64) as f32 * sc;
            let src_y = sy + ((i * 5) / 64) as f32 * sc * 1.6;
            for b in 0..5 {
                if (g >> (4 - b)) & 1 == 1 {
                    let tx = ax + i as f32 * cw + (cw - bc) * 0.5;
                    let ty = ay - (5 - b) as f32 * (bc + 2.0) - 6.0 * l.s;
                    let x = src_x + (tx - src_x) * k;
                    let y = src_y + (ty - src_y) * k;
                    f.rect(x, y, bc, bc, if check { lime(fade) } else { white(fade) });
                }
            }
            let ch_on = ph(enc * (n as f32 + 12.0) - i as f32, 8.0, 12.0);
            if ch_on > 0.0 {
                let ch = d.wallet.address.as_bytes()[i] as char;
                f.text(ax + i as f32 * cw, ay, size, &ch.to_string(), if check { lime(ch_on * fade) } else { white(ch_on * fade) });
            }
        }
        if t > 7.8 {
            let a = ph(t, 7.8, 8.2) * fade;
            label(f, ax, ay + size * f.line + 6.0 * l.s, l, &if zh() { format!("{} 个字符   256 位密钥哈希   30 位校验和", n) } else { format!("{} chars   256-bit key hash   30-bit checksum", n) }, gray(a));
        }
    }
}

fn kb(b: usize) -> String {
    if b >= 10_240 { format!("{:.1} KB", b as f64 / 1024.0) } else { format!("{b} B") }
}

fn group3(v: u64) -> String {
    let d = v.to_string();
    let mut out = String::new();
    for (i, c) in d.chars().enumerate() {
        if i > 0 && (d.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(c);
    }
    out
}

fn counter(f: &mut Frame, l: &Layout, a: f32, n: usize, total: usize, title: &str, status: &str) -> f32 {
    let cw = l.x1 - l.x0;
    let big = (54.0 * l.s).round();
    let y0 = l.y0 - 10.0 * l.s;
    let count = group3(n as u64);
    f.text(l.x0, y0, big, &count, lime(a));
    let total_txt = format!(" / {}", group3(total as u64));
    let cx = l.x0 + f.width(big, &count);
    let mid = (BODY * l.s).round();
    f.text(cx, y0 + big * f.line - mid * f.line * 1.25, mid * 1.6, &total_txt, gray(a));
    let after = cx + f.width(mid * 1.6, &total_txt) + 18.0 * l.s;
    f.text(after, y0 + big * f.line - mid * f.line * 2.1, mid, title, white(a));
    f.text(after, y0 + big * f.line - mid * f.line * 1.0, mid, status, gray(a));
    let bar_y = y0 + big * f.line + 10.0 * l.s;
    f.rect(l.x0, bar_y, cw, 2.0 * l.s, dark(a));
    f.rect(l.x0, bar_y, cw * (n as f32 / total.max(1) as f32).min(1.0), 2.0 * l.s, lime(a));
    bar_y
}

fn scene_spend(f: &mut Frame, l: &Layout, t: f32, g: &Live) {
    let a = ph(t, 0.0, 0.3);
    let cw = l.x1 - l.x0;
    let k = g.last;
    let finished = g.done(pipeline::SEND);
    let rate = g.send_rate();
    let status = match (finished, g.sends == 0, zh()) {
        (true, _, true) => format!("每秒 {:.1} 笔   已完成", rate),
        (true, _, false) => format!("{:.1} per second   done", rate),
        (false, true, _) => tr("starting", "正在开始").into(),
        (false, false, true) => format!("每秒 {:.1} 笔   当前：{} 输入 / {} 输出", rate, SHAPES[k], SHAPES[k]),
        (false, false, false) => format!("{:.1} per second   now: {} in / {} out", rate, SHAPES[k], SHAPES[k]),
    };
    let bar_y = counter(f, l, a, g.sends, SEND_RUNS, tr("transactions proved and checked", "笔交易已完成证明与验证"), &status);

    let head = (24.0 * l.s).round();
    let num = (20.0 * l.s).round();
    let cy = bar_y + 34.0 * l.s;
    let rows_h = (l.y1 + 40.0 * l.s - cy) / 4.4;
    let max_size = g.stats.iter().map(|s| s.proof_bytes).max().unwrap_or(1).max(1) as f32;
    let max_ms = g.stats.iter().map(|s| s.prove_ms()).fold(1.0, f64::max) as f32;
    let c1 = l.x0;
    let c2 = l.x0 + cw * 0.17;
    let c3 = l.x0 + cw * 0.56;
    let bw = cw * 0.27;
    let tw = cw * 0.27;
    label(f, c1, cy, l, tr("inputs / outputs", "输入 / 输出"), gray(a));
    label(f, c2, cy, l, tr("proof size", "证明大小"), gray(a));
    f.rect(c3, cy + 4.0 * l.s, 8.0 * l.s, 8.0 * l.s, lime(a));
    let create = tr("time to create", "生成耗时");
    label(f, c3 + 12.0 * l.s, cy, l, create, gray(a));
    let c3b = c3 + 12.0 * l.s + f.width((LABEL * l.s).round(), create) + 24.0 * l.s;
    f.rect(c3b, cy + 4.0 * l.s, 8.0 * l.s, 8.0 * l.s, gray(a));
    label(f, c3b + 12.0 * l.s, cy, l, tr("time to check", "验证耗时"), gray(a));
    for (i, st) in g.stats.iter().enumerate() {
        let n = SHAPES[i];
        let y = cy + 24.0 * l.s + i as f32 * rows_h;
        let on = i == k && !finished && g.sends > 0;
        f.text(c1, y, head, &format!("{n} / {n}"), if on { white(a) } else { white(a * 0.7) });
        if st.runs == 0 {
            continue;
        }
        let bh = 12.0 * l.s;
        let sw = bw * st.proof_bytes as f32 / max_size;
        f.rect(c2, y + 4.0 * l.s, sw, bh, white(a));
        f.text(c2 + sw + 10.0 * l.s, y, num, &kb(st.proof_bytes), white(a));
        let pw = tw * st.prove_ms() as f32 / max_ms;
        let vw = tw * st.verify_ms() as f32 / max_ms;
        f.rect(c3, y + 2.0 * l.s, pw, bh * 0.75, lime(a));
        f.rect(c3, y + 2.0 * l.s + bh, vw, bh * 0.75, gray(a));
        label(f, c3 + pw + 8.0 * l.s, y - 2.0 * l.s, l, &format!("{:.1} ms", st.prove_ms()), lime(a));
        label(f, c3 + vw + 8.0 * l.s, y + bh - 1.0 * l.s, l, &format!("{:.1} ms", st.verify_ms()), gray(a));
    }
    let foot = cy + 24.0 * l.s + 4.0 * rows_h;
    label(f, c1, foot, l, tr("live on this machine   one core   every input a fresh coin in the 1,048,576-output set", "本机实时测量   单核   每个输入都是 1,048,576 个输出中的一枚新币"), gray(a));
}

fn scene_set_build(f: &mut Frame, l: &Layout, t: f32, built: usize) {
    let a = ph(t, 0.0, 0.3);
    counter(f, l, a, built, NSET, tr("outputs committed", "个输出已生成承诺"), tr("each a real coin: its own spend key, owner key and amount", "每个都是真实的币：各有自己的花费密钥、所有者密钥和金额"));
}

fn scene_scan(f: &mut Frame, l: &Layout, t: f32, s: &pipeline::ScanRes) {
    let a = ph(t, 0.0, 0.3);
    let status = if zh() { format!("每秒 {} 个输出   已排除 {} 个视图标签误匹配", group3(s.rate() as u64), s.tag_only) } else { format!("{} outputs/s   {} view-tag false hits rejected", group3(s.rate() as u64), s.tag_only) };
    let bar_y = counter(f, l, a, s.mine, s.expected, tr("outputs found for this wallet", "个输出属于本钱包"), &status);
    let n = s.marks.len();
    let cw = l.x1 - l.x0;
    let top = bar_y + 34.0 * l.s;
    let h = l.y1 + 30.0 * l.s - top;
    let cols = ((n as f32 * cw / h).sqrt().ceil() as usize).max(1);
    let rows = n.div_ceil(cols);
    let cell = (cw / cols as f32).min(h / rows as f32).floor().max(2.0);
    let reveal = ph(t, 0.2, 2.6);
    for (i, m) in s.marks.iter().enumerate() {
        let (cx, cy) = (i % cols, i / cols);
        let k = ph(reveal * (cols + rows) as f32 - (cx + cy) as f32, 0.0, 1.0);
        if k <= 0.0 {
            continue;
        }
        let col = match m {
            Scan::Mine(_) => lime(a * k),
            Scan::TagOnly => gray(a * k),
            Scan::Skip => dark(a * k),
        };
        f.rect(l.x0 + cx as f32 * cell, top + cy as f32 * cell, cell - 1.0, cell - 1.0, col);
    }
    label(f, l.x0, top + rows as f32 * cell + 8.0 * l.s, l, &if zh() { format!("共 {} 个输出，来自 {} 笔交易，其中约一半发往另一个钱包", group3(n as u64), SEND_RUNS) } else { format!("{} outputs from {} transactions, half sent to another wallet", group3(n as u64), SEND_RUNS) }, gray(a));
}

fn hash01(a: usize, b: usize) -> f32 {
    let mut x = (a as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (b as u64).wrapping_mul(0xc2b2_ae3d_27d4_eb4f);
    x ^= x >> 31;
    x = x.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x ^= x >> 29;
    (x >> 40) as f32 / (1u64 << 24) as f32
}

fn mb(v: f64) -> String {
    if v >= 1048576.0 { format!("{:.1} MB", v / 1048576.0) } else { format!("{:.1} KB", v / 1024.0) }
}

const BLOCK_MINUTES: [f64; 4] = [2.0, 3.0, 5.0, 10.0];

fn scene_block(f: &mut Frame, l: &Layout, t: f32, ready: Option<f32>, b: &pipeline::BlockRes) {
    let a = ph(t, 0.0, 0.3);
    let status = match b.check_ms {
        Some(ms) if b.ok => if zh() { format!("{:.2} MB，验证用时 {:.2} 秒", b.bytes as f64 / 1048576.0, ms / 1000.0) } else { format!("{:.2} MB checked in {:.2} s", b.bytes as f64 / 1048576.0, ms / 1000.0) },
        Some(_) => tr("block rejected", "区块未通过验证").into(),
        None => tr("every proof, every nullifier, the tx root", "逐一验证每个证明、每个作废标识和交易根").into(),
    };
    let bar_y = counter(f, l, a, b.checked, b.txs.len(), tr("transactions in one 2 MB block checked", "笔交易已验证（一个 2 MB 区块）"), &status);

    let p0 = 0.8;
    let col_lag = 0.035;
    let cell_lag = 0.018;
    let since = ready.filter(|_| b.ok).map_or(-1.0, |r| r - p0);
    let ncols = b.txs.len().max(1);
    let max_cells = b.cells.iter().map(|c| c.len()).max().unwrap_or(1);
    let wave_end = ncols as f32 * col_lag + max_cells as f32 * cell_lag + 0.35;
    let tt = if since < 0.0 { -1.0 } else { since - wave_end };

    let top = bar_y + 70.0 * l.s;
    let bottom = l.y1 + 20.0 * l.s;
    let gw = (l.x1 - l.x0) * 0.66;
    let cw_ = (gw / ncols as f32).floor().max(2.0);
    let ch = ((bottom - top) / max_cells as f32).floor().max(2.0);
    let gx = l.x0;
    let base = top + max_cells as f32 * ch;

    let cs = cw_.min(ch);
    let n_target = b.pruned_cells.len().max(1);
    let tcols = (n_target as f32).sqrt().ceil() as usize;
    let trows = n_target.div_ceil(tcols);
    let target = |idx: usize| (gx + (idx % tcols) as f32 * cs, top + (idx / tcols) as f32 * cs);
    let merge_at = |i: usize| ease(ph(tt - 2.8 - i as f32 * 0.015, 0.0, 0.9));
    let packed = ph(tt - 2.8 - ncols as f32 * 0.015 - 0.8, 0.0, 0.4);

    let mut alive = 0usize;
    let mut proof_cells = 0usize;
    for (i, (cells, &(meta, _))) in b.cells.iter().zip(&b.txs).enumerate() {
        let meta_cells = meta.div_ceil(pipeline::CELL);
        let checked = i < b.checked;
        let x = gx + i as f32 * cw_;
        let fill = ph(t * 3.0 - i as f32 * 0.04, 0.0, 1.0);
        let shown = (fill * cells.len() as f32).ceil() as usize;
        proof_cells += cells.len() - meta_cells;
        for (k, &v) in cells.iter().enumerate().take(shown) {
            let y = base - (k + 1) as f32 * ch;
            let lum = 0.35 + 0.65 * (v as f32 / 255.0);
            if k < meta_cells {
                let m = merge_at(i);
                let off = vole::wire::HEADER_LEN + 4 + i * meta + k * pipeline::CELL;
                let (tx_, ty_) = target((off / pipeline::CELL).min(n_target - 1));
                let al = a * lum * (1.0 - packed);
                let col = if since >= 0.0 { lime(al) } else { gray(al) };
                let (w, h) = (cw_ + (cs - cw_) * m, ch + (cs - ch) * m);
                f.rect(x + (tx_ - x) * m, y + (ty_ - y) * m, w - 1.0, h - 1.0, col);
                continue;
            }
            let from_top = cells.len() - 1 - k;
            let gone = ph(since - i as f32 * col_lag - from_top as f32 * cell_lag, 0.0, 0.35);
            if gone > 0.0 {
                let g = ph(tt - 1.6 - hash01(i, k) * 0.7, 0.0, 0.9);
                if g < 1.0 {
                    let gg = g * g;
                    let dx = (hash01(k, i) - 0.5) * gw * 0.6 * gg;
                    let dy = -gg * (base - l.y0 + 60.0 * l.s) * (0.7 + 0.6 * hash01(i + 7, k));
                    let col = if g > 0.0 { gray(a * 0.55 * (1.0 - g)) } else { dark(a * gone * 0.8) };
                    let sz = 1.0 - 0.5 * g;
                    f.rect(x + dx, y + dy, (cw_ - 1.0) * sz, (ch - 1.0) * sz, col);
                }
            }
            if gone >= 1.0 {
                continue;
            }
            if gone == 0.0 {
                alive += 1;
            }
            let rise = ease(gone) * ch * 3.0;
            let al = a * lum * (1.0 - gone);
            let col = if checked { lime(al) } else { white(al * 0.85) };
            f.rect(x, y - rise, cw_ - 1.0, (ch - 1.0) * (1.0 - gone * 0.5), col);
        }
    }

    let word = ph(tt, 0.0, 0.9) * (1.0 - ph(tt, 1.5, 2.1));
    if word > 0.0 {
        let meta_h = b.txs.iter().map(|&(m, _)| m.div_ceil(pipeline::CELL)).max().unwrap_or(0) as f32 * ch;
        let (x0, x1, y0, y1) = (gx, gx + ncols as f32 * cw_, top, base - meta_h);
        let size = ((y1 - y0) * 0.22).min((x1 - x0) / (6.0 * f.adv) * 0.6).round();
        let pruned_word = tr("pruned", "已修剪");
        let w = f.width(size, pruned_word);
        f.text(x0 + (x1 - x0 - w) * 0.5, y0 + (y1 - y0 - size * f.line) * 0.5, size, pruned_word, gray(a * ease(word) * 0.9));
    }

    if packed > 0.0 {
        for (idx, &v) in b.pruned_cells.iter().enumerate() {
            let (px, py) = target(idx);
            let lum = 0.35 + 0.65 * (v as f32 / 255.0);
            f.rect(px, py, cs - 1.0, cs - 1.0, lime(a * lum * packed));
        }
        let lx = gx + tcols as f32 * cs + 24.0 * l.s;
        let big = (30.0 * l.s).round();
        let ly = top + (trows as f32 * cs - big * f.line - 16.0 * l.s) * 0.5;
        f.text(lx, ly, big, &mb(b.pruned as f64), lime(a * packed));
        label(f, lx, ly + big * f.line + 4.0 * l.s, l, &if zh() { format!("一个已存储区块   {} 笔交易", b.txs.len()) } else { format!("one stored block   {} transactions", b.txs.len()) }, gray(a * packed));
    }

    if let (Some(check_ms), true) = (b.check_ms, tt > 4.0) {
        let ty0 = top + trows as f32 * cs + 56.0 * l.s;
        let rows = BLOCK_MINUTES.len() + 1;
        let rh = ((base + 30.0 * l.s - ty0) / (rows as f32 + 0.5)).max(26.0 * l.s);
        label(f, gx, ty0 - 22.0 * l.s, l, tr("transactions per hour, at each block time", "不同出块时间下每小时可处理的交易数"), gray(a * ph(tt, 4.0, 4.4)));
        let name = (15.0 * l.s).round();
        let mbw = ((gw - 230.0 * l.s) / 30.0).floor().max(3.0);
        let bars_x = gx + 104.0 * l.s;
        let num_x = bars_x + 30.0 * mbw + 12.0 * l.s;
        let ours: Vec<(f64, u64)> = BLOCK_MINUTES.iter().map(|&m| (60.0 / m, (b.txs.len() as f64 * 60.0 / m).round() as u64)).collect();
        let far_per_hour = 60.0 / pipeline::FARADAY_V1_BLOCK_MIN;
        let far_tx_h = (pipeline::FARADAY_V1_ONE_BUILDER_PER_BLOCK as f64 * far_per_hour).round() as u64;
        let far_cap_h = (pipeline::FARADAY_V1_CAP_PER_BLOCK as f64 * far_per_hour).round() as u64;
        let max_tx_h = ours.iter().map(|o| o.1).chain([far_cap_h]).max().unwrap_or(1).max(1) as f32;
        let bar_w = num_x - 12.0 * l.s - bars_x;
        let row = |f: &mut Frame, r: usize, y: f32, title: &str, per_hour: f64, tx_h: u64, cap_h: Option<u64>, sub: &str, ours: bool| {
            let start = 4.2 + r as f32 * 0.35;
            let appear = ph(tt - start, 0.0, 0.4);
            if appear <= 0.0 {
                return;
            }
            if let Some(cap) = cap_h {
                let x0 = bars_x + bar_w * tx_h as f32 / max_tx_h;
                let x1 = bars_x + bar_w * cap as f32 / max_tx_h;
                let k = ph(tt - start - 0.5, 0.0, 0.4);
                f.rect(x0, y + 3.0 * l.s, (x1 - x0) * k, 12.0 * l.s, dark(a * appear));
            }
            f.text(gx, y, name, title, if ours { white(a * appear) } else { gray(a * appear) });
            let n = per_hour.round().max(1.0) as usize;
            let total = bar_w * tx_h as f32 / max_tx_h;
            let seg = total / n as f32;
            for j in 0..n {
                let pop = ph(tt - start - 0.1 - j as f32 * 0.02, 0.0, 0.15);
                let w = (seg - 2.0 * l.s).max(1.0);
                f.rect(bars_x + j as f32 * seg, y + 3.0 * l.s, w, 12.0 * l.s, if ours { lime(a * pop) } else { gray(a * pop) });
            }
            f.text(num_x, y, name, &if zh() { format!("{} 笔/小时", group3(tx_h)) } else { format!("{} tx/h", group3(tx_h)) }, if ours { lime(a * appear) } else { white(a * appear) });
            label(f, bars_x, y + 19.0 * l.s, l, sub, gray(a * appear));
        };
        for (r, &mins) in BLOCK_MINUTES.iter().enumerate() {
            let (per_hour, tx_h) = ours[r];
            let (sent, kept, check_s) = (mb(b.bytes as f64 * per_hour), mb(b.pruned as f64 * per_hour), check_ms / 1000.0 * per_hour);
            let sub = if zh() {
                format!("{:.0} 个区块，每块 {} 笔   发送 {}   存储 {}   单核验证 {:.0} 秒", per_hour, b.txs.len(), sent, kept, check_s)
            } else {
                format!("{:.0} blocks of {} tx   {} sent   {} stored   {:.0} s of one core to check", per_hour, b.txs.len(), sent, kept, check_s)
            };
            let title = if zh() { format!("{mins:.0} 分钟") } else { format!("{mins:.0} min") };
            row(f, r, ty0 + r as f32 * rh, &title, per_hour, tx_h, None, &sub, true);
        }
        let y_old = ty0 + (BLOCK_MINUTES.len() as f32 + 0.5) * rh;
        f.rect(gx, y_old - 0.3 * rh, gw, 1.0 * l.s, dark(a * ph(tt, 5.6, 6.0)));
        let sub = if zh() {
            format!("单个构建者每 {:.0} 分钟区块约 {} 笔   深色部分：每块上限 {} 笔", pipeline::FARADAY_V1_BLOCK_MIN, pipeline::FARADAY_V1_ONE_BUILDER_PER_BLOCK, pipeline::FARADAY_V1_CAP_PER_BLOCK)
        } else {
            format!("~{} tx per {:.0} min block, one builder   dark: cap of {} per block", pipeline::FARADAY_V1_ONE_BUILDER_PER_BLOCK, pipeline::FARADAY_V1_BLOCK_MIN, pipeline::FARADAY_V1_CAP_PER_BLOCK)
        };
        row(f, BLOCK_MINUTES.len(), y_old, "Faraday V1", far_per_hour, far_tx_h, Some(far_cap_h), &sub, false);
    }

    let rx = gx + gw + 40.0 * l.s;
    let pruning_done = proof_cells > 0 && alive == 0 && since > 0.0;
    let state = if since < 0.0 { 0 } else if pruning_done { 2 } else { 1 };
    let ss = (14.0 * l.s).round();
    let mut sy = top;
    for (k, name) in [tr("broadcast", "广播"), tr("pruning", "修剪中"), tr("stored", "已存储")].iter().enumerate() {
        let col = if k == state { if k == 2 { lime(a) } else { white(a) } } else { dark(a) };
        f.rect(rx, sy + ss * f.line * 0.5 - 1.0 * l.s, 6.0 * l.s, 2.0 * l.s, col);
        f.text(rx + 14.0 * l.s, sy, ss, name, col);
        sy += ss * f.line * 1.3;
    }
    let frac_alive = if proof_cells == 0 { 1.0 } else { alive as f64 / proof_cells as f64 };
    let now_bytes = if pruning_done { b.pruned as f64 } else { b.pruned as f64 + (b.bytes - b.pruned) as f64 * if since < 0.0 { 1.0 } else { frac_alive } };
    let big = (36.0 * l.s).round();
    let ry = sy + 30.0 * l.s;
    label(f, rx, ry, l, tr("broadcast, with proofs", "广播（含证明）"), gray(a));
    f.text(rx, ry + 16.0 * l.s, big, &mb(b.bytes as f64), if since < 0.0 { white(a) } else { gray(a) });
    if since >= 0.0 {
        let ry2 = ry + 16.0 * l.s + big * f.line + 24.0 * l.s;
        label(f, rx, ry2, l, tr("stored after the check", "验证后存储"), gray(a));
        f.text(rx, ry2 + 16.0 * l.s, big, &mb(now_bytes), if pruning_done { lime(a) } else { white(a) });
        if pruning_done {
            label(f, rx, ry2 + 16.0 * l.s + big * f.line + 6.0 * l.s, l, &if zh() { format!("磁盘占用降为原来的 1/{:.1}", b.bytes as f64 / b.pruned as f64) } else { format!("{:.1}x less disk", b.bytes as f64 / b.pruned as f64) }, gray(a * ph(tt, 0.0, 0.6)));
        }
    }
    let legend = a * (1.0 - ph(tt, 1.6, 2.4));
    if legend > 0.0 {
        let key = base + 16.0 * l.s;
        f.rect(gx, key + 3.0 * l.s, 8.0 * l.s, 8.0 * l.s, gray(legend));
        let fields = tr("inputs, outputs, fee", "输入、输出、手续费");
        label(f, gx + 12.0 * l.s, key, l, fields, gray(legend));
        let k2 = gx + 12.0 * l.s + f.width((LABEL * l.s).round(), fields) + 24.0 * l.s;
        f.rect(k2, key + 3.0 * l.s, 8.0 * l.s, 8.0 * l.s, white(legend));
        let proof_word = tr("proof", "证明");
        label(f, k2 + 12.0 * l.s, key, l, proof_word, gray(legend));
        let k3 = k2 + 12.0 * l.s + f.width((LABEL * l.s).round(), proof_word) + 24.0 * l.s;
        label(f, k3, key, l, tr("1 cell = 1 KB of the real block", "1 格 = 真实区块中的 1 KB"), gray(legend));
    }
}

fn scene_set(f: &mut Frame, l: &Layout, t: f32, d: &pipeline::SetRes) {
    let fade = ph(t, 0.0, 0.25);
    let fh = (l.y1 - l.y0) * 1.04;
    let fw = fh * FIELD_W as f32 / FIELD_H as f32;
    let fx = l.x0;
    let fy = l.y0;
    let (row, col) = (d.real / FIELD_W, d.real % FIELD_W);
    let cu = (col as f32 + 0.5) / FIELD_W as f32;
    let cv = (row as f32 + 0.5) / FIELD_H as f32;
    let zoom = ease(ph(t, 5.6, 8.0));
    let span = 1.0 - zoom * (1.0 - 28.0 / FIELD_W as f32);
    let uc = cu * zoom + 0.5 * (1.0 - zoom);
    let vc = cv * zoom + 0.5 * (1.0 - zoom);
    let (u0, v0, u1, v1) = (uc - span * 0.5, vc - span * 0.5, uc + span * 0.5, vc + span * 0.5);
    let wipe = ph(t, 0.05, 1.3);
    f.image = Some(([fx, fy, fw, fh * wipe], [u0, v0, u1, v0 + (v1 - v0) * wipe], fade));
    let to_x = |u: f32| fx + (u - u0) / (u1 - u0) * fw;
    let to_y = |v: f32| fy + (v - v0) / (v1 - v0) * fh;

    let bit = (8.0 * l.s).floor();
    let gap = 3.0 * l.s;
    let left_on = ph(t, 1.4, 1.6);
    if left_on > 0.0 {
        let settle = t >= 2.8;
        for i in 0..ETA {
            let on = if settle { d.left[i] } else { (((t * 30.0) as u64).wrapping_mul(2654435761) >> (i % 31)) & 1 == 1 };
            let y = fy + i as f32 * (fh / ETA as f32);
            let x = fx - 3.0 * bit - gap;
            f.rect(x, y, bit, fh / ETA as f32 - 2.0, if on { if settle { lime(fade) } else { white(fade) } } else { dark(fade * left_on) });
        }
        if settle {
            let sweep = ease(ph(t, 2.8, 3.4));
            let yy = fy + (to_y(cv) - fy) * sweep;
            if yy >= fy && yy <= fy + fh {
                f.rect(fx, yy - 0.5 * l.s, fw, 1.0 * l.s, lime(fade));
            }
            label(f, fx - 3.0 * bit - gap, fy + fh + 8.0 * l.s, l, &if zh() { format!("第 {row} 行") } else { format!("row {row}") }, gray(fade));
        }
    }
    let right_on = ph(t, 3.4, 3.6);
    if right_on > 0.0 {
        let settle = t >= 4.8;
        for i in 0..ETA {
            let on = if settle { d.right[i] } else { (((t * 30.0) as u64 + 77).wrapping_mul(2246822519) >> (i % 29)) & 1 == 1 };
            let x = fx + i as f32 * (fw / ETA as f32);
            let y = fy - 3.0 * bit - gap;
            f.rect(x, y, fw / ETA as f32 - 2.0, bit, if on { if settle { lime(fade) } else { white(fade) } } else { dark(fade * right_on) });
        }
        if settle {
            let sweep = ease(ph(t, 4.8, 5.4));
            let xx = fx + (to_x(cu) - fx) * sweep;
            if xx >= fx && xx <= fx + fw {
                f.rect(xx - 0.5 * l.s, fy, 1.0 * l.s, fh, lime(fade));
            }
            label(f, fx + fw + 8.0 * l.s, fy - 3.0 * bit - gap, l, &if zh() { format!("第 {col} 列") } else { format!("col {col}") }, gray(fade));
        }
    }
    if zoom > 0.0 {
        let cx = to_x(cu);
        let cy = to_y(cv);
        let px = fw / ((u1 - u0) * FIELD_W as f32);
        let r = px * 0.5 + 2.0 * l.s;
        let lw = 1.5 * l.s;
        f.rect(cx - r, cy - r, 2.0 * r, lw, lime(fade * zoom));
        f.rect(cx - r, cy + r - lw, 2.0 * r, lw, lime(fade * zoom));
        f.rect(cx - r, cy - r, lw, 2.0 * r, lime(fade * zoom));
        f.rect(cx + r - lw, cy - r, lw, 2.0 * r, lime(fade * zoom));
    }
    let panel = ph(t, 8.0, 8.6);
    if panel > 0.0 {
        let px = fx + fw + 24.0 * l.s;
        let pw = (l.w * 0.97 - px).max(80.0);
        let bc = (pw / 32.0).floor().max(2.0);
        let py = fy + fh * 0.5 - 10.0 * bc;
        for (i, b) in d.commit.iter().enumerate() {
            for k in 0..8 {
                let n = i * 8 + k;
                if n as f32 > panel * 640.0 {
                    break;
                }
                if (b >> (7 - k)) & 1 == 1 {
                    f.rect(px + (n % 32) as f32 * bc, py + (n / 32) as f32 * bc, bc - 1.0, bc - 1.0, white(fade));
                }
            }
        }
        label(f, px, py - 16.0 * l.s, l, &if zh() { format!("第 {} 个输出，共 {} 个", d.real, NSET) } else { format!("output {} of {}", d.real, NSET) }, gray(fade * panel));
        label(f, px, py + 20.0 * bc + 8.0 * l.s, l, tr("commitment  80 B", "承诺  80 字节"), gray(fade * panel));
    }
    if t < 5.6 {
        label(f, fx, fy + fh + 24.0 * l.s, l, &if zh() { format!("{} 个输出   {} x {}", NSET, FIELD_H, FIELD_W) } else { format!("{} outputs   {} x {}", NSET, FIELD_H, FIELD_W) }, gray(fade * ph(t, 0.6, 1.0)));
    }
}

struct Atlas {
    levels: Vec<(u32, u32, Vec<u8>)>,
    cell: (u32, u32),
    cols: u32,
    adv: f32,
    line: f32,
}

fn font_atlas() -> Atlas {
    use ab_glyph::{Font, FontRef, PxScale, ScaleFont};
    let font = FontRef::try_from_slice(include_bytes!("../assets/JetBrainsMono-Regular.ttf")).expect("font");
    let px = 96.0f32;
    let sf = font.as_scaled(PxScale::from(px));
    let adv = sf.h_advance(font.glyph_id('M'));
    let line = sf.ascent() - sf.descent();
    let pad = (px * 0.25).ceil();
    let cw = (adv + 2.0 * pad).ceil() as u32;
    let ch = (line + 2.0 * pad).ceil() as u32;
    let cols = 16u32;
    let (ccw, cch) = cjk::CJK_CELL;
    let cjk_rows = (cjk::CJK_GLYPHS.len() as u32).div_ceil(cols);
    let aw = (cw * cols).max(ccw * cols).next_power_of_two();
    let ah = (ch * 6 + cch * cjk_rows).next_power_of_two();
    let mut img = vec![0u8; (aw * ah) as usize];
    let mut map = std::collections::HashMap::new();
    let uv = |x: u32, y: u32, w: u32, h: u32| [x as f32 / aw as f32, y as f32 / ah as f32, (x + w) as f32 / aw as f32, (y + h) as f32 / ah as f32];
    for code in 33u32..127 {
        let k = code - 32;
        let (gx, gy) = (k % cols, k / cols);
        let c = char::from_u32(code).unwrap();
        let glyph = font.glyph_id(c).with_scale_and_position(PxScale::from(px), ab_glyph::point(pad, pad + sf.ascent()));
        if let Some(og) = font.outline_glyph(glyph) {
            let b = og.px_bounds();
            og.draw(|x, y, cov| {
                let xx = (b.min.x as i32 + x as i32).clamp(0, cw as i32 - 1) as u32 + gx * cw;
                let yy = (b.min.y as i32 + y as i32).clamp(0, ch as i32 - 1) as u32 + gy * ch;
                let p = &mut img[(yy * aw + xx) as usize];
                *p = (*p).max((cov.clamp(0.0, 1.0) * 255.0) as u8);
            });
        }
        map.insert(c, GInfo { uv: uv(gx * cw, gy * ch, cw, ch), size: [cw as f32 / px, ch as f32 / px], off: [-pad / px, -pad / px], adv: adv / px });
    }
    let base = ch * 6;
    let cpx = cjk::CJK_PX;
    let dy = (sf.ascent()) / px - (cjk::CJK_PAD + cjk::CJK_ASCENT) / cpx;
    for (i, &(c, a)) in cjk::CJK_GLYPHS.iter().enumerate() {
        let (gx, gy) = (i as u32 % cols, i as u32 / cols);
        let src = &cjk::CJK_BITMAP[i * (ccw * cch) as usize..(i + 1) * (ccw * cch) as usize];
        for y in 0..cch {
            let row = ((base + gy * cch + y) * aw + gx * ccw) as usize;
            img[row..row + ccw as usize].copy_from_slice(&src[(y * ccw) as usize..((y + 1) * ccw) as usize]);
        }
        map.insert(c, GInfo { uv: uv(gx * ccw, base + gy * cch, ccw, cch), size: [ccw as f32 / cpx, cch as f32 / cpx], off: [-cjk::CJK_PAD / cpx, dy], adv: a / cpx });
    }
    let _ = GLYPHS.set(map);
    let mut levels = vec![(aw, ah, img)];
    while levels.last().unwrap().0 > 16 && levels.len() < 6 {
        let (w, h, src) = levels.last().unwrap();
        let (nw, nh) = (w / 2, h / 2);
        let mut dst = vec![0u8; (nw * nh) as usize];
        for y in 0..nh {
            for x in 0..nw {
                let s = |dx: u32, dy: u32| src[((2 * y + dy) * w + 2 * x + dx) as usize] as u32;
                dst[(y * nw + x) as usize] = ((s(0, 0) + s(1, 0) + s(0, 1) + s(1, 1)) / 4) as u8;
            }
        }
        levels.push((nw, nh, dst));
    }
    Atlas { levels, cell: (cw, ch), cols, adv: adv / px, line: line / px }
}

struct Gpu {
    window: Arc<Window>,
    surface: wgpu::Surface<'static>,
    device: wgpu::Device,
    queue: wgpu::Queue,
    config: wgpu::SurfaceConfiguration,
    ubuf: wgpu::Buffer,
    bind: wgpu::BindGroup,
    rect_pipe: wgpu::RenderPipeline,
    image_pipe: wgpu::RenderPipeline,
    glyph_pipe: wgpu::RenderPipeline,
    logo_pipe: wgpu::RenderPipeline,
    rect_buf: wgpu::Buffer,
    glyph_buf: wgpu::Buffer,
    atlas: (f32, f32, f32, f32, f32, f32, f32),
    data_pipe: wgpu::RenderPipeline,
    quad_buf: wgpu::Buffer,
    field_tex: wgpu::Texture,
    field_ready: bool,
}

impl Gpu {
    fn new(window: Arc<Window>) -> Gpu {
        let instance = wgpu::Instance::new(wgpu::InstanceDescriptor::new_without_display_handle());
        let surface = instance.create_surface(window.clone()).expect("surface");
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            compatible_surface: Some(&surface),
            force_fallback_adapter: false,
            apply_limit_buckets: false,
        }))
        .expect("adapter");
        let (device, queue) = pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor { label: None, ..Default::default() })).expect("device");
        let size = window.inner_size();
        let mut config = surface.get_default_config(&adapter, size.width.max(1), size.height.max(1)).expect("config");
        let caps = surface.get_capabilities(&adapter);
        if let Some(f) = caps.formats.iter().find(|f| f.is_srgb()) {
            config.format = *f;
        }
        config.present_mode = wgpu::PresentMode::AutoNoVsync;
        config.desired_maximum_frame_latency = 1;
        surface.configure(&device, &config);

        let atlas = font_atlas();
        let (aw, ah) = (atlas.levels[0].0, atlas.levels[0].1);
        let font_tex = device.create_texture(&wgpu::TextureDescriptor {
            label: None,
            size: wgpu::Extent3d { width: aw, height: ah, depth_or_array_layers: 1 },
            mip_level_count: atlas.levels.len() as u32,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format: wgpu::TextureFormat::R8Unorm,
            usage: wgpu::TextureUsages::TEXTURE_BINDING | wgpu::TextureUsages::COPY_DST,
            view_formats: &[],
        });
        for (lvl, (lw, lh, px)) in atlas.levels.iter().enumerate() {
            queue.write_texture(
                wgpu::TexelCopyTextureInfo { texture: &font_tex, mip_level: lvl as u32, origin: wgpu::Origin3d::ZERO, aspect: wgpu::TextureAspect::All },
                px,
                wgpu::TexelCopyBufferLayout { offset: 0, bytes_per_row: Some(*lw), rows_per_image: Some(*lh) },
                wgpu::Extent3d { width: *lw, height: *lh, depth_or_array_layers: 1 },
            );
        }
        let field_tex = device.create_texture(&wgpu::TextureDescriptor {
            label: None,
            size: wgpu::Extent3d { width: FIELD_W as u32, height: FIELD_H as u32, depth_or_array_layers: 1 },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format: wgpu::TextureFormat::R8Unorm,
            usage: wgpu::TextureUsages::TEXTURE_BINDING | wgpu::TextureUsages::COPY_DST,
            view_formats: &[],
        });
        let data_tex = device.create_texture(&wgpu::TextureDescriptor {
            label: None,
            size: wgpu::Extent3d { width: DATA_TEX, height: DATA_TEX, depth_or_array_layers: 1 },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu::TextureDimension::D2,
            format: wgpu::TextureFormat::Rgba8Unorm,
            usage: wgpu::TextureUsages::TEXTURE_BINDING | wgpu::TextureUsages::COPY_DST,
            view_formats: &[],
        });
        let lin_s = device.create_sampler(&wgpu::SamplerDescriptor {
            mag_filter: wgpu::FilterMode::Linear,
            min_filter: wgpu::FilterMode::Linear,
            mipmap_filter: wgpu::MipmapFilterMode::Linear,
            ..Default::default()
        });
        let near_s = device.create_sampler(&wgpu::SamplerDescriptor { ..Default::default() });
        let ubuf = device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size: std::mem::size_of::<U>() as u64,
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let vis = wgpu::ShaderStages::VERTEX | wgpu::ShaderStages::FRAGMENT;
        let texe = |b| wgpu::BindGroupLayoutEntry {
            binding: b,
            visibility: vis,
            ty: wgpu::BindingType::Texture { sample_type: wgpu::TextureSampleType::Float { filterable: true }, view_dimension: wgpu::TextureViewDimension::D2, multisampled: false },
            count: None,
        };
        let sampe = |b| wgpu::BindGroupLayoutEntry { binding: b, visibility: vis, ty: wgpu::BindingType::Sampler(wgpu::SamplerBindingType::Filtering), count: None };
        let layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: None,
            entries: &[
                wgpu::BindGroupLayoutEntry {
                    binding: 0,
                    visibility: vis,
                    ty: wgpu::BindingType::Buffer { ty: wgpu::BufferBindingType::Uniform, has_dynamic_offset: false, min_binding_size: None },
                    count: None,
                },
                texe(1),
                sampe(2),
                texe(3),
                sampe(4),
                texe(5),
            ],
        });
        let bind = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: None,
            layout: &layout,
            entries: &[
                wgpu::BindGroupEntry { binding: 0, resource: ubuf.as_entire_binding() },
                wgpu::BindGroupEntry { binding: 1, resource: wgpu::BindingResource::TextureView(&font_tex.create_view(&Default::default())) },
                wgpu::BindGroupEntry { binding: 2, resource: wgpu::BindingResource::Sampler(&lin_s) },
                wgpu::BindGroupEntry { binding: 3, resource: wgpu::BindingResource::TextureView(&field_tex.create_view(&Default::default())) },
                wgpu::BindGroupEntry { binding: 4, resource: wgpu::BindingResource::Sampler(&near_s) },
                wgpu::BindGroupEntry { binding: 5, resource: wgpu::BindingResource::TextureView(&data_tex.create_view(&Default::default())) },
            ],
        });
        let module = device.create_shader_module(wgpu::ShaderModuleDescriptor { label: Some("draw"), source: wgpu::ShaderSource::Wgsl(include_str!("draw.wgsl").into()) });
        let pl = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor { label: None, bind_group_layouts: &[Some(&layout)], immediate_size: 0 });
        let premul = wgpu::BlendState {
            color: wgpu::BlendComponent { src_factor: wgpu::BlendFactor::One, dst_factor: wgpu::BlendFactor::OneMinusSrcAlpha, operation: wgpu::BlendOperation::Add },
            alpha: wgpu::BlendComponent { src_factor: wgpu::BlendFactor::One, dst_factor: wgpu::BlendFactor::OneMinusSrcAlpha, operation: wgpu::BlendOperation::Add },
        };
        let mk = |vs: &str, fs: &str, buffers: &[Option<wgpu::VertexBufferLayout>]| {
            device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
                label: Some(fs),
                layout: Some(&pl),
                vertex: wgpu::VertexState { module: &module, entry_point: Some(vs), compilation_options: Default::default(), buffers },
                primitive: wgpu::PrimitiveState::default(),
                depth_stencil: None,
                multisample: wgpu::MultisampleState::default(),
                fragment: Some(wgpu::FragmentState {
                    module: &module,
                    entry_point: Some(fs),
                    compilation_options: Default::default(),
                    targets: &[Some(wgpu::ColorTargetState { format: config.format, blend: Some(premul), write_mask: wgpu::ColorWrites::ALL })],
                }),
                multiview_mask: None,
                cache: None,
            })
        };
        let rect_layout = wgpu::VertexBufferLayout {
            array_stride: std::mem::size_of::<Rect>() as u64,
            step_mode: wgpu::VertexStepMode::Instance,
            attributes: &wgpu::vertex_attr_array![0 => Float32x2, 1 => Float32x2, 2 => Float32x4],
        };
        let glyph_layout = wgpu::VertexBufferLayout {
            array_stride: std::mem::size_of::<Glyph>() as u64,
            step_mode: wgpu::VertexStepMode::Instance,
            attributes: &wgpu::vertex_attr_array![0 => Float32x2, 1 => Float32x2, 2 => Float32x4, 3 => Float32x4],
        };
        let rect_pipe = mk("vs_rect", "fs_rect", &[Some(rect_layout)]);
        let image_pipe = mk("vs_image", "fs_image", &[]);
        let glyph_pipe = mk("vs_glyph", "fs_glyph", &[Some(glyph_layout)]);
        let logo_pipe = mk("vs_logo", "fs_logo", &[]);
        let quad_layout = wgpu::VertexBufferLayout {
            array_stride: std::mem::size_of::<DataQuad>() as u64,
            step_mode: wgpu::VertexStepMode::Instance,
            attributes: &wgpu::vertex_attr_array![0 => Float32x4, 1 => Float32x4, 2 => Float32x4, 3 => Float32x4],
        };
        let data_pipe = mk("vs_data", "fs_data", &[Some(quad_layout)]);
        let buf = |n: usize| {
            device.create_buffer(&wgpu::BufferDescriptor { label: None, size: n as u64, usage: wgpu::BufferUsages::VERTEX | wgpu::BufferUsages::COPY_DST, mapped_at_creation: false })
        };
        let rect_buf = buf(MAX_RECTS * std::mem::size_of::<Rect>());
        let glyph_buf = buf(MAX_GLYPHS * std::mem::size_of::<Glyph>());
        let quad_buf = buf(16 * std::mem::size_of::<DataQuad>());
        let atlas = (atlas.cell.0 as f32, atlas.cell.1 as f32, atlas.cols as f32, aw as f32, ah as f32, atlas.adv, atlas.line);
        Gpu { window, surface, device, queue, config, ubuf, bind, rect_pipe, image_pipe, glyph_pipe, logo_pipe, rect_buf, glyph_buf, atlas, data_pipe, quad_buf, field_tex, field_ready: false }
    }

    fn resize(&mut self, w: u32, h: u32) {
        if w > 0 && h > 0 {
            self.config.width = w;
            self.config.height = h;
            self.surface.configure(&self.device, &self.config);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn render(&mut self, view: usize, t: f32, tr: Option<f32>, live: &Live, built: usize, address_shown: bool, fps: f32, title: Option<f32>) -> Vec<([f32; 4], Hot)> {
        if !self.field_ready {
            if let Some(set) = &live.set {
                self.queue.write_texture(
                    wgpu::TexelCopyTextureInfo { texture: &self.field_tex, mip_level: 0, origin: wgpu::Origin3d::ZERO, aspect: wgpu::TextureAspect::All },
                    &set.field,
                    wgpu::TexelCopyBufferLayout { offset: 0, bytes_per_row: Some(FIELD_W as u32), rows_per_image: Some(FIELD_H as u32) },
                    wgpu::Extent3d { width: FIELD_W as u32, height: FIELD_H as u32, depth_or_array_layers: 1 },
                );
                self.field_ready = true;
            }
        }
        let frame = match self.surface.get_current_texture() {
            wgpu::CurrentSurfaceTexture::Success(f) | wgpu::CurrentSurfaceTexture::Suboptimal(f) => f,
            wgpu::CurrentSurfaceTexture::Outdated | wgpu::CurrentSurfaceTexture::Lost => {
                self.surface.configure(&self.device, &self.config);
                return Vec::new();
            }
            _ => return Vec::new(),
        };
        let (w, h) = (self.config.width as f32, self.config.height as f32);
        let l = layout(w, h, self.window.scale_factor() as f32);
        let a = self.atlas;
        let mut f = Frame { rects: Vec::with_capacity(16_384), glyphs: Vec::with_capacity(512), adv: a.5, line: a.6, image: None, quads: Vec::new(), logo: None, hot: Vec::new() };
        match (title, view) {
            (Some(tt), _) => scene_title(&mut f, &l, tt),
            (None, pipeline::ADDRESS) => {
                if let (Some(a), Some(tr)) = (&live.addr, tr) {
                    scene_address(&mut f, &l, tr * PACE, a);
                }
            }
            (None, pipeline::SET) => match (&live.set, tr) {
                (Some(s), Some(tr)) => scene_set(&mut f, &l, tr * PACE, s),
                _ => scene_set_build(&mut f, &l, t, built),
            },
            (None, pipeline::SEND) => scene_spend(&mut f, &l, t, live),
            (None, pipeline::MINING) => scene_mining(&mut f, &l, t, live),
            (None, pipeline::REPORT) => {
                if let (Some(r), Some(tr)) = (&live.report, tr) {
                    scene_report(&mut f, &l, tr, live, r);
                }
            }
            (None, pipeline::SCAN) => {
                if let (Some(s), Some(tr)) = (&live.scan, tr) {
                    scene_scan(&mut f, &l, tr * PACE, s);
                }
            }
            _ => {
                if let Some(b) = &live.block {
                    scene_block(&mut f, &l, t, tr.map(|x| x * PACE), b);
                }
            }
        }
        if title.is_none() {
            let results = results(live, address_shown);
            overlay(&mut f, &l, view, &results, fps);
        }
        let logo = (30.0 * l.s).round();
        let m = (24.0 * l.s).round();
        let logo_u = f.logo.map_or([w - m - logo, h - m - logo, logo, 0.0], |g| [g[0], g[1], g[2], 0.0]);
        let (img, uvr, tint) = f.image.unwrap_or(([0.0; 4], [0.0; 4], 0.0));
        let wc = white(1.0);
        let u = U {
            res: [w, h, a.3, a.4],
            atlas: [a.0, a.1, a.2, 0.0],
            img,
            uvr,
            logo: logo_u,
            tint: [wc[0], wc[1], wc[2], tint],
        };
        self.queue.write_buffer(&self.ubuf, 0, bytemuck::bytes_of(&u));
        if !f.rects.is_empty() {
            self.queue.write_buffer(&self.rect_buf, 0, bytemuck::cast_slice(&f.rects));
        }
        if !f.quads.is_empty() {
            self.queue.write_buffer(&self.quad_buf, 0, bytemuck::cast_slice(&f.quads));
        }
        if !f.glyphs.is_empty() {
            self.queue.write_buffer(&self.glyph_buf, 0, bytemuck::cast_slice(&f.glyphs));
        }
        let view = frame.texture.create_view(&Default::default());
        let mut enc = self.device.create_command_encoder(&Default::default());
        {
            let mut p = enc.begin_render_pass(&wgpu::RenderPassDescriptor {
                label: None,
                color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                    view: &view,
                    depth_slice: None,
                    resolve_target: None,
                    ops: wgpu::Operations { load: wgpu::LoadOp::Clear(wgpu::Color::BLACK), store: wgpu::StoreOp::Store },
                })],
                depth_stencil_attachment: None,
                timestamp_writes: None,
                occlusion_query_set: None,
                multiview_mask: None,
            });
            p.set_bind_group(0, &self.bind, &[]);
            if tint > 0.0 {
                p.set_pipeline(&self.image_pipe);
                p.draw(0..6, 0..1);
            }
            if !f.quads.is_empty() {
                p.set_pipeline(&self.data_pipe);
                p.set_vertex_buffer(0, self.quad_buf.slice(..));
                p.draw(0..6, 0..f.quads.len() as u32);
            }
            if !f.rects.is_empty() {
                p.set_pipeline(&self.rect_pipe);
                p.set_vertex_buffer(0, self.rect_buf.slice(..));
                p.draw(0..6, 0..f.rects.len() as u32);
            }
            if !f.glyphs.is_empty() {
                p.set_pipeline(&self.glyph_pipe);
                p.set_vertex_buffer(0, self.glyph_buf.slice(..));
                p.draw(0..6, 0..f.glyphs.len() as u32);
            }
            p.set_pipeline(&self.logo_pipe);
            p.draw(0..6, 0..1);
        }
        self.queue.submit([enc.finish()]);
        self.queue.present(frame);
        f.hot
    }
}

struct App {
    shared: Arc<Shared>,
    gpu: Option<Gpu>,
    step: usize,
    view: usize,
    view_start: Instant,
    ready_at: [Option<Instant>; LIVE_STEPS],
    address_shown: bool,
    report_opened: bool,
    title: bool,
    hot: Vec<([f32; 4], Hot)>,
    cursor: (f32, f32),
    last: Instant,
    fps: f32,
}

fn open_external(target: &str, reveal: bool) {
    let _ = if cfg!(target_os = "macos") {
        std::process::Command::new("open").args(if reveal { vec!["-R", target] } else { vec![target] }).spawn()
    } else if cfg!(windows) {
        if reveal {
            std::process::Command::new("explorer").arg(format!("/select,{target}")).spawn()
        } else {
            std::process::Command::new("cmd").args(["/C", "start", "", target]).spawn()
        }
    } else {
        let t = if reveal { std::path::Path::new(target).parent().map_or(target.to_string(), |p| p.display().to_string()) } else { target.to_string() };
        std::process::Command::new("xdg-open").arg(t).spawn()
    };
}

impl App {
    fn hit(&self) -> Option<Hot> {
        let (x, y) = self.cursor;
        self.hot.iter().find(|(r, _)| x >= r[0] && x <= r[0] + r[2] && y >= r[1] && y <= r[1] + r[3]).map(|h| h.1)
    }

    fn end_title(&mut self) {
        self.title = false;
        self.view_start = Instant::now();
        pipeline::allow(&self.shared, pipeline::ADDRESS);
    }

    fn frame(&mut self) {
        let now = Instant::now();
        let dt = now.duration_since(self.last).as_secs_f32().max(1e-5);
        self.last = now;
        self.fps = self.fps * 0.95 + (1.0 / dt) * 0.05;
        let shared = self.shared.clone();
        let live: MutexGuard<Live> = shared.live.lock().unwrap();
        for (s, at) in self.ready_at.iter_mut().enumerate() {
            if at.is_none() && live.done(s) {
                *at = Some(now);
            }
        }
        let t = now.duration_since(self.view_start).as_secs_f32();
        if self.title {
            if let Some(g) = &mut self.gpu {
                self.hot = g.render(0, 0.0, None, &live, 0, false, self.fps, Some(t));
            }
            return;
        }
        let tr = self.ready_at[self.view].map(|r| now.duration_since(r.max(self.view_start)).as_secs_f32());
        if self.view == pipeline::ADDRESS && tr.is_some_and(|x| x * PACE >= 7.9) {
            self.address_shown = true;
        }
        if self.view == pipeline::REPORT && !self.report_opened && tr.is_some_and(|x| x >= OPEN_REPORT_AFTER) {
            self.report_opened = true;
            if let Some(r) = live.report.as_ref().filter(|r| !r.path.is_empty()) {
                let opener = if cfg!(target_os = "macos") {
                    ("open", vec!["-t", r.path.as_str()])
                } else if cfg!(windows) {
                    ("notepad", vec![r.path.as_str()])
                } else {
                    ("xdg-open", vec![r.path.as_str()])
                };
                let _ = std::process::Command::new(opener.0).args(opener.1).spawn();
                open_external(&r.path, true);
            }
        }
        let advance = self.view == self.step && self.step + 1 < LIVE_STEPS && tr.is_some_and(|x| x >= HOLD[self.step]);
        let built = shared.set_built.load(std::sync::atomic::Ordering::Relaxed);
        if let Some(g) = &mut self.gpu {
            self.hot = g.render(self.view, t, tr, &live, built, self.address_shown, self.fps, None);
        }
        drop(live);
        if advance {
            self.step += 1;
            self.view = self.step;
            self.view_start = now;
            pipeline::allow(&shared, self.step);
        }
    }
}

impl ApplicationHandler for App {
    fn resumed(&mut self, event_loop: &ActiveEventLoop) {
        if self.gpu.is_some() {
            return;
        }
        let attrs = Window::default_attributes().with_title("Blocknet Bench 3").with_inner_size(LogicalSize::new(1280.0, 720.0)).with_fullscreen(None);
        let window = Arc::new(event_loop.create_window(attrs).expect("window"));
        self.gpu = Some(Gpu::new(window));
        self.view_start = Instant::now();
    }

    fn window_event(&mut self, event_loop: &ActiveEventLoop, _id: WindowId, event: WindowEvent) {
        match event {
            WindowEvent::CloseRequested => event_loop.exit(),
            WindowEvent::Resized(s) => {
                if let Some(g) = &mut self.gpu {
                    g.resize(s.width, s.height);
                }
            }
            WindowEvent::KeyboardInput { event: KeyEvent { logical_key, state: ElementState::Pressed, .. }, .. } => match logical_key {
                Key::Named(NamedKey::Escape) => event_loop.exit(),
                Key::Named(NamedKey::ArrowRight) | Key::Named(NamedKey::Enter) if self.title => self.end_title(),
                Key::Named(NamedKey::ArrowRight) if self.view == self.step && self.ready_at[self.step].is_some() && self.step + 1 < LIVE_STEPS => {
                    self.step += 1;
                    self.view = self.step;
                    self.view_start = Instant::now();
                    pipeline::allow(&self.shared, self.step);
                }
                Key::Named(NamedKey::ArrowRight) | Key::Named(NamedKey::ArrowLeft) => {
                    let n = self.step + 1;
                    self.view = if matches!(logical_key, Key::Named(NamedKey::ArrowRight)) { (self.view + 1) % n } else { (self.view + n - 1) % n };
                    self.view_start = Instant::now();
                }
                Key::Character(c) if c.as_str() == "q" => event_loop.exit(),
                Key::Character(c) if c.as_str() == "l" => text::set_zh(!zh()),
                Key::Character(c) if c.as_str() == "r" => self.view_start = Instant::now(),
                Key::Character(c) if c.as_str() == "f" => {
                    if let Some(g) = &self.gpu {
                        let full = g.window.fullscreen().is_some();
                        g.window.set_fullscreen(if full { None } else { Some(Fullscreen::Borderless(None)) });
                    }
                }
                _ => {}
            },
            WindowEvent::RedrawRequested => self.frame(),
            WindowEvent::CursorMoved { position, .. } => {
                self.cursor = (position.x as f32, position.y as f32);
                let over = self.hit().is_some();
                if let Some(g) = &self.gpu {
                    g.window.set_cursor(if over { winit::window::CursorIcon::Pointer } else { winit::window::CursorIcon::Default });
                }
            }
            WindowEvent::MouseInput { state: ElementState::Pressed, button: winit::event::MouseButton::Left, .. } => match self.hit() {
                Some(Hot::Share) => open_external(&format!("https://{SHARE_URL}"), false),
                Some(Hot::Lang(z)) => text::set_zh(z),
                Some(Hot::Start) if self.title => self.end_title(),
                Some(Hot::Start) => {}
                None => {}
            },
            _ => {}
        }
    }

    fn about_to_wait(&mut self, _event_loop: &ActiveEventLoop) {
        if let Some(g) = &self.gpu {
            g.window.request_redraw();
        }
    }
}

fn main() {
    text::set_zh(text::detect());
    let shared = pipeline::start();
    let event_loop = EventLoop::new().expect("event loop");
    event_loop.set_control_flow(ControlFlow::Poll);
    let now = Instant::now();
    let mut app = App { shared, gpu: None, step: 0, view: 0, view_start: now, ready_at: [None; LIVE_STEPS], address_shown: false, report_opened: false, title: true, hot: Vec::new(), cursor: (0.0, 0.0), last: now, fps: 60.0 };
    event_loop.run_app(&mut app).expect("run");
}
