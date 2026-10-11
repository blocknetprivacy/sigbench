#![allow(dead_code)]

use std::io::{self, Read, Write};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};

pub const FPS: u64 = 30;
pub static QUIT: AtomicBool = AtomicBool::new(false);
pub static KEY: AtomicU8 = AtomicU8::new(0);

#[derive(Clone, Copy, Default, PartialEq)]
pub struct Rgb(pub f32, pub f32, pub f32);

impl Rgb {
    pub fn add(self, o: Rgb) -> Rgb {
        Rgb(self.0 + o.0, self.1 + o.1, self.2 + o.2)
    }
    pub fn scale(self, k: f32) -> Rgb {
        Rgb(self.0 * k, self.1 * k, self.2 * k)
    }
    pub fn lerp(self, o: Rgb, t: f32) -> Rgb {
        let t = t.clamp(0.0, 1.0);
        Rgb(self.0 + (o.0 - self.0) * t, self.1 + (o.1 - self.1) * t, self.2 + (o.2 - self.2) * t)
    }
    pub fn lum(self) -> f32 {
        self.0 + self.1 + self.2
    }
    pub fn bytes(self) -> (u8, u8, u8) {
        let c = |v: f32| (v.clamp(0.0, 1.0).powf(1.0 / 2.2) * 255.0) as u8;
        (c(self.0), c(self.1), c(self.2))
    }
}

pub fn hex(h: u32) -> Rgb {
    let f = |s: u32| ((h >> s) & 0xff) as f32 / 255.0;
    Rgb(f(16).powf(2.2), f(8).powf(2.2), f(0).powf(2.2))
}

pub fn ease(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    t * t * (3.0 - 2.0 * t)
}

pub fn mix64(mut x: u64) -> u64 {
    x ^= x >> 33;
    x = x.wrapping_mul(0xff51_afd7_ed55_8ccd);
    x ^= x >> 33;
    x = x.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    x ^ (x >> 33)
}

pub fn noise(x: usize, y: usize) -> f32 {
    (mix64((x as u64) << 32 | y as u64) >> 40) as f32 / (1u64 << 24) as f32
}

pub struct Rand(pub u64);
impl Rand {
    pub fn next(&mut self) -> f32 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 >> 40) as f32 / (1u64 << 24) as f32
    }
}

pub struct Canvas {
    pub w: usize,
    pub h: usize,
    pub px: Vec<Rgb>,
}

impl Canvas {
    pub fn new(w: usize, h: usize, bg: Rgb) -> Self {
        Canvas { w, h, px: vec![bg; w * h] }
    }
    pub fn add(&mut self, x: i32, y: i32, c: Rgb) {
        if x >= 0 && y >= 0 && (x as usize) < self.w && (y as usize) < self.h {
            let p = &mut self.px[y as usize * self.w + x as usize];
            *p = p.add(c);
        }
    }
    pub fn set(&mut self, x: i32, y: i32, c: Rgb) {
        if x >= 0 && y >= 0 && (x as usize) < self.w && (y as usize) < self.h {
            self.px[y as usize * self.w + x as usize] = c;
        }
    }
    pub fn glow(&mut self, x: f32, y: f32, r: f32, c: Rgb) {
        let reach = r * 2.2;
        for yy in (y - reach) as i32..=(y + reach) as i32 + 1 {
            for xx in (x - reach) as i32..=(x + reach) as i32 + 1 {
                let d2 = ((xx as f32 - x).powi(2) + (yy as f32 - y).powi(2)) / (r * r);
                if d2 < 5.0 {
                    self.add(xx, yy, c.scale((-d2).exp()));
                }
            }
        }
    }
    pub fn line(&mut self, a: (f32, f32), b: (f32, f32), c: Rgb) {
        let n = ((b.0 - a.0).abs().max((b.1 - a.1).abs()) as usize).max(1);
        for i in 0..=n {
            let t = i as f32 / n as f32;
            self.add((a.0 + (b.0 - a.0) * t) as i32, (a.1 + (b.1 - a.1) * t) as i32, c);
        }
    }
}

pub struct Dots {
    pub w: usize,
    pub h: usize,
    pub on: Vec<Option<Rgb>>,
}

impl Dots {
    pub fn new(w: usize, h: usize) -> Self {
        Dots { w, h, on: vec![None; w * h] }
    }
    pub fn set(&mut self, x: i32, y: i32, c: Rgb) {
        if x >= 0 && y >= 0 && (x as usize) < self.w && (y as usize) < self.h {
            let p = &mut self.on[y as usize * self.w + x as usize];
            if p.map_or(true, |o| c.lum() > o.lum()) {
                *p = Some(c);
            }
        }
    }
}

#[derive(Clone, Copy)]
pub struct Cell {
    pub ch: char,
    pub fg: Rgb,
    pub bg: Rgb,
}

pub struct Grid {
    pub w: usize,
    pub h: usize,
    pub c: Vec<Cell>,
}

impl Grid {
    pub fn new(w: usize, h: usize, bg: Rgb) -> Self {
        Grid { w, h, c: vec![Cell { ch: ' ', fg: bg, bg }; w * h] }
    }
    pub fn from_canvas(cv: &Canvas, rows: usize) -> Self {
        let mut g = Grid::new(cv.w, rows, Rgb::default());
        for y in 0..rows {
            for x in 0..cv.w {
                let top = cv.px[(2 * y).min(cv.h - 1) * cv.w + x];
                let bot = cv.px[(2 * y + 1).min(cv.h - 1) * cv.w + x];
                g.c[y * cv.w + x] = Cell { ch: '▀', fg: top, bg: bot };
            }
        }
        g
    }
    pub fn from_dots(d: &Dots, rows: usize, back: Rgb) -> Self {
        const BIT: [[u32; 2]; 4] = [[0x01, 0x08], [0x02, 0x10], [0x04, 0x20], [0x40, 0x80]];
        let cols = d.w / 2;
        let mut g = Grid::new(cols, rows, back);
        for y in 0..rows {
            for x in 0..cols {
                let (mut mask, mut col, mut n) = (0u32, Rgb::default(), 0.0);
                for (dy, bits) in BIT.iter().enumerate() {
                    for (dx, bit) in bits.iter().enumerate() {
                        if let Some(c) = d.on[(y * 4 + dy) * d.w + x * 2 + dx] {
                            mask |= bit;
                            col = col.add(c);
                            n += 1.0;
                        }
                    }
                }
                if mask != 0 {
                    g.c[y * cols + x] = Cell { ch: char::from_u32(0x2800 + mask).unwrap(), fg: col.scale(1.0 / n), bg: back };
                }
            }
        }
        g
    }
    pub fn get(&mut self, x: usize, y: usize) -> Option<&mut Cell> {
        if x < self.w && y < self.h {
            Some(&mut self.c[y * self.w + x])
        } else {
            None
        }
    }
    pub fn scale(&mut self, k: f32) {
        for c in self.c.iter_mut() {
            c.fg = c.fg.scale(k);
            c.bg = c.bg.scale(k);
        }
    }
    pub fn text(&mut self, x: usize, y: usize, s: &str, fg: Rgb) {
        for (i, ch) in s.chars().enumerate() {
            if let Some(c) = self.get(x + i, y) {
                if c.ch == '▀' {
                    c.bg = c.fg.lerp(c.bg, 0.5);
                }
                c.ch = ch;
                c.fg = fg;
            }
        }
    }
    pub fn panel(&mut self, x0: usize, y0: usize, w: usize, h: usize, border: Rgb, title: &str, title_fg: Rgb) {
        let tint = hex(0x070a12);
        for y in y0..y0 + h {
            for x in x0..x0 + w {
                if let Some(c) = self.get(x, y) {
                    let under = if c.ch == '▀' { c.fg.lerp(c.bg, 0.5) } else { c.bg.lerp(c.fg, 0.3) };
                    c.bg = tint.lerp(under, 0.04);
                    c.fg = c.bg;
                    c.ch = ' ';
                }
            }
        }
        if w < 4 || h < 2 {
            return;
        }
        for x in x0..x0 + w {
            for y in [y0, y0 + h - 1] {
                if let Some(c) = self.get(x, y) {
                    c.ch = '─';
                    c.fg = border;
                }
            }
        }
        for y in y0..y0 + h {
            for x in [x0, x0 + w - 1] {
                if let Some(c) = self.get(x, y) {
                    c.ch = '│';
                    c.fg = border;
                }
            }
        }
        for (x, y, ch) in [(x0, y0, '╭'), (x0 + w - 1, y0, '╮'), (x0, y0 + h - 1, '╰'), (x0 + w - 1, y0 + h - 1, '╯')] {
            if let Some(c) = self.get(x, y) {
                c.ch = ch;
                c.fg = border;
            }
        }
        if !title.is_empty() {
            self.text(x0 + 2, y0, &format!(" {title} "), title_fg);
        }
    }
    pub fn bar(&mut self, x: usize, y: usize, w: usize, p: f32, on: Rgb, off: Rgb) {
        let fill = p.clamp(0.0, 1.0) * w as f32;
        for i in 0..w {
            if let Some(c) = self.get(x + i, y) {
                let f = (fill - i as f32).clamp(0.0, 1.0);
                c.ch = if f > 0.0 && f < 1.0 { '╸' } else { '━' };
                c.fg = if f > 0.0 { on } else { off };
            }
        }
    }
}

pub fn dissolve(a: Grid, b: Grid, p: f32) -> Grid {
    let mut out = b;
    let seam = hex(0xbffcf0);
    for y in 0..out.h.min(a.h) {
        for x in 0..out.w.min(a.w) {
            let n = noise(x, y);
            let i = y * out.w + x;
            if n > p {
                out.c[i] = a.c[y * a.w + x];
            } else if p - n < 0.06 {
                let c = &mut out.c[i];
                c.fg = c.fg.lerp(seam, 0.6);
                c.bg = c.bg.lerp(seam, 0.25);
            }
        }
    }
    out
}

pub struct Term {
    pub saved: String,
}

impl Term {
    pub fn stty(args: &[&str]) -> String {
        Command::new("stty")
            .args(args)
            .stdin(Stdio::inherit())
            .output()
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
            .unwrap_or_default()
    }
    pub fn open() -> Term {
        let saved = Term::stty(&["-g"]);
        Term::stty(&["raw", "-echo"]);
        print!("\x1b[?1049h\x1b[?25l\x1b[?7l\x1b[2J");
        let _ = io::stdout().flush();
        std::thread::spawn(|| {
            let mut b = [0u8; 16];
            let mut stdin = io::stdin();
            while let Ok(n) = stdin.read(&mut b) {
                if let Some(&k) = b[..n].last() {
                    KEY.store(k, Ordering::SeqCst);
                }
                if n == 0 || b[..n].iter().any(|&k| k == b'q' || k == b'Q' || k == 3 || k == 4) {
                    QUIT.store(true, Ordering::SeqCst);
                    break;
                }
            }
        });
        Term { saved }
    }
    pub fn size() -> (usize, usize) {
        let s = Term::stty(&["size"]);
        let v: Vec<usize> = s.split_whitespace().filter_map(|x| x.parse().ok()).collect();
        if v.len() == 2 && v[0] > 0 && v[1] > 0 {
            (v[1], v[0])
        } else {
            (100, 30)
        }
    }
}

impl Drop for Term {
    fn drop(&mut self) {
        print!("\x1b[0m\x1b[?7h\x1b[?25h\x1b[?1049l");
        let _ = io::stdout().flush();
        if !self.saved.is_empty() {
            Term::stty(&[&self.saved]);
        } else {
            Term::stty(&["sane"]);
        }
    }
}

pub fn emit(g: &Grid, out: &mut String) {
    out.clear();
    let mut last: Option<((u8, u8, u8), (u8, u8, u8))> = None;
    for y in 0..g.h {
        out.push_str(&format!("\x1b[{};1H", y + 1));
        for x in 0..g.w {
            let c = g.c[y * g.w + x];
            let key = (c.fg.bytes(), c.bg.bytes());
            if last != Some(key) {
                let ((fr, fg, fb), (br, bg, bb)) = key;
                out.push_str(&format!("\x1b[38;2;{fr};{fg};{fb};48;2;{br};{bg};{bb}m"));
                last = Some(key);
            }
            out.push(c.ch);
        }
    }
    out.push_str("\x1b[0m");
    let mut so = io::stdout().lock();
    let _ = so.write_all(out.as_bytes());
    let _ = so.flush();
}

pub const BLOCKNET_GREEN: u32 = 0xaaff00;

fn capsule(px: f32, py: f32, a: (f32, f32), b: (f32, f32), r: f32) -> f32 {
    let (dx, dy) = (b.0 - a.0, b.1 - a.1);
    let h = (((px - a.0) * dx + (py - a.1) * dy) / (dx * dx + dy * dy)).clamp(0.0, 1.0);
    ((px - a.0 - dx * h).powi(2) + (py - a.1 - dy * h).powi(2)).sqrt() - r
}

fn logo_sdf(u: f32, v: f32) -> f32 {
    let flat = capsule(u, v, (247.0, 832.0), (831.0, 832.0), 121.0);
    let tilted = capsule(u, v, (539.0, 246.0), (832.0, 540.0), 121.0);
    flat.min(tilted)
}

pub fn draw_logo(g: &mut Grid, cx: f32, cy: f32, size: f32, alpha: f32, glow: f32) {
    if alpha <= 0.0 || size < 4.0 {
        return;
    }
    let green = hex(BLOCKNET_GREEN);
    let k = 1080.0 / size;
    let to_logo = |px: f32, py: f32| (539.0 + (px - cx) * k, 539.0 + (py - cy) * k);
    let reach = size * 0.75;
    let (x0, x1) = ((cx - reach).max(0.0) as usize, ((cx + reach) as usize).min(g.w));
    let (y0, y1) = (((cy - reach) / 2.0).max(0.0) as usize, (((cy + reach) / 2.0) as usize + 1).min(g.h));
    const SUB: [(f32, f32); 4] = [(0.25, 0.25), (0.75, 0.25), (0.25, 0.75), (0.75, 0.75)];
    for row in y0..y1 {
        for col in x0..x1 {
            let mut cover = [0.0f32; 2];
            let mut near = f32::MAX;
            for (half, c) in cover.iter_mut().enumerate() {
                for (sx, sy) in SUB {
                    let (u, v) = to_logo(col as f32 + sx, (2 * row + half) as f32 + sy);
                    let d = logo_sdf(u, v);
                    near = near.min(d);
                    if d <= 0.0 {
                        *c += 0.25;
                    }
                }
            }
            let cell = &mut g.c[row * g.w + col];
            let d = near.max(0.0) / k / size;
            let halo = green.scale(glow * ((-d / 0.06).exp() - (-0.3f32 / 0.06).exp()).max(0.0) * 0.35);
            if cover[0] + cover[1] > 0.0 {
                let under = if cell.ch == '▀' { (cell.fg, cell.bg) } else { (cell.bg, cell.bg) };
                let top = under.0.add(halo).lerp(green, cover[0] * alpha);
                let bot = under.1.add(halo).lerp(green, cover[1] * alpha);
                *cell = Cell { ch: '▀', fg: top, bg: bot };
            } else {
                cell.bg = cell.bg.add(halo.scale(alpha));
            }
        }
    }
}
