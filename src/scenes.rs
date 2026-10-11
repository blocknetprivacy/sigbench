#![allow(dead_code)]

use crate::fx;
use crate::gfx::*;
use crate::machine::cmd;

pub const INK: u32 = 0xe8ecf4;
pub const DIM: u32 = 0x6b7590;
pub const ACCENT: u32 = BLOCKNET_GREEN;

pub fn glyph(ch: char) -> [u8; 5] {
    match ch {
        'F' => [0b11111, 0b10000, 0b11110, 0b10000, 0b10000],
        'A' => [0b01110, 0b10001, 0b11111, 0b10001, 0b10001],
        'R' => [0b11110, 0b10001, 0b11110, 0b10100, 0b10011],
        'D' => [0b11110, 0b10001, 0b10001, 0b10001, 0b11110],
        'Y' => [0b10001, 0b01010, 0b00100, 0b00100, 0b00100],
        _ => [0; 5],
    }
}

pub fn boot_bottom(w: usize, rows: usize, info_len: usize) -> usize {
    let scale = ((w as f32 / (7 * 6) as f32).floor() as usize).clamp(1, 3);
    let th = 5 * scale;
    let ph = rows * 2;
    let y0 = (ph.saturating_sub(th) / 2).saturating_sub(ph / 8);
    let below = (y0 + th) / 2 + 2;
    below + 3 + info_len
}

pub fn boot(w: usize, rows: usize, t: f32, lat: &mut LatticeState, info: &[(String, String)]) -> Grid {
    let _ = lat;
    let mut g = Grid::new(w, rows, Rgb::default());
    let word = "FARADAY";
    let scale = ((w as f32 / (word.len() * 6) as f32).floor() as usize).clamp(1, 3);
    let tw = word.len() * 6 * scale;
    let th = 5 * scale;
    let ph = rows * 2;
    let mut cv = Canvas::new(w, ph, Rgb::default());
    let x0 = w.saturating_sub(tw) / 2;
    let y0 = (ph.saturating_sub(th) / 2).saturating_sub(ph / 8);
    let sweep = (t - 1.6) * 0.9;
    for (li, ch) in word.chars().enumerate() {
        let rows5 = glyph(ch);
        let lock = 0.4 + li as f32 * 0.12;
        for gy in 0..5 {
            for gx in 0..5 {
                let on = rows5[gy] >> (4 - gx) & 1 == 1;
                let n = noise(li * 7 + gx, gy + 11);
                let reveal = ((t - lock) * 1.6 - n).clamp(0.0, 1.0);
                let spark = if reveal < 1.0 && t > lock - 0.3 && noise(gx + li * 5, gy + (t * 24.0) as usize) > 0.72 { 0.7 } else { 0.0 };
                let lit = if on { reveal } else { 0.0 } + spark * (1.0 - reveal);
                if lit <= 0.0 {
                    continue;
                }
                let px = x0 + (li * 6 + gx) * scale;
                let py = y0 + gy * scale;
                let fx = (px - x0) as f32 / tw.max(1) as f32;
                let band = (-((fx - sweep).powi(2)) * 40.0).exp();
                let col = hex(BLOCKNET_GREEN).lerp(hex(0x3dff6e), fx).scale(lit * (1.0 - 0.92 * band));
                for sy in 0..scale {
                    for sx in 0..scale {
                        cv.add((px + sx) as i32, (py + sy) as i32, col);
                    }
                }
            }
        }
    }
    let title = Grid::from_canvas(&cv, rows);
    for (i, c) in title.c.iter().enumerate() {
        if c.fg.lum() + c.bg.lum() > 0.02 {
            g.c[i] = *c;
        }
    }
    let cx = |s: &str| w.saturating_sub(s.chars().count()) / 2;
    let kicker = "B L O C K N E T";
    if t > 0.6 {
        let shown: String = kicker.chars().take(((t - 0.6) * 30.0) as usize).collect();
        g.text(cx(kicker), (y0 / 2).saturating_sub(2), &shown, hex(DIM));
    }
    let below = (y0 + th) / 2 + 2;
    let sub = "BENCH 2  ·  today's Blocknet vs. the Faraday fork, on this machine";
    if t > 2.0 {
        let shown: String = sub.chars().take(((t - 2.0) * 40.0) as usize).collect();
        g.text(cx(sub), below, &shown, hex(INK));
    }
    let lw = info.iter().map(|r| r.0.chars().count()).max().unwrap_or(0);
    let vw = info.iter().map(|r| r.1.chars().count()).max().unwrap_or(0);
    let bx = w.saturating_sub(lw + 3 + vw) / 2;
    if t > 2.8 {
        let rule = ease((t - 2.8) / 0.6);
        let n = ((lw + 3 + vw) as f32 * rule) as usize;
        g.text(bx, below + 2, &"─".repeat(n), hex(0x1f2a3a));
    }
    for (i, (label, value)) in info.iter().enumerate() {
        let start = 3.2 + i as f32 * 0.3;
        if t > start {
            let y = below + 3 + i;
            g.text(bx + lw - label.chars().count(), y, label, hex(DIM));
            let shown: String = value.chars().take(((t - start) * 70.0) as usize).collect();
            g.text(bx + lw + 3, y, &shown, hex(INK).lerp(hex(ACCENT), 0.25));
        }
    }
    g
}

pub fn ring(w: usize, rows: usize, t: f32) -> Grid {
    let h = rows * 2;
    let mut cv = Canvas::new(w, h, Rgb::default());
    let (cx, cy) = (w as f32 * 0.5, h as f32 * 0.5);
    for y in 0..h {
        for x in 0..w {
            let dx = (x as f32 - cx) / w as f32;
            let dy = (y as f32 - cy) / h as f32;
            let r = (dx * dx + dy * dy).sqrt();
            cv.px[y * w + x] = hex(0x160d02).lerp(hex(0x020203), r * 2.2);
        }
    }
    let rx = (w as f32 * 0.36).min(h as f32 * 1.1);
    let ry = rx * 0.38;
    let spin = t * 0.22;
    let tau = std::f32::consts::TAU;
    let at = |a: f32| -> (f32, f32, f32) {
        let a = a + spin;
        (cx + rx * a.cos(), cy + ry * a.sin(), (a.sin() + 1.0) * 0.5)
    };
    let gold = hex(0xffc857);
    for i in 0..900 {
        let (x, y, depth) = at(i as f32 / 900.0 * tau);
        cv.add(x as i32, y as i32, gold.scale(0.05 + 0.12 * depth));
    }
    let lap = 0.9;
    let ph = (t / lap).fract();
    for k in 0..70 {
        let a = ph * tau - k as f32 * 0.032;
        let (x, y, depth) = at(a);
        let fade = (1.0 - k as f32 / 70.0).powi(2);
        cv.glow(x, y, 1.0 + 1.4 * fade, hex(0xfff1c2).lerp(hex(0xff7a29), k as f32 / 70.0).scale(fade * (0.6 + 0.6 * depth)));
    }
    for i in 0..16 {
        let a = i as f32 / 16.0 * tau;
        let (x, y, depth) = at(a);
        let passed = (ph * tau - a).rem_euclid(tau);
        let lit = (-passed * 1.8).exp();
        cv.glow(x, y, 1.6 + depth * 1.6, gold.scale(0.35 + 0.5 * depth + 1.6 * lit));
    }
    let since = ph * lap;
    let (x0, y0, _) = at(0.0);
    cv.glow(x0, y0, 3.0 + 10.0 * since, hex(0xffe3a3).scale(0.9 * (-since * 5.0).exp()));
    let ripple_r = since * rx * 0.9;
    for i in 0..480 {
        let a = i as f32 / 480.0 * tau;
        cv.add((x0 + ripple_r * a.cos()) as i32, (y0 + ripple_r * a.sin() * 0.45) as i32, hex(0xffcf7a).scale(0.55 * (-since * 3.0).exp()));
    }
    cv.glow(cx, cy, rx * 0.12, hex(0x3a2306).scale(0.5 + 0.2 * (t * 2.0).sin()));
    Grid::from_canvas(&cv, rows)
}

pub struct ShortVec {
    pub from: (i32, i32, i32),
    pub dir: (i32, i32, i32),
    pub born: f32,
    pub color: Rgb,
}

pub struct LatticeState {
    pub vecs: Vec<ShortVec>,
    pub rng: Rand,
    pub clock: f32,
}

pub fn lattice(w: usize, rows: usize, t: f32, st: &mut LatticeState) -> Grid {
    if (t - st.clock).abs() > 1.0 {
        st.vecs.clear();
    }
    st.clock = t;
    let mut d = Dots::new(w * 2, rows * 4);
    let (dw, dh) = (d.w as f32, d.h as f32);
    let (cx, cy) = (dw * 0.5, dh * 0.5);
    let (ya, xa) = (t * 0.32, 0.45 + 0.2 * (t * 0.27).sin());
    let (sy, cyw, sx, cxw) = (ya.sin(), ya.cos(), xa.sin(), xa.cos());
    let n = 4i32;
    let unit = dh.min(dw * 0.5) * 0.095;
    let project = |p: (f32, f32, f32)| -> (f32, f32, f32) {
        let (x, z) = (p.0 * cyw - p.2 * sy, p.0 * sy + p.2 * cyw);
        let (y, z) = (p.1 * cxw - z * sx, p.1 * sx + z * cxw);
        let k = 9.0 / (9.0 + z);
        (cx + x * unit * k * 2.0, cy + y * unit * k, z)
    };
    let (near, far) = (hex(0x9ff6ff), hex(0x172f73));
    for i in -n..=n {
        for j in -n..=n {
            for k in -n..=n {
                let (px, py, z) = project((i as f32, j as f32, k as f32));
                d.set(px as i32, py as i32, far.lerp(near, (4.5 - z) / 9.0));
            }
        }
    }
    const GROW: f32 = 0.6;
    const HOLD: f32 = 1.6;
    const FADE: f32 = 0.9;
    const LIVE: usize = 10;
    st.vecs.retain(|v| t - v.born < GROW + HOLD + FADE);
    let palette = [hex(0xff5fa2), hex(0xffb347), hex(0x7cf7d4), hex(0xc58bff), hex(0xff7a59)];
    while st.vecs.len() < LIVE {
        let rng = &mut st.rng;
        let dir = loop {
            let mut c = || (rng.next() * 3.0) as i32 - 1;
            let mut v = (c(), c(), c());
            if rng.next() < 0.2 {
                v.0 *= 2;
            }
            if v != (0, 0, 0) {
                break v;
            }
        };
        let inside = |a: i32, b: i32| (-n..=n).contains(&a) && (-n..=n).contains(&(a + b));
        let from = loop {
            let mut pick = || (rng.next() * (2 * n + 1) as f32) as i32 - n;
            let f = (pick(), pick(), pick());
            if inside(f.0, dir.0) && inside(f.1, dir.1) && inside(f.2, dir.2) {
                break f;
            }
        };
        let born = t - rng.next() * (GROW + HOLD) * if st.vecs.is_empty() { 1.0 } else { 0.0 };
        let color = palette[(rng.next() * 5.0) as usize % 5];
        st.vecs.push(ShortVec { from, dir, born, color });
    }
    for v in st.vecs.iter() {
        let age = t - v.born;
        let grow = ease(age / GROW);
        let alpha = if age < GROW + HOLD { 1.0 } else { 1.0 - ease((age - GROW - HOLD) / FADE) };
        let col = v.color.scale(alpha * (0.75 + 0.25 * (age * 6.0).sin()));
        let a = (v.from.0 as f32, v.from.1 as f32, v.from.2 as f32);
        let b = (a.0 + v.dir.0 as f32 * grow, a.1 + v.dir.1 as f32 * grow, a.2 + v.dir.2 as f32 * grow);
        let (o, e) = (project(a), project(b));
        for s in 0..=80 {
            let f = s as f32 / 80.0;
            d.set((o.0 + (e.0 - o.0) * f) as i32, (o.1 + (e.1 - o.1) * f) as i32, col);
        }
        for p in [o, e] {
            for (dx, dy) in [(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1)] {
                d.set(p.0 as i32 + dx, p.1 as i32 + dy, col);
            }
        }
    }
    Grid::from_dots(&d, rows, hex(0x03050c))
}

pub fn column(cv: &mut Canvas, sx: f32, sy: f32, tw: f32, th: f32, h: f32, top: Rgb) {
    let (x0, x1) = ((sx - tw).floor() as i32, (sx + tw).ceil() as i32);
    let (y0, y1) = ((sy - h - th).floor() as i32, (sy + th).ceil() as i32);
    for py in y0..=y1 {
        for px in x0..=x1 {
            let dx = (px as f32 + 0.5 - sx) / tw;
            if dx.abs() > 1.0 {
                continue;
            }
            let dy = py as f32 + 0.5 - sy;
            let span = th * (1.0 - dx.abs());
            if dy > span || dy < -h - span {
                continue;
            }
            let face = dx.abs() + (dy + h).abs() / th;
            let c = if face <= 1.0 {
                if face > 0.78 { top.scale(1.3) } else { top }
            } else {
                let down = 1.0 - 0.45 * ((dy + h) / (h + th)).clamp(0.0, 1.0);
                top.scale(if dx < 0.0 { 0.55 } else { 0.3 } * down)
            };
            cv.set(px, py, c);
        }
    }
}

pub fn memory(w: usize, rows: usize, t: f32, n: usize, per_hash: f32, base: Rgb, hot: Rgb) -> Grid {
    let ph = rows * 2;
    let (fw, fh) = (w as f32, ph as f32);
    let mut cv = Canvas::new(w, ph, Rgb::default());
    for y in 0..ph {
        for x in 0..w {
            let r = (((x as f32 - fw * 0.5) / fw).powi(2) + ((y as f32 - fh * 0.6) / fh).powi(2)).sqrt();
            cv.px[y * w + x] = base.scale(0.09).lerp(hex(0x020306), r * 2.0);
        }
    }
    let tw = (fw * 0.84 / (2.0 * n as f32)).min(fh * 0.6 / n as f32);
    let th = tw * 0.5;
    let max_h = fh * 0.3;
    let ox = fw * 0.5;
    let oy = (fh - n as f32 * tw - max_h) * 0.5 + max_h + th;
    let total = n * n;
    let hash = (t / per_hash) as u64;
    let k = (t / per_hash).fract() * total as f32;
    let kk = (k as usize).min(total - 1);
    let since = (t / per_hash).fract() * per_hash;
    let sink = 1.0 - ease(since / 0.35);
    let tall = |hsh: u64, j: usize| max_h * (0.15 + 0.85 * (mix64(hsh * 7_777 + j as u64) >> 40) as f32 / (1u64 << 24) as f32);
    let center = |j: usize| -> (f32, f32) {
        let (i, r) = ((j % n) as f32, (j / n) as f32);
        (ox + (i - r) * tw, oy + (i + r) * th)
    };
    let mut boost = vec![0.0f32; total];
    let mut arcs = Vec::new();
    for back in 0..6usize {
        if kk < back + 1 {
            break;
        }
        let j = kk - back;
        let r = (mix64(hash * 1_000_003 + j as u64) % j as u64) as usize;
        let fade = (1.0 - back as f32 / 6.0).powi(2);
        boost[r] = boost[r].max(fade);
        arcs.push((j, r, fade));
    }
    let mut height = vec![0.0f32; total];
    let mut color = vec![Rgb::default(); total];
    for j in 0..total {
        if (j as f32) < k {
            let age = k - j as f32;
            height[j] = tall(hash, j) * ease(age / (total as f32 * 0.03).max(2.0));
            let heat = (-age / (total as f32 * 0.06)).exp();
            color[j] = base.lerp(hot, heat * 0.85 + boost[j] * 0.7).add(hex(0xffffff).scale(boost[j] * 0.35));
        } else if hash > 0 && sink > 0.0 {
            height[j] = tall(hash - 1, j) * sink;
            color[j] = base.scale(0.6).add(hot.scale(0.4 * (1.0 - sink)));
        } else {
            color[j] = base.scale(0.13);
        }
    }
    let mut order: Vec<usize> = (0..total).collect();
    order.sort_by_key(|&j| j % n + j / n);
    for j in order {
        let (sx, sy) = center(j);
        column(&mut cv, sx, sy, tw * 0.86, th * 0.86, height[j], color[j]);
    }
    for (j, r, fade) in arcs {
        let (a, b) = (center(j), center(r));
        let (a, b) = ((a.0, a.1 - height[j]), (b.0, b.1 - height[r]));
        let lift = (a.0 - b.0).abs() * 0.25 + (a.1 - b.1).abs() * 0.3 + fh * 0.08;
        let mid = ((a.0 + b.0) * 0.5, a.1.min(b.1) - lift);
        let mut prev = a;
        for s in 1..=80 {
            let u = s as f32 / 80.0;
            let p = (
                (1.0 - u).powi(2) * a.0 + 2.0 * (1.0 - u) * u * mid.0 + u * u * b.0,
                (1.0 - u).powi(2) * a.1 + 2.0 * (1.0 - u) * u * mid.1 + u * u * b.1,
            );
            cv.line(prev, p, hot.scale(0.55 * fade));
            prev = p;
        }
        cv.glow(b.0, b.1, 1.5 + tw * 0.3, hot.scale(0.8 * fade));
    }
    let (hx, hy) = center(kk);
    let top = hy - height[kk];
    for y in 0..top.max(0.0) as i32 {
        let f = (y as f32 / top.max(1.0)).powi(2);
        cv.add(hx as i32, y, hot.scale(0.7 * f));
        cv.add(hx as i32 - 1, y, hot.scale(0.2 * f));
        cv.add(hx as i32 + 1, y, hot.scale(0.2 * f));
    }
    cv.glow(hx, top, 1.5 + tw * 0.4, hex(0xffffff).scale(0.9));
    Grid::from_canvas(&cv, rows)
}

pub struct Report {
    pub stamp: String,
    pub sections: Vec<(&'static str, Vec<(&'static str, String)>)>,
    pub saved: String,
    pub left: usize,
    pub txt: String,
}

pub fn save_report(sections: Vec<(&'static str, Vec<(&'static str, String)>)>, note: &str, left: usize) -> Report {
    let stamp = cmd("date", &["+%Y-%m-%d %H:%M"]).unwrap_or_default();
    let mut txt = format!("Blocknet Faraday Bench 2 results\n{stamp}\n");
    if !note.is_empty() {
        txt.push_str(note);
        txt.push('\n');
    }
    for (title, rows) in &sections {
        let lw = rows.iter().map(|r| r.0.len()).max().unwrap_or(0) + 3;
        txt.push_str(&format!("\n{title}\n"));
        for (label, value) in rows {
            txt.push_str(&format!("  {label:<lw$}{value}\n"));
        }
    }
    let dir = std::env::current_exe().ok().and_then(|p| p.parent().map(|d| d.to_path_buf())).unwrap_or_else(|| ".".into());
    let file = format!("blocknet-bench2-{}.txt", stamp.replace([' ', ':'], "-"));
    let path = dir.join(file);
    let saved = match std::fs::write(&path, &txt) {
        Ok(()) => format!("Saved to {}", path.display()),
        Err(e) => format!("Could not save the report: {e}"),
    };
    Report { stamp, sections, saved, left, txt }
}

pub fn report_card(g: &mut Grid, rep: &Report, intro: f32) {
    let (w, h) = (g.w, g.h);
    let (ink, dim, accent) = (hex(INK), hex(DIM), hex(ACCENT));
    let block = |s: &(&str, Vec<(&str, String)>)| -> Vec<(String, String, bool)> {
        let lw = s.1.iter().map(|r| r.0.len()).max().unwrap_or(0) + 3;
        let mut v = vec![(s.0.to_string(), String::new(), true)];
        v.extend(s.1.iter().map(|(l, val)| (format!("{l:<lw$}"), val.clone(), false)));
        v
    };
    let width = |b: &[(String, String, bool)]| b.iter().map(|r| r.0.chars().count() + r.1.chars().count()).max().unwrap_or(0);
    let stack = |idx: &[usize]| -> Vec<(String, String, bool)> {
        let mut v = Vec::new();
        for (n, &i) in idx.iter().enumerate() {
            if n > 0 {
                v.push((String::new(), String::new(), false));
            }
            v.extend(block(&rep.sections[i]));
        }
        v
    };
    let n = rep.sections.len();
    let split = rep.left.min(n);
    let (left, right) = (stack(&(0..split).collect::<Vec<_>>()), stack(&(split..n).collect::<Vec<_>>()));
    let gap = 6;
    let two = width(&left) + gap + width(&right) + 6 <= w.saturating_sub(4);
    let cols: Vec<Vec<(String, String, bool)>> = if two { vec![left, right] } else { vec![stack(&(0..n).collect::<Vec<_>>())] };
    let inner_w = if two { width(&cols[0]) + gap + width(&cols[1]) } else { width(&cols[0]) };
    let cw = (inner_w + 6).min(w.saturating_sub(2));
    let body = cols.iter().map(|c| c.len()).max().unwrap_or(0);
    let ch = (body + 5).min(h.saturating_sub(4));
    let cx = w.saturating_sub(cw) / 2;
    let cy = (1 + h.saturating_sub(ch + 3) / 2 + ((1.0 - ease(intro)) * 3.0) as usize).max(1);
    g.panel(cx, cy, cw, ch, hex(0x3a4766), "", ink);
    let fit = |s: &str, n: usize| s.chars().take(n).collect::<String>();
    let title = "BENCH 2 RESULTS";
    g.text(cx + cw.saturating_sub(title.len()) / 2, cy + 1, title, ink);
    g.text(cx + cw.saturating_sub(rep.stamp.len()) / 2, cy + 2, &rep.stamp, dim);
    let mut x = cx + 3;
    for (ci, col) in cols.iter().enumerate() {
        let room = cw.saturating_sub(x - cx + 3);
        for (r, (label, value, head)) in col.iter().enumerate() {
            let y = cy + 4 + r;
            if y + 1 >= cy + ch {
                break;
            }
            if *head {
                g.text(x, y, &fit(label, room), accent);
            } else {
                g.text(x, y, &fit(label, room), dim);
                g.text(x + label.chars().count(), y, &fit(value, room.saturating_sub(label.chars().count())), ink);
            }
        }
        if ci == 0 && two {
            x += width(col) + gap;
        }
    }
    let saved = &rep.saved;
    let shown: String = if saved.chars().count() + 4 > w {
        let keep = w.saturating_sub(5);
        format!("…{}", saved.chars().skip(saved.chars().count() - keep).collect::<String>())
    } else {
        saved.clone()
    };
    if cy + ch + 1 < h - 1 {
        g.text(w.saturating_sub(shown.chars().count()) / 2, cy + ch + 1, &shown, dim.lerp(ink, 0.4));
    }
}

pub fn keycap(g: &mut Grid, x: usize, y: usize, key: &str, a: f32) -> usize {
    let n = key.chars().count() + 2;
    let (edge, label) = (hex(0x8a3a8a).scale(a), hex(0xff4fd8).scale(a));
    g.text(x, y, &format!("╭{}╮", "─".repeat(n)), edge);
    g.text(x, y + 1, "│", edge);
    g.text(x + 2, y + 1, key, label);
    g.text(x + n + 1, y + 1, "│", edge);
    g.text(x, y + 2, &format!("╰{}╯", "─".repeat(n)), edge);
    n + 2
}

const PROMPT: [(&str, Option<&str>); 5] =
    [("Press ", None), ("", Some("Enter")), (" to continue     ·     Press ", None), ("", Some("V")), (" to disable visuals", None)];

pub fn key_prompt_width() -> usize {
    PROMPT.iter().map(|(t, k)| t.chars().count() + k.map(|k| k.chars().count() + 4).unwrap_or(0)).sum()
}

pub fn key_prompt_line(g: &mut Grid, y: usize, a: f32) {
    let full = "Enter to continue  ·  V to disable visuals";
    let short = "Enter: go  ·  V: no visuals";
    let s = if full.chars().count() + 2 <= g.w { full } else { short };
    let x = g.w.saturating_sub(s.chars().count()) / 2;
    g.text(x, y, s, hex(INK).scale(a));
    let key = hex(0xff4fd8).scale(a);
    g.text(x, y, "Enter", key);
    if let Some(i) = s.find("V ").or_else(|| s.find("V:")) {
        let col = s[..i].chars().count();
        g.text(x + col, y, "V", key);
    }
}

pub fn key_prompt(g: &mut Grid, y: usize, a: f32) {
    let parts = PROMPT;
    let width = key_prompt_width();
    let mut x = g.w.saturating_sub(width) / 2;
    for (text, key) in parts {
        if let Some(k) = key {
            x += keycap(g, x, y, k, a);
        } else {
            g.text(x, y + 1, text, hex(INK).scale(a));
            x += text.chars().count();
        }
    }
}

pub const TWEEN: f32 = 1.2;

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Scene {
    Boot,
    Ring,
    Lattice,
    Argon2id,
    Argon2d,
    Blake2b,
    Sha3,
    Fold,
    Report,
}

pub struct SceneCtx {
    pub lat: LatticeState,
    pub info: Vec<(String, String)>,
    pub argon_id_secs: f32,
    pub argon_d_secs: f32,
    pub fold_period: f32,
}

impl SceneCtx {
    pub fn new(info: Vec<(String, String)>) -> Self {
        SceneCtx {
            lat: LatticeState { vecs: Vec::new(), rng: Rand(0x9e37_79b9_7f4a_7c15), clock: 0.0 },
            info,
            argon_id_secs: 1.2,
            argon_d_secs: 0.3,
            fold_period: 14.0,
        }
    }
}

pub fn scene_grid(s: Scene, w: usize, rows: usize, t: f32, cx: &mut SceneCtx) -> Grid {
    match s {
        Scene::Boot => boot(w, rows, t, &mut cx.lat, &cx.info),
        Scene::Ring => ring(w, rows, t),
        Scene::Lattice => {
            let mut g = lattice(w, rows, t, &mut cx.lat);
            let size = (rows as f32 * 2.0 * 0.3).min(w as f32 * 0.2);
            draw_logo(&mut g, w as f32 * 0.5, rows as f32, size, 1.0, 0.8 + 0.2 * (t * 1.7).sin());
            g
        }
        Scene::Argon2id => memory(w, rows, t, 16, cx.argon_id_secs.max(0.05), hex(0x0f5f7a), hex(0xaef4ff)),
        Scene::Argon2d => memory(w, rows, t, 8, cx.argon_d_secs.max(0.05), hex(0x7a3a0c), hex(0xffd9a0)),
        Scene::Blake2b => {
            const SEGS: &[(usize, f32)] = &[(12, 2.2), (1140, 0.9)];
            if t < 2.2 {
                fx::blake_dials(w, rows, t, SEGS)
            } else if t < 2.8 {
                dissolve(fx::blake_dials(w, rows, t, SEGS), fx::blake_iso(w, rows, t, SEGS), ease((t - 2.2) / 0.6))
            } else {
                fx::blake_iso(w, rows, t, SEGS)
            }
        }
        Scene::Sha3 => fx::keccak_cube(w, rows, t, &[(5, 2.4), (115, 0.8)]),
        Scene::Fold => fx::fri_fold(w, rows, (t % cx.fold_period) * 10.0 / cx.fold_period),
        Scene::Report => {
            let mut g = fx::fri_fold(w, rows, 10.0);
            g.scale(0.3);
            g
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
pub enum SuiteState {
    Pending,
    Active,
    Done,
    Skipped,
}

pub struct Suite {
    pub name: &'static str,
    pub state: SuiteState,
    pub result: String,
}

pub struct Hud<'a> {
    pub suites: &'a [Suite],
    pub panel: &'a str,
    pub headline: String,
    pub lines: Vec<String>,
    pub progress: Option<f32>,
    pub run_frac: f32,
    pub run_secs: f32,
    pub right: String,
    pub intro: f32,
    pub report: bool,
}

pub fn interface(g: &mut Grid, hud: &Hud, frame: u64) {
    let (w, h) = (g.w, g.h);
    let (ink, dim, accent) = (hex(INK), hex(DIM), hex(ACCENT));
    let border = hex(0x26324a);
    let bar_bg = hex(0x0b0f1a);
    let slide = ease(hud.intro);
    for x in 0..w {
        for y in [0, h - 1] {
            if let Some(c) = g.get(x, y) {
                *c = Cell { ch: ' ', fg: ink, bg: bar_bg };
            }
        }
    }
    g.text(2, 0, "◆ BLOCKNET FARADAY  ·  BENCH 2", accent);
    if w > hud.right.chars().count() + 36 {
        g.text(w - hud.right.chars().count() - 2, 0, &hud.right, dim);
    }
    let secs = hud.run_secs as u64;
    let label = format!(" {:>3.0}%  {}:{:02} ", 100.0 * hud.run_frac.clamp(0.0, 1.0), secs / 60, secs % 60);
    g.text(1, h - 1, &label, dim);
    let bw = w.saturating_sub(label.chars().count() + 40);
    g.bar(label.chars().count() + 2, h - 1, bw, hud.run_frac, accent, hex(0x1d2333));
    let hint = "press I for more info   ·   q quit";
    let hx = w.saturating_sub(hint.chars().count() + 2);
    g.text(hx, h - 1, hint, dim);
    g.text(hx + 6, h - 1, "I", hex(0xff4fd8));
    g.text(hx + hint.chars().count() - 6, h - 1, "q", hex(0xff4fd8));
    if h < 12 || w < 46 || hud.report {
        return;
    }
    let pw = (w / 3).clamp(26, 36);
    let ph = hud.suites.len() + 2;
    if w >= 84 && h >= ph + 6 {
        let off = ((1.0 - slide) * (pw as f32 + 2.0)) as usize;
        let px = 2usize;
        let vis = pw - off.min(pw);
        if vis >= 6 {
            g.panel(px, 2, vis, ph, border, "SUITES", accent);
            for (i, s) in hud.suites.iter().enumerate() {
                let y = 3 + i;
                let (icon, fg) = match s.state {
                    SuiteState::Done => ('✓', hex(0x7cff9f)),
                    SuiteState::Active => (['◐', '◓', '◑', '◒'][(frame / 4 % 4) as usize], accent),
                    SuiteState::Skipped => ('–', dim),
                    SuiteState::Pending => ('·', dim),
                };
                let name: String = s.name.chars().take(vis.saturating_sub(6)).collect();
                g.text(px + 2, y, &icon.to_string(), fg);
                let nf = match s.state {
                    SuiteState::Active => ink,
                    SuiteState::Done => ink.scale(0.75),
                    _ => dim,
                };
                g.text(px + 4, y, &name, nf);
                let r = &s.result;
                if !r.is_empty() && vis > name.chars().count() + r.chars().count() + 8 {
                    g.text(px + vis - r.chars().count() - 2, y, r, if s.state == SuiteState::Active { accent } else { dim });
                }
            }
        }
    }
    let rw = ((w as f32 * 0.55) as usize).clamp(40, 74).min(w.saturating_sub(4));
    let rh = hud.lines.len() + 3 + hud.progress.is_some() as usize;
    if h < rh + 4 {
        return;
    }
    let rx = w.saturating_sub(rw + 2);
    let ry = h.saturating_sub(rh + 2) + ((1.0 - slide) * 6.0) as usize;
    g.panel(rx, ry, rw, rh, border, hud.panel, accent);
    let fit = |s: &str| s.chars().take(rw.saturating_sub(4)).collect::<String>();
    g.text(rx + 2, ry + 1, &fit(&hud.headline), ink);
    for (k, l) in hud.lines.iter().enumerate() {
        g.text(rx + 2, ry + 2 + k, &fit(l), dim.lerp(ink, 0.5));
    }
    match hud.progress {
        Some(p) => g.bar(rx + 2, ry + rh - 2, rw.saturating_sub(4), p, accent, hex(0x1d2333)),
        None => {
            let bw = rw.saturating_sub(4);
            let pos = (frame as f32 * 0.6) % (bw as f32 + 10.0) - 5.0;
            for i in 0..bw {
                let d = (i as f32 - pos).abs();
                let col = hex(0x1d2333).lerp(accent, (1.0 - d / 5.0).max(0.0));
                if let Some(c) = g.get(rx + 2 + i, ry + rh - 2) {
                    c.ch = '━';
                    c.fg = col;
                }
            }
        }
    }
}

pub fn start_info(m: &crate::machine::Machine) -> Vec<(String, String)> {
    let pair = |a: &str, b: String| (a.to_string(), b);
    vec![
        pair("cpu", format!("{}  ·  {} threads  ·  {} RAM", m.cpu, m.threads, m.ram())),
        pair("system", format!("{}  ·  {}  ·  {}", m.os, m.arch, m.simd_short())),
        pair("spend", "post-quantum zk-STARK  ·  full-chain anonymity set  ·  112-bit security".into()),
        pair("keys", "post-quantum ML-KEM-768 key exchange  ·  Poseidon2 hashes".into()),
        pair("block", "~470 transactions per 2 MB block  ·  one folded proof".into()),
    ]
}

pub struct Stager {
    pub scene: Scene,
    pub since: std::time::Instant,
    prev: Option<(Scene, f32)>,
}

impl Stager {
    pub fn new(scene: Scene) -> Self {
        Stager { scene, since: std::time::Instant::now(), prev: None }
    }
    pub fn set(&mut self, scene: Scene) {
        if scene != self.scene {
            self.prev = Some((self.scene, self.local()));
            self.scene = scene;
            self.since = std::time::Instant::now();
        }
    }
    pub fn local(&self) -> f32 {
        self.since.elapsed().as_secs_f32()
    }
    pub fn draw(&self, w: usize, h: usize, cx: &mut SceneCtx, visuals: bool, global: f32) -> Grid {
        let mut one = |s: Scene, t: f32| {
            if visuals || s == Scene::Boot {
                scene_grid(s, w, h, if s == Scene::Lattice { global } else { t }, cx)
            } else {
                Grid::new(w, h, hex(0x05070d))
            }
        };
        let local = self.local();
        let g = one(self.scene, local);
        match self.prev {
            Some((p, held)) if local < TWEEN => {
                let prev = one(p, held + local);
                dissolve(prev, g, ease(local / TWEEN))
            }
            _ => g,
        }
    }
}

pub struct Screen {
    term: Option<Term>,
    pub cols: usize,
    pub rows: usize,
    last_poll: std::time::Instant,
    out: String,
    frame_start: std::time::Instant,
    pub frame: u64,
}

impl Screen {
    pub fn open() -> Self {
        let term = Term::open();
        let (cols, rows) = Term::size();
        let now = std::time::Instant::now();
        Screen { term: Some(term), cols, rows, last_poll: now, out: String::new(), frame_start: now, frame: 0 }
    }
    pub fn begin(&mut self, cx: &mut SceneCtx) -> (usize, usize) {
        self.frame_start = std::time::Instant::now();
        if self.last_poll.elapsed() > std::time::Duration::from_millis(150) {
            let (c, r) = Term::size();
            if (c, r) != (self.cols, self.rows) {
                self.cols = c;
                self.rows = r;
                cx.lat.vecs.clear();
                print!("\x1b[0m\x1b[2J");
            }
            self.last_poll = std::time::Instant::now();
        }
        (self.cols.max(20), self.rows.max(8))
    }
    pub fn show(&mut self, g: &Grid, fps: u64) {
        emit(g, &mut self.out);
        self.frame += 1;
        if let Some(rest) = std::time::Duration::from_millis(1000 / fps).checked_sub(self.frame_start.elapsed()) {
            std::thread::sleep(rest);
        }
    }
    pub fn close(&mut self) {
        self.term.take();
    }
}

pub fn start_screen(w: usize, h: usize, t: f32, cx: &mut SceneCtx, ready: bool, waiting: &str) -> Grid {
    let mut g = scene_grid(Scene::Boot, w, h, t, cx);
    if t > 4.2 {
        let free = boot_bottom(w, h, cx.info.len()) + 1;
        let y = (h * 4 / 5).max(free).min(h.saturating_sub(4));
        if ready {
            let a = (0.7 + 0.3 * (t * 2.5).sin().abs()) * ease((t - 4.2) / 0.8);
            if y >= free && key_prompt_width() + 2 <= w {
                key_prompt(&mut g, y, a);
            } else {
                let row = free.min(h.saturating_sub(1));
                for x in 0..w {
                    if let Some(c) = g.get(x, row) {
                        c.ch = ' ';
                    }
                }
                key_prompt_line(&mut g, row, a);
            }
        } else {
            let dots = ".".repeat(((t * 2.0) as usize) % 4);
            let msg = format!("{waiting}{dots}");
            g.text(w.saturating_sub(msg.chars().count()) / 2, y + 1, &msg, hex(DIM));
        }
    }
    g
}

pub fn start_key() -> Option<bool> {
    match KEY.swap(0, std::sync::atomic::Ordering::SeqCst) {
        b'\r' | b'\n' => Some(true),
        b'v' | b'V' => Some(false),
        _ => None,
    }
}

const INFO: &str = include_str!("info.md");

fn info_section(scene: Scene) -> Option<(&'static str, &'static str)> {
    let key = match scene {
        Scene::Boot => return None,
        Scene::Ring => "Legacy RingCT",
        Scene::Lattice => "Faraday spend",
        Scene::Argon2id | Scene::Argon2d => "Argon2",
        Scene::Blake2b => "BLAKE2b",
        Scene::Sha3 => "SHA3",
        Scene::Fold => "Block fold",
        Scene::Report => "Report",
    };
    INFO.split("\n## ").skip(1).find(|s| s.starts_with(key)).and_then(|s| s.split_once('\n')).map(|(t, b)| (t.trim(), b))
}

fn wrap(text: &str, width: usize, indent: usize, out: &mut Vec<String>) {
    let mut line = String::new();
    for word in text.split_whitespace() {
        let n = line.chars().count();
        if n > 0 && n + 1 + word.chars().count() > width {
            out.push(std::mem::take(&mut line));
            line = " ".repeat(indent);
        }
        if !line.trim().is_empty() {
            line.push(' ');
        }
        line.push_str(word);
    }
    if !line.trim().is_empty() {
        out.push(line);
    }
}

fn info_lines(body: &str, width: usize) -> Vec<String> {
    let mut out = Vec::new();
    for para in body.split("\n\n").map(str::trim).filter(|p| !p.is_empty()) {
        if !out.is_empty() {
            out.push(String::new());
        }
        let mut items: Vec<String> = Vec::new();
        for l in para.lines() {
            match l.trim_start().strip_prefix("- ") {
                Some(item) => items.push(format!("• {item}")),
                None if !items.is_empty() && l.starts_with("  ") => {
                    let last = items.last_mut().unwrap();
                    last.push(' ');
                    last.push_str(l.trim());
                }
                None => items.push(l.trim().to_string()),
            }
        }
        if items.iter().any(|i| i.starts_with('•')) {
            for i in items {
                wrap(&i, width, 2, &mut out);
            }
        } else {
            wrap(&items.join(" "), width, 0, &mut out);
        }
    }
    out
}

pub fn info_keys(open: &mut bool) {
    match KEY.swap(0, std::sync::atomic::Ordering::SeqCst) {
        b'i' | b'I' => *open = !*open,
        27 => *open = false,
        _ => {}
    }
}

pub fn info_card(g: &mut Grid, scene: Scene) {
    let Some((title, body)) = info_section(scene) else { return };
    let (w, h) = (g.w, g.h);
    let cw = 76.min(w.saturating_sub(4));
    if cw < 24 || h < 8 {
        return;
    }
    let mut lines = info_lines(body, cw - 6);
    let room = h.saturating_sub(7);
    if lines.len() > room {
        lines.truncate(room.saturating_sub(1));
        lines.push("…".into());
    }
    let ch = lines.len() + 6;
    let (x0, y0) = ((w - cw) / 2, h.saturating_sub(ch) / 2);
    let black = Rgb::default();
    for y in y0..y0 + ch {
        for x in x0..x0 + cw {
            if let Some(c) = g.get(x, y) {
                *c = Cell { ch: ' ', fg: black, bg: black };
            }
        }
    }
    g.panel(x0, y0, cw, ch, hex(0x3a4766), "", hex(INK));
    for y in y0 + 1..y0 + ch - 1 {
        for x in x0 + 1..x0 + cw - 1 {
            if let Some(c) = g.get(x, y) {
                c.bg = black;
            }
        }
    }
    g.text(x0 + 3, y0 + 1, title, hex(ACCENT));
    for (i, l) in lines.iter().enumerate() {
        g.text(x0 + 3, y0 + 3 + i, l, hex(INK));
    }
    let close = "ESC to close";
    g.text(x0 + cw - close.len() - 3, y0 + ch - 2, close, hex(DIM));
    g.text(x0 + cw - close.len() - 3, y0 + ch - 2, "ESC", hex(0xff4fd8));
}
