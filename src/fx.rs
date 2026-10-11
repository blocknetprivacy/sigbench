#![allow(dead_code)]

use crate::algo::*;
use crate::gfx::*;

pub const WHITE: u32 = 0xffffff;
pub const INK: u32 = 0xe8ecf4;
pub const DIM: u32 = 0x6b7590;

pub struct Clock {
    pub segs: &'static [(usize, f32)],
}

pub struct Tick {
    pub hash: u64,
    pub step: f32,
    pub dur: f32,
}

impl Clock {
    pub fn at(&self, t: f32) -> Tick {
        let (mut t0, mut s0) = (0.0f32, 0usize);
        let first: f32 = self.segs.iter().map(|s| s.1).sum();
        for &(n, secs) in self.segs {
            if t < t0 + secs {
                return Tick { hash: 0, step: s0 as f32 + (t - t0) / secs * n as f32, dur: first };
            }
            t0 += secs;
            s0 += n;
        }
        let steps = s0 as f32;
        let (mut d, mut k, min) = (0.8f32, 1u64, 1.0 / 30.0);
        loop {
            if d <= min {
                return Tick { hash: k + ((t - t0) / min) as u64, step: steps, dur: min };
            }
            if t < t0 + d {
                return Tick { hash: k, step: (t - t0) / d * steps, dur: d };
            }
            t0 += d;
            d *= 0.62;
            k += 1;
        }
    }
}

pub fn slowmo(dur: f32, real_ns: f32) -> String {
    let x = dur / (real_ns * 1e-9);
    let s = format!("{:.0}", x);
    let mut out = String::new();
    for (i, ch) in s.chars().enumerate() {
        if i > 0 && (s.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(ch);
    }
    format!("slow motion ×{out}")
}

pub fn backdrop(w: usize, ph: usize, tint: Rgb) -> Canvas {
    let mut cv = Canvas::new(w, ph, Rgb::default());
    let (fw, fh) = (w as f32, ph as f32);
    for y in 0..ph {
        for x in 0..w {
            let r = (((x as f32 - fw * 0.5) / fw).powi(2) + ((y as f32 - fh * 0.45) / fh).powi(2)).sqrt();
            cv.px[y * w + x] = tint.scale(0.16).lerp(hex(0x020306), (r * 2.1).min(1.0));
        }
    }
    cv
}

#[allow(clippy::too_many_arguments)]
pub fn word_tile(cv: &mut Canvas, x0: f32, y0: f32, s: f32, word: u64, flash: u64, fk: f32, on: Rgb, off: Rgb) {
    let size = 8.0 * s;
    for py in y0.floor() as i32..(y0 + size).ceil() as i32 {
        for px in x0.floor() as i32..(x0 + size).ceil() as i32 {
            let (fx, fy) = ((px as f32 + 0.5 - x0) / s, (py as f32 + 0.5 - y0) / s);
            if !(0.0..8.0).contains(&fx) || !(0.0..8.0).contains(&fy) {
                continue;
            }
            if s >= 3.0 && (fx.fract() > 0.78 || fy.fract() > 0.78) {
                continue;
            }
            let bit = 63 - (fy as u32 * 8 + fx as u32);
            let mut c = if word >> bit & 1 == 1 { on } else { off };
            if flash >> bit & 1 == 1 {
                c = c.add(hex(WHITE).scale(fk));
            }
            cv.set(px, py, c);
        }
    }
}

pub fn frame(cv: &mut Canvas, x0: f32, y0: f32, x1: f32, y1: f32, c: Rgb) {
    cv.line((x0, y0), (x1, y0), c);
    cv.line((x0, y1), (x1, y1), c);
    cv.line((x0, y0), (x0, y1), c);
    cv.line((x1, y0), (x1, y1), c);
}

pub fn beam(cv: &mut Canvas, a: (f32, f32), b: (f32, f32), r: f32, c: Rgb) {
    let n = ((b.0 - a.0).abs().max((b.1 - a.1).abs()) as usize).max(1);
    for i in 0..=n {
        let t = i as f32 / n as f32;
        cv.glow(a.0 + (b.0 - a.0) * t, a.1 + (b.1 - a.1) * t, r, c.scale(1.0 / (1.0 + r)));
    }
}

pub fn centered(g: &mut Grid, y: usize, s: &str, fg: Rgb) {
    let n = s.chars().count();
    let s: String = if n > g.w.saturating_sub(2) { s.chars().take(g.w.saturating_sub(2)).collect() } else { s.to_string() };
    g.text(g.w.saturating_sub(s.chars().count()) / 2, y, &s, fg);
}

pub fn digest_lines(g: &mut Grid, y: usize, d: &[u8; 64], col: Rgb) {
    let hit = d[0] >> 4 == 0;
    let c = if hit { hex(0xffd36b) } else { col };
    if g.w >= 72 {
        centered(g, y, &hex_str(&d[..32]), c);
        centered(g, y + 1, &hex_str(&d[32..]), c);
    } else {
        let n = (g.w.saturating_sub(4)) / 2;
        centered(g, y, &hex_str(&d[..n.min(64)]), c);
    }
    if hit {
        centered(g, y + 2, "✦ starts with 0: a hit", hex(0xffd36b));
    }
}

pub fn hex_str(b: &[u8]) -> String {
    hex_bytes(b)
}

#[allow(clippy::too_many_arguments)]
pub fn lane_column(cv: &mut Canvas, sx: f32, sy: f32, tw: f32, th: f32, h: f32, word: u64, shift: f32, flash: u64, fk: f32, on: Rgb, top: Rgb) {
    let off = on.scale(0.1);
    for py in (sy - h - th).floor() as i32..=(sy + th).ceil() as i32 {
        for px in (sx - tw).floor() as i32..=(sx + tw).ceil() as i32 {
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
                if face > 0.75 { top.scale(1.3) } else { top }
            } else {
                let v = ((span - dy) / h).clamp(0.0, 0.9999);
                let band = ((v * 64.0 - shift).rem_euclid(64.0)) as u32;
                let mut c = if word >> band & 1 == 1 { on } else { off };
                if flash >> band & 1 == 1 {
                    c = c.add(hex(WHITE).scale(fk));
                }
                c.scale(if dx < 0.0 { 0.95 } else { 0.62 })
            };
            cv.set(px, py, c);
        }
    }
}

pub fn keccak_cube(w: usize, rows: usize, t: f32, segs: &'static [(usize, f32)]) -> Grid {
    let clock = Clock { segs };
    let tk = clock.at(t);
    let tr = sha3_512_trace(&mining_input(tk.hash));
    let ph = rows * 2;
    let (fw, fh) = (w as f32, ph as f32);
    let mut cv = backdrop(w, ph, hex(0x3a1a6b));
    let done = tk.step >= 120.0;
    let si = (tk.step as usize).min(119);
    let frac = if done { 1.0 } else { tk.step.fract() };
    let step = KSTEPS[si % 5];
    let (prev, next) = if done { (tr.states[120], tr.states[120]) } else { (tr.states[si], tr.states[si + 1]) };
    let h = fh * 0.42;
    let tw = (fw * 0.062).min((fh * 0.88 - h) / (5.0 * 1.25));
    let th = tw * 0.5;
    let sp = 1.25;
    let ox = fw * 0.5;
    let oy = fh * 0.93 - 2.0 * 4.0 * th * sp - th;
    let pos = |i: usize| -> (f32, f32) {
        let (x, y) = ((i % 5) as f32, (i / 5) as f32);
        (ox + (x - y) * tw * sp, oy + (x + y) * th * sp)
    };
    let (rate_on, cap_on) = (hex(0xc58bff), hex(0x4f6bff));
    let e = ease(frac);
    let mut cols: Vec<(f32, f32, usize)> = (0..25)
        .map(|i| {
            if step == KStep::Pi && !done {
                let (a, b) = (pos(i), pos(pi_dest(i)));
                (a.0 + (b.0 - a.0) * e, a.1 + (b.1 - a.1) * e, i)
            } else {
                let p = pos(i);
                (p.0, p.1, i)
            }
        })
        .collect();
    cols.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
    for (sx, sy, i) in cols {
        let (x, y) = (i % 5, i / 5);
        let (word, shift, flash) = match step {
            _ if done => (next[i], 0.0, 0),
            KStep::Rho => (prev[i], frac * RHO[i] as f32, 0),
            KStep::Pi => (prev[i], 0.0, 0),
            _ => (next[i], 0.0, prev[i] ^ next[i]),
        };
        let fk = (1.0 - frac).powi(2);
        let on = if i < RATE_LANES { rate_on } else { cap_on };
        let mut top = on.scale(0.55);
        if !done {
            match step {
                KStep::Theta if x == (frac * 5.0) as usize => top = top.add(hex(WHITE).scale(0.5)),
                KStep::Chi if y == (frac * 5.0) as usize => top = top.add(hex(WHITE).scale(0.5)),
                KStep::Iota if i == 0 => top = hex(0xffd36b).scale(1.0 + fk),
                _ => {}
            }
        } else if i < 8 {
            top = hex(0xffd36b);
        }
        lane_column(&mut cv, sx, sy, tw * 0.86, th * 0.86, h, word, shift, flash, fk, on, top);
    }
    if done {
        for i in 0..8 {
            let p = pos(i);
            beam(&mut cv, (p.0, p.1 - h - th), (p.0, 0.0), 0.6, hex(0xffd36b).scale(0.18));
        }
    }
    let mut g = Grid::from_canvas(&cv, rows);
    let info = if done {
        "squeeze: lanes 0-7 are the 512-bit digest".to_string()
    } else {
        format!("round {:>2}/24  ·  {}", si / 5 + 1, step.name())
    };
    centered(&mut g, 2, &info, hex(INK));
    centered(&mut g, 3, &format!("5 x 5 lanes x 64 bits  ·  nonce {}  ·  {}", tk.hash, slowmo(tk.dur, 355.0)), hex(DIM));
    g.text(2, rows.saturating_sub(4), "■ rate (9 lanes)", rate_on);
    g.text(2, rows.saturating_sub(3), "■ capacity (16 lanes)", cap_on);
    g
}

pub fn fri_fold(w: usize, rows: usize, t: f32) -> Grid {
    let ph = rows * 2;
    let (fw, fh) = (w as f32, ph as f32);
    let mut cv = backdrop(w, ph, hex(0x103a40));
    const N: [usize; 5] = [256, 64, 16, 4, 1];
    let mut layers: Vec<Vec<f32>> = vec![(0..256)
        .map(|i| {
            let th = i as f32 / 256.0 * std::f32::consts::TAU;
            (0.55 * (th + 0.3).sin() + 0.3 * (3.0 * th + 1.1).sin() + 0.18 * (7.0 * th + 2.0).sin() + 0.1 * (13.0 * th).sin()) * 0.9
        })
        .collect()];
    for l in 0..4 {
        let (p, n) = (&layers[l], N[l + 1]);
        let beta = [0.7, -0.5, 0.9, -0.6][l];
        let child: Vec<f32> = (0..n)
            .map(|j| {
                let q: Vec<f32> = (0..4).map(|r| p[j + r * n]).collect();
                ((q[0] + q[1] + q[2] + q[3]) * 0.25 + beta * (q[0] - q[2]) * 0.5 + 0.5 * beta * (q[1] - q[3]) * 0.5).clamp(-1.0, 1.0)
            })
            .collect();
        layers.push(child);
    }
    let mx = fw * 0.08;
    let ww = fw - 2.0 * mx;
    let ly = |l: usize| fh * 0.17 + l as f32 * fh * 0.165;
    let amp = fh * 0.05;
    let px = |l: usize, j: usize| mx + (j as f32 + 0.5) / N[l] as f32 * ww;
    let pt = |l: usize, j: usize| (px(l, j), ly(l) - layers[l][j] * amp);
    let color = |l: usize, v: f32| hex(0x2ef2c3).lerp(hex(0xffc857), l as f32 / 4.0).scale(0.7 + 0.3 * v.abs());
    let reveal0 = (t / 1.0).clamp(0.0, 1.0);
    for j in 0..256 {
        if (j as f32) / 256.0 > reveal0 {
            break;
        }
        let (x, y) = pt(0, j);
        if j > 0 {
            cv.line(pt(0, j - 1), (x, y), color(0, layers[0][j]).scale(0.6));
        }
        cv.glow(x, y, 0.7, color(0, layers[0][j]).scale(0.7));
    }
    for l in 1..5 {
        let start = 1.0 + (l - 1) as f32 * 1.35;
        let lp = ((t - start) / 1.35).clamp(0.0, 1.0);
        if lp <= 0.0 {
            continue;
        }
        let n = N[l];
        for j in 0..n {
            let child = pt(l, j);
            for r in 0..4 {
                let parent = pt(l - 1, j + r * n);
                let delay = (j as f32 / n as f32) * 0.35 + r as f32 * 0.05;
                let p = ((lp - delay) / 0.55).clamp(0.0, 1.0);
                let a = 0.10 + 0.25 / (n as f32).sqrt();
                if p > 0.0 {
                    let e = ease(p);
                    let tip = (parent.0 + (child.0 - parent.0) * e, parent.1 + (child.1 - parent.1) * e);
                    cv.line(parent, tip, color(l, 0.5).scale(a));
                    if p < 1.0 {
                        cv.glow(tip.0, tip.1, 0.8, color(l, 1.0).scale(0.8));
                    }
                }
            }
            let grown = ((lp - (j as f32 / n as f32) * 0.35 - 0.55) / 0.1).clamp(0.0, 1.0);
            if grown > 0.0 {
                let (x, y) = child;
                cv.line((x, ly(l)), (x, y), color(l, 0.6).scale(0.4 * grown));
                cv.glow(x, y, 0.9 + l as f32 * 0.5, color(l, layers[l][j]).scale(grown));
            }
        }
    }
    let qt = ((t - 6.6) / 2.2).clamp(0.0, 1.0);
    let queries = [37usize, 101, 166, 203, 250];
    if qt > 0.0 {
        let gold = hex(0xffe08a);
        for (qi, &q) in queries.iter().enumerate() {
            let depth = qt * 4.0 - qi as f32 * 0.12;
            for l in 0..4 {
                let p = (depth - l as f32).clamp(0.0, 1.0);
                if p <= 0.0 {
                    break;
                }
                let n = N[l + 1];
                let j = q % n;
                for r in 0..4 {
                    let sib = pt(l, j + r * n);
                    cv.glow(sib.0, sib.1, 1.3, gold.scale(0.7 * p));
                }
                let a = pt(l, q % N[l]);
                let b = pt(l + 1, j);
                let e = ease(p);
                beam(&mut cv, a, (a.0 + (b.0 - a.0) * e, a.1 + (b.1 - a.1) * e), 0.5, gold.scale(0.5));
            }
        }
    }
    let mut g = Grid::from_canvas(&cv, rows);
    centered(&mut g, 2, "FRI: each fold merges 4 points into 1", hex(INK));
    let sub = if qt > 0.0 { "106 queries check the folds (5 shown)" } else { "this is how every proof shrinks to a few hundred KB" };
    centered(&mut g, 3, sub, hex(DIM));
    for (l, n) in N.iter().enumerate() {
        let y = ((ly(l)) / 2.0) as usize;
        if l == 0 || t > 1.0 + (l - 1) as f32 * 1.35 {
            g.text(1, y, &format!("{n:>3}"), hex(DIM));
        }
    }
    g
}

pub fn b2_op_text(op: &B2Op) -> String {
    let [a, b, c, d] = G_LANES[op.g];
    match op.kind {
        Arx::Rot(r) => format!("v{0} ← v{0} ⋙ {r}", op.lane),
        Arx::Add if op.lane == a => format!("v{a} ← v{a} + v{b} + m{}", op.msg.unwrap_or(0)),
        Arx::Add => format!("v{c} ← v{c} + v{d}"),
        Arx::Xor if op.lane == d => format!("v{d} ← v{d} ⊕ v{a}"),
        Arx::Xor => format!("v{b} ← v{b} ⊕ v{c}"),
    }
}

fn op_flow(op: &B2Op) -> Option<(usize, usize)> {
    let [a, b, c, d] = G_LANES[op.g];
    match op.kind {
        Arx::Add if op.lane == a => Some((b, a)),
        Arx::Add => Some((d, c)),
        Arx::Xor if op.lane == d => Some((a, d)),
        Arx::Xor => Some((c, b)),
        Arx::Rot(_) => None,
    }
}

fn op_color(kind: Arx) -> Rgb {
    match kind {
        Arx::Add => hex(0xffb347),
        Arx::Xor => hex(0xd8fbff),
        Arx::Rot(_) => hex(0xff6ad5),
    }
}

fn shown_bit(tr: &B2Trace, i: usize, f: f32, l: usize, pos: f32) -> (bool, f32) {
    let n = tr.ops.len();
    let bit = |w: u64, p: f32| w >> ((p.rem_euclid(64.0)) as u32).min(63) & 1 == 1;
    if i >= n {
        return (bit(tr.states[n][l], pos), 0.0);
    }
    let (prev, next, op) = (tr.states[i][l], tr.states[i + 1][l], tr.ops[i]);
    if op.lane != l {
        return (bit(next, pos), 0.0);
    }
    match op.kind {
        Arx::Rot(r) => (bit(prev, pos + f * r as f32), 0.0),
        Arx::Add => {
            let sweep = 64.0 * f;
            let glow = (-((pos - sweep).powi(2)) * 0.5).exp() * 0.9;
            (bit(if pos < sweep { next } else { prev }, pos), glow)
        }
        Arx::Xor => {
            let flipped = (prev ^ next) >> (pos as u32).min(63) & 1 == 1;
            (bit(next, pos), if flipped { (1.0 - f).powi(2) } else { 0.0 })
        }
    }
}

pub const B2_SEGS: &[(usize, f32)] = &[(12, 3.8), (1140, 2.0)];

fn b2_header(g: &mut Grid, tr: &B2Trace, i: usize, tk: &Tick) {
    let info = if i < tr.ops.len() {
        let o = tr.ops[i];
        format!("round {:>2}/12  ·  G{}  ·  {}", o.round + 1, o.g, b2_op_text(&o))
    } else {
        "digest  h ⊕ v[0..8] ⊕ v[8..16]".into()
    };
    centered(g, 2, &info, hex(INK));
    centered(g, 3, &format!("16 words x 64 bits  ·  nonce {}  ·  {}", tk.hash, slowmo(tk.dur, 212.0)), hex(DIM));
}

pub fn blake_dials(w: usize, rows: usize, t: f32, segs: &'static [(usize, f32)]) -> Grid {
    let tk = Clock { segs }.at(t);
    let tr = blake2b_trace(&mining_input(tk.hash));
    let n = tr.ops.len();
    let i = (tk.step as usize).min(n);
    let f = tk.step.fract();
    let ph = rows * 2;
    let (fw, fh) = (w as f32, ph as f32);
    let mut cv = backdrop(w, ph, hex(0x0a3a52));
    let pitch = (fh * 0.78 / 4.0).min(fw * 0.62 / 4.0);
    let rad = pitch * 0.4;
    let (cx0, cy0) = (fw * 0.5, fh * 0.56);
    let center = |l: usize| (cx0 + ((l % 4) as f32 - 1.5) * pitch, cy0 + ((l / 4) as f32 - 1.5) * pitch);
    let op = (i < n).then(|| tr.ops[i]);
    let lanes = op.map(|o| G_LANES[o.g]).unwrap_or([99; 4]);
    let base = hex(0x2ad4ff);
    let tau = std::f32::consts::TAU;
    for l in 0..16 {
        let (cx, cy) = center(l);
        let involved = lanes.contains(&l);
        let active = op.is_some_and(|o| o.lane == l);
        let on = if active { op_color(op.unwrap().kind) } else if involved { base.lerp(hex(0xd8fbff), 0.4) } else { base.scale(0.55) };
        for k in 0..96 {
            let a = k as f32 / 96.0 * tau;
            cv.add((cx + (rad + 1.6) * a.cos()) as i32, (cy + (rad + 1.6) * a.sin()) as i32, on.scale(if involved { 0.18 } else { 0.06 }));
        }
        for k in 0..64 {
            let pos = 63.0 - k as f32;
            let (set, extra) = shown_bit(&tr, i, f, l, pos);
            let a = -tau / 4.0 + (k as f32 + 0.5) / 64.0 * tau;
            let c = if set { on } else { on.scale(0.08) }.add(hex(WHITE).scale(extra * 0.8));
            cv.glow(cx + rad * a.cos(), cy + rad * a.sin(), 0.45 + rad * 0.025, c);
        }
        if active {
            if let Some(Arx::Rot(r)) = op.map(|o| o.kind) {
                let a = -tau / 4.0 + f * r as f32 / 64.0 * tau;
                beam(&mut cv, (cx, cy), (cx + rad * 0.8 * a.cos(), cy + rad * 0.8 * a.sin()), 0.5, on.scale(0.5));
            }
            cv.glow(cx, cy, rad * 0.5, on.scale(0.12));
        }
    }
    if let Some(o) = op {
        if let Some((from, to)) = op_flow(&o) {
            let (a, b) = (center(from), center(to));
            beam(&mut cv, a, b, 0.5, op_color(o.kind).scale(0.3));
            let e = ease(f);
            cv.glow(a.0 + (b.0 - a.0) * e, a.1 + (b.1 - a.1) * e, 1.6, op_color(o.kind));
        }
        if o.msg.is_some() {
            let b = center(o.lane);
            let e = ease(f);
            cv.glow(b.0, fh * 0.12 + (b.1 - fh * 0.12) * e, 1.4, hex(0xffd36b).scale(1.0 - f * 0.5));
        }
    }
    let mut g = Grid::from_canvas(&cv, rows);
    b2_header(&mut g, &tr, i, &tk);
    if rad >= 5.0 {
        for l in 0..16 {
            let (cx, cy) = center(l);
            let s = format!("v{l}");
            g.text((cx as usize).saturating_sub(s.len() / 2), (cy / 2.0) as usize, &s, if lanes.contains(&l) { hex(INK) } else { hex(DIM) });
        }
    }
    g
}

pub fn blake_cylinder(w: usize, rows: usize, t: f32) -> Grid {
    let tk = Clock { segs: &[(4, 4.6), (44, 1.4)] }.at(t);
    let tr = blake2b_trace(&mining_input(tk.hash));
    let ph = rows * 2;
    let (fw, fh) = (w as f32, ph as f32);
    let mut cv = backdrop(w, ph, hex(0x0a3a52));
    let done = tk.step >= 48.0;
    let u = (tk.step as usize).min(47);
    let f = tk.step.fract();
    let (round, phase) = (u / 4, u % 4);
    let (state, prev, diag, g_now, gf, label): ([u64; 16], [u64; 16], f32, Option<usize>, f32, String) = if done {
        (*tr.after_g(96), *tr.after_g(96), 0.0, None, 0.0, "digest  h ⊕ v[0..8] ⊕ v[8..16]".into())
    } else {
        match phase {
            0 | 2 => {
                let g = (f * 4.0) as usize + if phase == 2 { 4 } else { 0 };
                let k = round * 8 + g;
                let what = if phase == 0 { "column step: G0-G3 mix each column" } else { "diagonal step: G4-G7 mix each diagonal" };
                (*tr.after_g(k + 1), *tr.after_g(k), if phase == 0 { 0.0 } else { 1.0 }, Some(g), (f * 4.0).fract(), what.into())
            }
            1 => (*tr.after_g(round * 8 + 4), *tr.after_g(round * 8 + 4), ease(f), None, 0.0, "diagonalize: row r turns r places".into()),
            _ => (*tr.after_g(round * 8 + 8), *tr.after_g(round * 8 + 8), 1.0 - ease(f), None, 0.0, "undiagonalize: rows turn back".into()),
        }
    };
    let active: [usize; 4] = g_now.map(|g| G_LANES[g]).unwrap_or([99; 4]);
    let rc = (fw * 0.3).min(fh * 1.1);
    let cx = fw * 0.5;
    let sv = fh * 0.6 / 38.4;
    let top = fh * 0.56 - 19.2 * sv;
    let spin = t * 0.45;
    let quarter = std::f32::consts::FRAC_PI_2;
    let base = hex(0x2ad4ff);
    let sample = |phi: f32, r: usize, brow: usize| -> Option<(Rgb, bool)> {
        let a = (phi - spin + r as f32 * diag * quarter).rem_euclid(4.0 * quarter);
        let cpos = a / quarter;
        let c = (cpos as usize).min(3);
        let within = (cpos - c as f32) * 9.6;
        if within >= 8.0 {
            return None;
        }
        let l = r * 4 + c;
        let bit = 63 - (brow * 8 + within as usize) as u32;
        let set = state[l] >> bit & 1 == 1;
        let flash = (prev[l] ^ state[l]) >> bit & 1 == 1;
        let hot = active.contains(&l);
        let on = if hot { hex(0xd8fbff) } else { base.scale(0.75) };
        let mut col = if set { on } else { on.scale(0.08) };
        if flash {
            col = col.add(hex(WHITE).scale((1.0 - gf).powi(2) * 0.9));
        }
        Some((col, hot))
    };
    for py in 0..ph {
        let v = (py as f32 + 0.5 - top) / sv;
        if !(0.0..38.4).contains(&v) {
            continue;
        }
        let r = ((v / 9.6) as usize).min(3);
        let within = v - r as f32 * 9.6;
        if within >= 8.0 {
            continue;
        }
        let brow = within as usize;
        for px in 0..w {
            let xn = (px as f32 + 0.5 - cx) / rc;
            if xn.abs() >= 1.0 {
                continue;
            }
            let front = xn.asin();
            let light = (1.0 - xn * xn).sqrt();
            let c = match sample(front, r, brow) {
                Some((c, hot)) => c.scale(0.3 + 0.7 * light).add(if hot { hex(0x0a3040).scale(light) } else { Rgb::default() }),
                None => match sample(std::f32::consts::PI - front, r, brow) {
                    Some((c, _)) => c.scale(0.14),
                    None => continue,
                },
            };
            cv.set(px as i32, py as i32, c);
        }
    }
    for py in top as i32..(top + 38.4 * sv) as i32 {
        cv.add((cx - rc) as i32, py, base.scale(0.15));
        cv.add((cx + rc) as i32, py, base.scale(0.15));
    }
    let mut g = Grid::from_canvas(&cv, rows);
    let info = if done { label } else { format!("round {:>2}/12  ·  {label}", round + 1) };
    centered(&mut g, 2, &info, hex(INK));
    centered(&mut g, 3, &format!("rows v0-3, v4-7, v8-11, v12-15  ·  nonce {}  ·  {}", tk.hash, slowmo(tk.dur, 212.0)), hex(DIM));
    g
}

#[allow(clippy::too_many_arguments)]
fn column_fn(cv: &mut Canvas, sx: f32, sy: f32, tw: f32, th: f32, h: f32, top: Rgb, side: &dyn Fn(f32) -> Rgb) {
    for py in (sy - h - th).floor() as i32..=(sy + th).ceil() as i32 {
        for px in (sx - tw).floor() as i32..=(sx + tw).ceil() as i32 {
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
                if face > 0.75 { top.scale(1.3) } else { top }
            } else {
                side(((span - dy) / h).clamp(0.0, 0.9999)).scale(if dx < 0.0 { 0.95 } else { 0.62 })
            };
            cv.set(px, py, c);
        }
    }
}

pub fn blake_iso(w: usize, rows: usize, t: f32, segs: &'static [(usize, f32)]) -> Grid {
    let tk = Clock { segs }.at(t);
    let tr = blake2b_trace(&mining_input(tk.hash));
    let n = tr.ops.len();
    let i = (tk.step as usize).min(n);
    let f = tk.step.fract();
    let ph = rows * 2;
    let (fw, fh) = (w as f32, ph as f32);
    let mut cv = backdrop(w, ph, hex(0x0a3a52));
    let op = (i < n).then(|| tr.ops[i]);
    let lanes = op.map(|o| G_LANES[o.g]).unwrap_or([99; 4]);
    let h = fh * 0.4;
    let sp = 1.3;
    let tw = (fw * 0.075).min((fh * 0.84 - h) / (4.0 * sp));
    let th = tw * 0.5;
    let ox = fw * 0.5;
    let oy = fh * 0.95 - 2.0 * 3.0 * th * sp - th;
    let pos = |l: usize| -> (f32, f32) {
        let (x, y) = ((l % 4) as f32, (l / 4) as f32);
        (ox + (x - y) * tw * sp, oy + (x + y) * th * sp)
    };
    let in_g = |l: usize| lanes.contains(&l);
    let lift = |l: usize| if in_g(l) { h * 0.14 * if i % 12 == 0 { ease(f * 3.0) } else { 1.0 } } else { 0.0 };
    let base = hex(0x2ad4ff);
    let mut order: Vec<usize> = (0..16).collect();
    order.sort_by(|a, b| pos(*a).1.partial_cmp(&pos(*b).1).unwrap());
    for l in order {
        let (sx, sy) = pos(l);
        let active = op.is_some_and(|o| o.lane == l);
        let on = if active { op_color(op.unwrap().kind) } else if in_g(l) { base.lerp(hex(0xd8fbff), 0.35) } else { base.scale(0.6) };
        let top = if active { on } else { on.scale(0.5) };
        let side = |v: f32| -> Rgb {
            let (set, extra) = shown_bit(&tr, i, f, l, v * 64.0);
            if set { on } else { on.scale(0.09) }.add(hex(WHITE).scale(extra * 0.8))
        };
        column_fn(&mut cv, sx, sy - lift(l), tw * 0.84, th * 0.84, h, top, &side);
    }
    if let Some(o) = op {
        let tops: Vec<(f32, f32)> = lanes.iter().map(|&l| (pos(l).0, pos(l).1 - lift(l) - h - th * 0.2)).collect();
        for pair in tops.windows(2) {
            beam(&mut cv, pair[0], pair[1], 0.5, base.scale(0.18));
        }
        if let Some((from, to)) = op_flow(&o) {
            let (ai, bi) = (lanes.iter().position(|&x| x == from).unwrap(), lanes.iter().position(|&x| x == to).unwrap());
            let (a, b) = (tops[ai], tops[bi]);
            let e = ease(f);
            cv.glow(a.0 + (b.0 - a.0) * e, a.1 + (b.1 - a.1) * e, 1.6, op_color(o.kind));
        }
        if o.msg.is_some() {
            let b = tops[0];
            cv.glow(b.0, b.1 * ease(f), 1.5, hex(0xffd36b).scale(1.0 - f * 0.4));
        }
    } else {
        for l in 0..8 {
            let (a, b) = (pos(l), pos(l + 8));
            beam(&mut cv, (a.0, a.1 - h - th), (a.0, 0.0), 0.5, hex(0xffd36b).scale(0.15));
            beam(&mut cv, (b.0, b.1 - h - th), (a.0, a.1 - h - th), 0.5, hex(0xffd36b).scale(0.12));
        }
    }
    let mut g = Grid::from_canvas(&cv, rows);
    b2_header(&mut g, &tr, i, &tk);
    g
}
