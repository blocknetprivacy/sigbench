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

pub fn vole_tree(w: usize, rows: usize, t: f32) -> Grid {
    let ph = rows * 2;
    let (fw, fh) = (w as f32, ph as f32);
    let mut cv = backdrop(w, ph, hex(0x1b2f6b));
    const DEPTH: usize = 5;
    const PERIOD: f32 = 9.0;
    let cycle = (t / PERIOD) as u64;
    let lt = t % PERIOD;
    let hidden = (mix64(cycle + 7) % (1 << DEPTH)) as usize;
    let top = fh * 0.22;
    let bottom = fh * 0.86;
    let ly = |l: usize| top + (bottom - top) * l as f32 / DEPTH as f32;
    let lx = |l: usize, j: usize| fw * 0.08 + (fw * 0.84) * (j as f32 + 0.5) / (1usize << l) as f32;
    let seed = hex(0x7cf7d4);
    let leaf = hex(0x9fb4ff);
    let gold = hex(0xffd36b);
    let grow = (lt / 3.0).clamp(0.0, 1.0) * DEPTH as f32;
    let pick = ((lt - 3.6) / 1.4).clamp(0.0, 1.0);
    let open = ((lt - 5.2) / 1.0).clamp(0.0, 1.0);
    let on_path = |l: usize, j: usize| j == hidden >> (DEPTH - l);
    for l in 0..DEPTH {
        let p = (grow - l as f32).clamp(0.0, 1.0);
        if p <= 0.0 {
            break;
        }
        for j in 0..(1usize << l) {
            let a = (lx(l, j), ly(l));
            for c in 0..2 {
                let k = 2 * j + c;
                let b = (lx(l + 1, k), ly(l + 1));
                let e = ease(p);
                let tip = (a.0 + (b.0 - a.0) * e, a.1 + (b.1 - a.1) * e);
                let path = pick > 0.0 && on_path(l + 1, k) && on_path(l, j);
                let col = if path { gold.scale(0.25 + 0.6 * pick) } else { seed.scale(0.28) };
                cv.line(a, tip, col);
            }
        }
    }
    for l in 0..=DEPTH {
        if (l as f32) > grow + 0.01 {
            break;
        }
        for j in 0..(1usize << l) {
            let (x, y) = (lx(l, j), ly(l));
            let sibling_of_path = l > 0 && !on_path(l, j) && on_path(l - 1, j >> 1);
            let col = if l == DEPTH && j == hidden && pick > 0.5 {
                hex(0x2a2f45)
            } else if open > 0.0 && sibling_of_path {
                gold.scale(0.5 + 0.5 * open)
            } else if l == DEPTH {
                leaf.scale(0.7)
            } else {
                seed.scale(0.8)
            };
            let r = if l == 0 { 2.2 } else if l == DEPTH { 1.1 } else { 1.4 };
            cv.glow(x, y, r, col);
        }
    }
    if pick > 0.5 {
        let (x, y) = (lx(DEPTH, hidden), ly(DEPTH));
        cv.glow(x, y, 2.0 + 0.6 * (t * 5.0).sin().abs(), hex(0xff5fa2).scale(0.5));
    }
    let mut g = Grid::from_canvas(&cv, rows);
    centered(&mut g, 2, "VOLE commitment: one seed grows a tree of random values", hex(INK));
    let sub = if open > 0.0 {
        "the verifier gets every leaf but one  ·  11 trees  ·  the hidden leaves keep the spend secret"
    } else if pick > 0.0 {
        "a hash of the commitment picks one leaf to keep hidden"
    } else {
        "each leaf masks one copy of the witness: keys, amounts, which coin"
    };
    centered(&mut g, 3, sub, hex(DIM));
    let y = ((ly(DEPTH) / 2.0) as usize + 2).min(rows.saturating_sub(2));
    if open > 0.0 {
        centered(&mut g, y, "then QuickSilver checks every AES round and every sum on the masked values", hex(DIM));
    }
    g
}

pub fn set_select(w: usize, rows: usize, t: f32) -> Grid {
    let ph = rows * 2;
    let (fw, fh) = (w as f32, ph as f32);
    let mut cv = backdrop(w, ph, hex(0x0f4a3a));
    const PERIOD: f32 = 8.0;
    let cycle = (t / PERIOD) as u64;
    let lt = t % PERIOD;
    let (x0, x1) = (fw * 0.12, fw * 0.88);
    let (y0, y1) = (fh * 0.24, fh * 0.86);
    let cols = ((x1 - x0) / 3.0) as usize;
    let rws = ((y1 - y0) / 3.0) as usize;
    let tc = (mix64(cycle * 2 + 1) % cols.max(1) as u64) as usize;
    let tr = (mix64(cycle * 2 + 2) % rws.max(1) as u64) as usize;
    let cell = |c: usize, r: usize| (x0 + c as f32 * 3.0 + 1.5, y0 + r as f32 * 3.0 + 1.5);
    let base = hex(0x2ef2c3);
    let reveal = (lt / 1.2).clamp(0.0, 1.0);
    for r in 0..rws {
        for c in 0..cols {
            if (noise(c, r * 7 + 3) * 0.5 + (r as f32 / rws as f32) * 0.5) > reveal {
                continue;
            }
            let (x, y) = cell(c, r);
            let b = 0.10 + 0.10 * noise(c * 3 + cycle as usize, r);
            cv.add(x as i32, y as i32, base.scale(b));
        }
    }
    let lock = ((lt - 1.4) / 2.6).clamp(0.0, 1.0);
    let e = ease(lock);
    let row_y = cell(0, tr).1 * e + y0 * (1.0 - e) + (1.0 - e) * (y1 - y0) * 0.5 * (1.0 + (lt * 2.3).sin());
    let col_x = cell(tc, 0).0 * e + x0 * (1.0 - e) + (1.0 - e) * (x1 - x0) * 0.5 * (1.0 + (lt * 1.7).cos());
    if lt > 1.2 {
        let band = hex(0xc58bff).scale(0.22);
        let band2 = hex(0xffb347).scale(0.22);
        cv.line((x0, row_y), (x1, row_y), band);
        cv.line((col_x, y0), (col_x, y1), band2);
    }
    let hit = ((lt - 4.2) / 0.8).clamp(0.0, 1.0);
    if hit > 0.0 {
        let (x, y) = cell(tc, tr);
        cv.glow(x, y, 1.5 + 1.5 * hit + 0.4 * (t * 6.0).sin().abs(), hex(0xffe08a).scale(0.8 * hit));
    }
    let fade = ((lt - 6.4) / 1.2).clamp(0.0, 1.0);
    if fade > 0.0 {
        for px in cv.px.iter_mut() {
            *px = px.scale(1.0 - 0.6 * fade);
        }
    }
    let mut g = Grid::from_canvas(&cv, rows);
    centered(&mut g, 2, "the anonymity set: 2^20 = 1,048,576 coins", hex(INK));
    let sub = if hit > 0.0 {
        "the proof shows a coin in the set was opened  ·  never which one"
    } else if lt > 1.2 {
        "two 45-bit selectors, one per axis, cross at the coin you spend"
    } else {
        "every coin is a hidden commitment to its owner and amount"
    };
    centered(&mut g, 3, sub, hex(DIM));
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

#[cfg(test)]
mod tests {
    #[test]
    fn new_scenes_draw_at_every_phase() {
        for (w, rows) in [(80usize, 24usize), (200, 60), (40, 12)] {
            let mut t = 0.0f32;
            while t < 40.0 {
                let a = super::vole_tree(w, rows, t);
                let b = super::set_select(w, rows, t);
                assert_eq!((a.w, b.w), (w, w));
                t += 0.37;
            }
        }
    }
}
