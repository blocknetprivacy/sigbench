#![allow(dead_code)]

pub mod address;

use crate::gfx::{Cell, Grid, Rgb};

pub const SS: usize = 2;

#[derive(Clone, Copy, Default, Debug)]
pub struct C3(pub f32, pub f32, pub f32);

impl C3 {
    pub fn hex(h: u32) -> C3 {
        let f = |v: u32| (v as f32 / 255.0).powf(2.2);
        C3(f((h >> 16) & 255), f((h >> 8) & 255), f(h & 255))
    }
    pub fn s(self, k: f32) -> C3 {
        C3(self.0 * k, self.1 * k, self.2 * k)
    }
    pub fn add(self, o: C3) -> C3 {
        C3(self.0 + o.0, self.1 + o.1, self.2 + o.2)
    }
    pub fn mix(self, o: C3, t: f32) -> C3 {
        let t = t.clamp(0.0, 1.0);
        C3(self.0 + (o.0 - self.0) * t, self.1 + (o.1 - self.1) * t, self.2 + (o.2 - self.2) * t)
    }
    pub fn rgb(self) -> Rgb {
        Rgb(self.0.clamp(0.0, 1.0), self.1.clamp(0.0, 1.0), self.2.clamp(0.0, 1.0))
    }
}

pub mod pal {
    use super::C3;
    pub fn green() -> C3 { C3::hex(0xaaff00) }
    pub fn teal() -> C3 { C3::hex(0x2ef2c3) }
    pub fn cyan() -> C3 { C3::hex(0x5fd8ff) }
    pub fn blue() -> C3 { C3::hex(0x3b6cff) }
    pub fn violet() -> C3 { C3::hex(0xa66bff) }
    pub fn magenta() -> C3 { C3::hex(0xff4fb0) }
    pub fn gold() -> C3 { C3::hex(0xffc65a) }
    pub fn red() -> C3 { C3::hex(0xff3b4e) }
    pub fn white() -> C3 { C3(1.0, 1.0, 1.0) }
    pub fn ink() -> C3 { C3::hex(0xe8ecf4) }
    pub fn dim() -> C3 { C3::hex(0x6b7590) }
}

pub fn ease(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    t * t * (3.0 - 2.0 * t)
}

pub fn ease_out(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    1.0 - (1.0 - t).powi(3)
}

pub fn ease_in(t: f32) -> f32 {
    let t = t.clamp(0.0, 1.0);
    t * t * t
}

pub fn phase(t: f32, a: f32, b: f32) -> f32 {
    ((t - a) / (b - a)).clamp(0.0, 1.0)
}

pub fn hash32(mut x: u64) -> u64 {
    x ^= x >> 33;
    x = x.wrapping_mul(0xff51afd7ed558ccd);
    x ^= x >> 33;
    x = x.wrapping_mul(0xc4ceb9fe1a85ec53);
    x ^ (x >> 33)
}

pub fn rnd(i: u64) -> f32 {
    (hash32(i) >> 40) as f32 / (1u64 << 24) as f32
}

pub struct Fb {
    pub cols: usize,
    pub rows: usize,
    pub w: usize,
    pub h: usize,
    pub px: Vec<C3>,
}

impl Fb {
    pub fn new(cols: usize, rows: usize, bg: C3) -> Fb {
        let (w, h) = (cols * SS, rows * 2 * SS);
        Fb { cols, rows, w, h, px: vec![bg; w * h] }
    }

    pub fn width(&self) -> f32 {
        self.cols as f32
    }

    pub fn height(&self) -> f32 {
        (self.rows * 2) as f32
    }

    pub fn sky(&mut self, top: C3, bottom: C3, glow: C3, gx: f32, gy: f32) {
        let (w, h) = (self.w as f32, self.h as f32);
        for y in 0..self.h {
            let v = y as f32 / h;
            let base = top.mix(bottom, v);
            for x in 0..self.w {
                let dx = (x as f32 / w - gx) * (w / h) * 0.5;
                let dy = v - gy;
                let r2 = dx * dx + dy * dy;
                self.px[y * self.w + x] = base.add(glow.s((-r2 * 6.0).exp()));
            }
        }
    }

    #[inline]
    pub fn add_px(&mut self, x: i32, y: i32, c: C3) {
        if x >= 0 && y >= 0 && (x as usize) < self.w && (y as usize) < self.h {
            let p = &mut self.px[y as usize * self.w + x as usize];
            *p = p.add(c);
        }
    }

    pub fn splat(&mut self, x: f32, y: f32, r: f32, c: C3) {
        let (sx, sy, sr) = (x * SS as f32, y * SS as f32, (r * SS as f32).max(0.6));
        let reach = (sr * 2.4).ceil() as i32;
        let (cx, cy) = (sx.floor() as i32, sy.floor() as i32);
        let inv = 1.0 / (sr * sr);
        for yy in cy - reach..=cy + reach {
            for xx in cx - reach..=cx + reach {
                let d2 = ((xx as f32 + 0.5 - sx).powi(2) + (yy as f32 + 0.5 - sy).powi(2)) * inv;
                if d2 < 5.8 {
                    self.add_px(xx, yy, c.s((-d2).exp()));
                }
            }
        }
    }

    pub fn line(&mut self, a: (f32, f32), b: (f32, f32), r: f32, c: C3) {
        let len = ((b.0 - a.0).powi(2) + (b.1 - a.1).powi(2)).sqrt();
        let n = ((len * SS as f32 / (r * SS as f32).max(0.5) * 1.6) as usize).max(1);
        let k = c.s(1.6 / (n as f32 / len.max(0.01)).max(1.0));
        for i in 0..=n {
            let t = i as f32 / n as f32;
            self.splat(a.0 + (b.0 - a.0) * t, a.1 + (b.1 - a.1) * t, r, k);
        }
    }

    pub fn ring(&mut self, x: f32, y: f32, rad: f32, r: f32, c: C3) {
        let n = ((rad * 6.0) as usize).clamp(24, 720);
        for i in 0..n {
            let a = i as f32 / n as f32 * std::f32::consts::TAU;
            self.splat(x + a.cos() * rad, y + a.sin() * rad * 0.5 * 2.0, r, c.s(1.0 / (n as f32 / (rad * 4.0)).max(1.0)));
        }
    }

    pub fn fade(&mut self, k: f32) {
        for p in self.px.iter_mut() {
            *p = p.s(k);
        }
    }

    pub fn finish(&self, bloom: f32, vignette: f32, grain_seed: u64) -> Grid {
        let (w, h) = (self.w, self.h);
        let bw = w.div_ceil(4);
        let bh = h.div_ceil(4);
        let mut small = vec![C3::default(); bw * bh];
        for y in 0..h {
            for x in 0..w {
                let p = self.px[y * w + x];
                let lum = 0.2126 * p.0 + 0.7152 * p.1 + 0.0722 * p.2;
                let k = ((lum - 0.55).max(0.0) / lum.max(1e-4)).min(1.0);
                let q = &mut small[(y / 4) * bw + x / 4];
                *q = q.add(p.s(k / 16.0));
            }
        }
        for _ in 0..3 {
            blur(&mut small, bw, bh, 2);
        }
        let mut g = Grid::new(self.cols, self.rows, Rgb::default());
        let (fw, fh) = (self.cols as f32, (self.rows * 2) as f32);
        for row in 0..self.rows {
            for col in 0..self.cols {
                let mut half = [C3::default(); 2];
                for (hi, out) in half.iter_mut().enumerate() {
                    let py = row * 2 + hi;
                    let mut acc = C3::default();
                    for sy in 0..SS {
                        for sx in 0..SS {
                            let x = col * SS + sx;
                            let y = py * SS + sy;
                            let b = sample(&small, bw, bh, x as f32 / 4.0, y as f32 / 4.0);
                            acc = acc.add(self.px[y * w + x].add(b.s(bloom)));
                        }
                    }
                    let mut c = acc.s(1.0 / (SS * SS) as f32);
                    let (u, v) = (col as f32 / fw - 0.5, py as f32 / fh - 0.5);
                    let vig = 1.0 - vignette * (u * u * 1.4 + v * v * 1.8);
                    c = c.s(vig.max(0.0));
                    let n = (rnd(grain_seed ^ ((py * 9973 + col) as u64)) - 0.5) * 0.0025;
                    *out = tonemap(c).add(C3(n, n, n));
                }
                g.c[row * self.cols + col] = Cell { ch: '▀', fg: half[0].rgb(), bg: half[1].rgb() };
            }
        }
        g
    }
}

fn tonemap(c: C3) -> C3 {
    let f = |x: f32| {
        let x = x.max(0.0) * 0.9;
        ((x * (2.51 * x + 0.03)) / (x * (2.43 * x + 0.59) + 0.14)).clamp(0.0, 1.0)
    };
    C3(f(c.0), f(c.1), f(c.2))
}

fn blur(buf: &mut [C3], w: usize, h: usize, r: usize) {
    let mut tmp = buf.to_vec();
    for y in 0..h {
        for x in 0..w {
            let mut acc = C3::default();
            let mut n = 0.0;
            for k in x.saturating_sub(r)..=(x + r).min(w - 1) {
                acc = acc.add(buf[y * w + k]);
                n += 1.0;
            }
            tmp[y * w + x] = acc.s(1.0 / n);
        }
    }
    for y in 0..h {
        for x in 0..w {
            let mut acc = C3::default();
            let mut n = 0.0;
            for k in y.saturating_sub(r)..=(y + r).min(h - 1) {
                acc = acc.add(tmp[k * w + x]);
                n += 1.0;
            }
            buf[y * w + x] = acc.s(1.0 / n);
        }
    }
}

fn sample(buf: &[C3], w: usize, h: usize, x: f32, y: f32) -> C3 {
    let x = (x - 0.5).clamp(0.0, (w - 1) as f32);
    let y = (y - 0.5).clamp(0.0, (h - 1) as f32);
    let (x0, y0) = (x.floor() as usize, y.floor() as usize);
    let (x1, y1) = ((x0 + 1).min(w - 1), (y0 + 1).min(h - 1));
    let (fx, fy) = (x - x0 as f32, y - y0 as f32);
    let a = buf[y0 * w + x0].mix(buf[y0 * w + x1], fx);
    let b = buf[y1 * w + x0].mix(buf[y1 * w + x1], fx);
    a.mix(b, fy)
}

pub struct Cam {
    pub yaw: f32,
    pub pitch: f32,
    pub dist: f32,
    pub fov: f32,
    pub cx: f32,
    pub cy: f32,
    pub scale: f32,
}

impl Cam {
    pub fn project(&self, p: [f32; 3]) -> Option<(f32, f32, f32)> {
        let (sy, cy) = self.yaw.sin_cos();
        let (sp, cp) = self.pitch.sin_cos();
        let x = p[0] * cy - p[2] * sy;
        let z = p[0] * sy + p[2] * cy;
        let y = p[1] * cp - z * sp;
        let z = p[1] * sp + z * cp + self.dist;
        if z < 0.1 {
            return None;
        }
        let k = self.fov / z;
        Some((self.cx + x * k * self.scale, self.cy + y * k * self.scale, z))
    }
}

pub fn text(g: &mut Grid, x: usize, y: usize, s: &str, c: C3) {
    for (i, ch) in s.chars().enumerate() {
        if let Some(cell) = g.get(x + i, y) {
            let under = if cell.ch == '▀' { cell.fg.lerp(cell.bg, 0.5) } else { cell.bg };
            cell.bg = under;
            cell.ch = ch;
            cell.fg = c.rgb();
        }
    }
}

pub fn text_center(g: &mut Grid, y: usize, s: &str, c: C3) {
    let n = s.chars().count();
    text(g, g.w.saturating_sub(n) / 2, y, s, c);
}

pub fn tile(g: &mut Grid, x: usize, y: usize, ch: char, fg: C3, bg: C3) {
    if let Some(cell) = g.get(x, y) {
        cell.ch = ch;
        cell.fg = fg.rgb();
        cell.bg = bg.rgb();
    }
}

pub fn reveal(s: &str, p: f32) -> String {
    let n = s.chars().count();
    s.chars().take((p.clamp(0.0, 1.0) * n as f32).round() as usize).collect()
}

#[cfg(test)]
mod tests {
    use crate::gfx::Grid;

    fn ppm(g: &Grid, path: &str) {
        let (w, h) = (g.w * 4, g.h * 8);
        let mut buf = format!("P6 {w} {h} 255\n").into_bytes();
        for y in 0..h {
            for x in 0..w {
                let c = g.c[(y / 8) * g.w + x / 4];
                let top = (y % 8) < 4;
                let glyph = c.ch != ' ' && c.ch != '▀' && (1..=2).contains(&(x % 4)) && (2..=5).contains(&(y % 8));
                let col = if c.ch == '▀' { if top { c.fg } else { c.bg } } else if glyph { c.fg } else { c.bg };
                let (r, gg, b) = col.bytes();
                buf.extend([r, gg, b]);
            }
        }
        std::fs::write(path, buf).unwrap();
    }

    #[test]
    fn address_scenes_render_fast() {
        let w = crate::address::wallet(&[5u8; 32]);
        let dir = std::env::var("FRAMES").ok();
        let scenes: [(&str, fn(usize, usize, f32, &crate::address::Wallet) -> Grid); 3] =
            [("squeeze", super::address::squeeze), ("typo", super::address::typo), ("registry", super::address::registry)];
        for (name, f) in scenes {
            let start = std::time::Instant::now();
            let mut frames = 0;
            let mut t = 0.0f32;
            while t < 15.0 {
                let g = f(180, 50, t, &w);
                assert_eq!((g.w, g.h), (180, 50));
                if let Some(d) = &dir {
                    if (t * 2.0).fract() < 0.01 {
                        ppm(&g, &format!("{d}/{name}-{:04.1}.ppm", t));
                    }
                }
                frames += 1;
                t += 0.25;
            }
            let ms = start.elapsed().as_secs_f64() * 1000.0 / frames as f64;
            eprintln!("{name}: {ms:.1} ms per frame at 180x50");
        }
    }
}
