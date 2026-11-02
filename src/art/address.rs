use super::*;
use crate::address::{self, Wallet};
use crate::gfx::Grid;
use std::f32::consts::TAU;

fn hexs(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn addr_colors(i: usize, n: usize) -> C3 {
    if i >= n - 6 {
        pal::gold()
    } else {
        pal::cyan().mix(pal::white(), 0.35)
    }
}

fn byte_color(b: u8, owner: bool) -> C3 {
    if owner {
        pal::magenta().mix(pal::gold(), b as f32 / 255.0)
    } else {
        pal::blue().mix(pal::teal(), b as f32 / 255.0)
    }
}

fn address_row(g: &mut Grid, y: usize, addr: &str, shown: f32, t: f32, glow: f32) {
    let n = addr.chars().count();
    let x0 = g.w.saturating_sub(n) / 2;
    let k = (shown * n as f32) as usize;
    for (i, ch) in addr.chars().enumerate() {
        if i >= k {
            break;
        }
        let age = (shown * n as f32 - i as f32).clamp(0.0, 6.0);
        let flash = (1.0 - age / 1.5).max(0.0);
        let sweep = (-((i as f32 - (t * 22.0) % (n as f32 + 30.0)).powi(2)) / 18.0).exp() * glow;
        let c = addr_colors(i, n).mix(pal::white(), flash * 0.8 + sweep * 0.6);
        let bg = addr_colors(i, n).s(0.10 + 0.25 * flash + 0.25 * sweep);
        tile(g, x0 + i, y, ch, c, bg);
    }
}

pub fn squeeze(cols: usize, rows: usize, t: f32, w: &Wallet) -> Grid {
    const LOOP: f32 = 14.0;
    let t = t % LOOP;
    let mut fb = Fb::new(cols, rows, C3::default());
    let (fw, fh) = (fb.width(), fb.height());
    fb.sky(C3::hex(0x02030a), C3::hex(0x060312), C3::hex(0x16245a).s(0.35), 0.5, 0.42);
    let cam = Cam {
        yaw: 0.25 * (t * 0.22).sin(),
        pitch: 0.62 + 0.04 * (t * 0.3).sin(),
        dist: 4.6,
        fov: 2.0,
        cx: fw * 0.5,
        cy: fh * 0.60,
        scale: fw * 0.34,
    };
    for i in 0..260u64 {
        let x = rnd(i * 3) * fw;
        let y = rnd(i * 3 + 1) * fh * 0.55;
        let tw = 0.5 + 0.5 * (t * (0.7 + rnd(i * 3 + 2) * 2.5) + i as f32).sin();
        fb.splat(x, y, 0.3, C3(0.6, 0.7, 1.0).s(0.035 * tw * (1.0 - y / (fh * 0.55))));
    }

    let kem = w.kem_key.len();
    let total = kem + w.owner_key.len();
    let lift_a = 2.0;
    let lift_b = 6.2;
    let bang = 6.6;
    let center = [0.0f32, -1.05, 0.15];
    let heat = phase(t, lift_a, bang);
    let mut absorbed = 0usize;

    for i in 0..total {
        let owner = i >= kem;
        let b = if owner { w.owner_key[i - kem] } else { w.kem_key[i] };
        let bf = b as f32 / 255.0;
        let home = if owner {
            let j = i - kem;
            let (gx, gy) = ((j % 8) as f32, (j / 8) as f32);
            let a = t * 0.8;
            let lx = (gx - 3.5) * 0.075;
            [1.75 + lx * a.cos(), -0.75 + (gy - 1.5) * 0.075 + 0.05 * (t * 1.4).sin(), 0.25 + lx * a.sin()]
        } else {
            let (gx, gy) = ((i % 37) as f32, (i / 37) as f32);
            let x = (gx - 18.0) * 0.072;
            let z = (gy - 15.5) * 0.072;
            let wave = 0.06 * (gx * 0.45 + t * 2.1).sin() * (gy * 0.35 - t * 1.4).cos() + 0.03 * (bf - 0.5);
            [x, wave, z]
        };
        let order = if owner {
            0.93 + 0.07 * ((i - kem) as f32 / 32.0)
        } else {
            let (gx, gy) = ((i % 37) as f32, (i / 37) as f32);
            let r = ((gx - 18.0).powi(2) + (gy - 15.5).powi(2)).sqrt() / 24.0;
            (1.0 - r.min(1.0)) * 0.7 + 0.3 * rnd(i as u64 + 77)
        };
        let start = lift_a + order * (lift_b - lift_a - 1.1);
        let p = phase(t, start, start + 1.1);
        if p >= 1.0 || t >= bang {
            absorbed += 1;
            continue;
        }
        let appear = ease(phase(t, 0.1 + (i % 37) as f32 * 0.01 + (i / 37) as f32 * 0.02, 0.9 + (i / 37) as f32 * 0.02));
        let at = |q: f32| -> [f32; 3] {
            let e = ease_in(q);
            let ang0 = (home[2] - center[2]).atan2(home[0] - center[0]);
            let r0 = ((home[0] - center[0]).powi(2) + (home[2] - center[2]).powi(2)).sqrt();
            let ang = ang0 + e * 8.5;
            let r = r0 * (1.0 - e).powf(1.3);
            let spun = [center[0] + ang.cos() * r, home[1] + (center[1] - home[1]) * e.powf(0.6), center[2] + ang.sin() * r];
            let k = ease(q * 3.0);
            [home[0] + (spun[0] - home[0]) * k, home[1] + (spun[1] - home[1]) * k, home[2] + (spun[2] - home[2]) * k]
        };
        let pos = at(p);
        let Some((x, y, z)) = cam.project(pos) else { continue };
        let depth = (4.6 / z).powi(2);
        let col = byte_color(b, owner);
        let base = if owner { 0.7 } else { 0.22 + 0.75 * bf * bf };
        let bright = base + 0.9 * ease(p);
        fb.splat(x, y, 0.32 + 0.25 * ease(p) + if owner { 0.12 } else { 0.0 }, col.s(bright * depth * appear));
        if p > 0.02 {
            if let Some((px, py, _)) = cam.project(at((p - 0.16).max(0.0))) {
                fb.line((px, py), (x, y), 0.22, col.s(0.5 * depth * ease(p)));
            }
        }
    }

    if let Some((ox, oy, _)) = cam.project(center) {
        let live = if t < bang { heat } else { 0.0 };
        let spin = t * 5.0;
        for k in 0..4 {
            let rr = (0.9 + k as f32 * 0.55) * (0.3 + 0.9 * live);
            for s in 0..120 {
                let a = spin * (1.0 + k as f32 * 0.25) + s as f32 / 120.0 * TAU;
                let wob = 1.0 + 0.08 * (a * 3.0 + t * 4.0).sin();
                let lift = -(k as f32) * 2.2 * live;
                fb.splat(ox + a.cos() * rr * 3.2 * wob, oy + lift + a.sin() * rr * 0.9 * wob, 0.3, pal::violet().mix(pal::cyan(), k as f32 / 3.0).s(0.09 * live));
            }
        }
        fb.splat(ox, oy, 0.8 + 2.4 * live, pal::violet().mix(pal::white(), live * 0.7).s(0.25 + 0.9 * live));
        let b = phase(t, bang, bang + 1.3);
        if b > 0.0 && b < 1.0 {
            fb.splat(ox, oy, 2.0 + 26.0 * ease_out(b), pal::white().s(2.2 * (1.0 - b).powi(3)));
            for (k, col) in [(0.0, pal::cyan()), (0.12, pal::violet()), (0.24, pal::magenta())] {
                let bb = (b - k).max(0.0);
                let rad = ease_out(bb) * fw * 0.6;
                for s in 0..420 {
                    let a = s as f32 / 420.0 * TAU;
                    fb.splat(ox + a.cos() * rad, oy + a.sin() * rad * 0.42, 0.5, col.s(0.55 * (1.0 - bb).powi(2)));
                }
            }
        }
        if t > bang {
            let age = t - bang;
            for i in 0..420u64 {
                let a = rnd(i * 5) * TAU;
                let sp = 0.25 + rnd(i * 5 + 1) * 0.9;
                let dist = (age * 6.0).min(1.0) * sp * fw * 0.45 + age * sp * 2.0;
                let x = ox + a.cos() * dist;
                let y = oy + a.sin() * dist * 0.45 + age * age * 1.2 * rnd(i * 5 + 2);
                let life = (1.0 - age / (5.0 + 3.0 * rnd(i * 5 + 3))).max(0.0);
                let tw = 0.6 + 0.4 * (t * (3.0 + 6.0 * rnd(i * 5 + 4)) + i as f32).sin();
                let col = pal::cyan().mix(pal::violet(), rnd(i)).mix(pal::gold(), rnd(i + 9) * 0.5);
                fb.splat(x, y, 0.3, col.s(0.5 * life * tw));
            }
        }
        let beads = phase(t, bang + 0.2, bang + 1.2);
        let fly = phase(t, 8.3, 10.6);
        if beads > 0.0 {
            let n = w.address.chars().count() as f32;
            let row_y = fh * 0.82;
            for (j, &hb) in w.hash.iter().enumerate() {
                let a = j as f32 / 32.0 * TAU + t * 0.7;
                let ring_r = ease_out(beads) * fh * 0.20;
                let ring = (ox + a.cos() * ring_r * 2.2, oy + a.sin() * ring_r * 0.7);
                let target = ((fw - n) / 2.0 + (j as f32 + 0.5) * (n - 6.0) / 32.0, row_y);
                let f = ease((fly - j as f32 * 0.015) / 0.55);
                if f >= 1.0 {
                    continue;
                }
                let arc = (ring.0 + (target.0 - ring.0) * f, ring.1 + (target.1 - ring.1) * f - (f * (1.0 - f)) * fh * 0.25);
                let col = byte_color(hb, false).mix(pal::gold(), 0.55);
                let tw = 0.8 + 0.2 * (t * 7.0 + j as f32).sin();
                fb.splat(arc.0, arc.1, 0.7, col.s(1.4 * tw));
                fb.splat(arc.0, arc.1, 2.2, col.s(0.12 * tw));
            }
        }
    }

    let shown_px = phase(t, 8.6, 11.0);
    if shown_px > 0.0 {
        let n = w.address.chars().count();
        let x0 = (cols.saturating_sub(n) / 2) as f32;
        let ry = (((fh * 0.82) / 2.0) as usize * 2) as f32 + 1.0;
        let k = (shown_px * n as f32) as usize;
        for i in 0..k.min(n) {
            let c = addr_colors(i, n);
            let breathe = 0.7 + 0.3 * (t * 2.0 + i as f32 * 0.3).sin();
            fb.splat(x0 + i as f32 + 0.5, ry, 1.6, c.s(0.10 * breathe));
            fb.splat(x0 + i as f32 + 0.5, ry + 2.5, 1.0, c.s(0.05 * breathe));
        }
        let land = shown_px * n as f32;
        let li = land as usize;
        if li < n {
            for s in 0..24u64 {
                let a = rnd(s + li as u64 * 31) * TAU;
                let r = rnd(s * 3 + li as u64) * 4.0 * land.fract();
                fb.splat(x0 + li as f32 + 0.5 + a.cos() * r * 1.5, ry + a.sin() * r, 0.3, addr_colors(li, n).s(0.6 * (1.0 - land.fract())));
            }
        }
    }
    let fade = (1.0 - phase(t, LOOP - 0.7, LOOP)) * ease(phase(t, 0.0, 0.4));
    fb.fade(fade);
    let mut g = fb.finish(0.8, 0.6, (t * 30.0) as u64);

    text_center(&mut g, 1, "Y O U R   A D D R E S S", pal::ink().s(fade));
    let sub = if t < lift_a {
        "a real ML-KEM-768 key (1,184 bytes, blue) and a real owner key (32 bytes, pink), made just now"
    } else if t < bang {
        "SHA3-256 pulls in every byte"
    } else if t < 8.3 {
        "1,216 bytes became 32"
    } else {
        "bech32m writes those 32 bytes as 58 characters"
    };
    text_center(&mut g, 3, sub, pal::dim().mix(pal::ink(), 0.35).s(fade));
    if (lift_a..bang).contains(&t) {
        let s = format!("bytes absorbed  {:>5} / {}", absorbed, total);
        text_center(&mut g, rows.saturating_sub(4), &s, pal::violet().mix(pal::ink(), 0.5).s(fade));
    }
    if (bang + 0.6..8.6).contains(&t) {
        text_center(&mut g, rows.saturating_sub(4), &hexs(&w.hash), pal::gold().s(fade * phase(t, bang + 0.6, bang + 1.0)));
    }
    let row = ((fh * 0.82) / 2.0) as usize;
    let shown = phase(t, 8.6, 11.0);
    if shown > 0.0 {
        address_row(&mut g, row, &w.address, shown, t, phase(t, 11.0, 11.6));
    }
    if t > 11.2 {
        text_center(&mut g, row + 2, "white: hash of your keys   gold: checksum", pal::dim().mix(pal::ink(), 0.4).s(fade));
    }
    g
}

pub fn typo(cols: usize, rows: usize, t: f32, w: &Wallet) -> Grid {
    const LOOP: f32 = 13.0;
    let t = t % LOOP;
    let addr: Vec<char> = w.address.chars().collect();
    let n = addr.len();
    let cycle = 0u64;
    let pos = hash32(cycle + 11) as usize % (n - 8);
    let correct = addr[pos];
    let wrong = {
        let c = address::CHARSET[(address::CHARSET.iter().position(|&x| x as char == correct).unwrap() + 7) % 32] as char;
        c
    };
    let roll_out = phase(t, 2.0, 3.0);
    let roll_back = phase(t, 6.6, 7.4);
    let broken = roll_out >= 1.0 && roll_back < 1.0;
    let mut shown_addr = addr.clone();
    if roll_out > 0.0 && roll_back < 1.0 {
        let spin = if roll_out < 1.0 { roll_out } else { roll_back };
        let target = if roll_out < 1.0 { wrong } else { correct };
        shown_addr[pos] = if spin < 1.0 && spin > 0.0 {
            address::CHARSET[(hash32((t * 30.0) as u64) % 32) as usize] as char
        } else {
            target
        };
    }
    let as_string: String = shown_addr.iter().collect();
    let valid = address::decode(&as_string).is_some();
    let sweep1 = phase(t, 3.4, 5.4);
    let sweep2 = phase(t, 7.8, 9.8);
    let verdict_bad = t >= 5.4 && t < 7.4;
    let verdict_good = t >= 9.8;

    let mut fb = Fb::new(cols, rows, C3::default());
    let (fw, fh) = (fb.width(), fb.height());
    let flash_bad = if verdict_bad { (1.0 - phase(t, 5.4, 6.4)).max(0.0) } else { 0.0 };
    let flash_good = if verdict_good { (1.0 - phase(t, 9.8, 11.0)).max(0.0) } else { 0.0 };
    let mood = if verdict_bad { pal::red() } else if verdict_good { pal::green() } else { pal::blue() };
    let flash = flash_bad.max(flash_good);
    fb.sky(C3::hex(0x010208), C3::hex(0x04030c), mood.s(0.03 + 0.10 * flash + if verdict_bad { 0.02 } else { 0.0 }), 0.5, 0.5);

    let line_w = (n + n / 4 + 2) as f32;
    let two = line_w + 4.0 > fw;
    let row_px = (rows / 2) as f32 * 2.0 + 1.0;
    let left = if two { (fw - line_w / 2.0) / 2.0 } else { (fw - line_w) / 2.0 };
    let right = fw - left;
    let cyc = |i: usize| -> f32 { i as f32 };
    let _ = cyc;

    for i in 0..340u64 {
        let x = rnd(i * 7) * fw;
        let depth = rnd(i * 7 + 1);
        let y = (rnd(i * 7 + 2) * fh + t * (2.0 + depth * 6.0)) % fh;
        fb.splat(x, y, 0.25 + depth * 0.2, pal::cyan().mix(pal::violet(), rnd(i)).s(0.04 + 0.05 * depth));
    }

    for (sw, colr) in [(sweep1, if valid { pal::green() } else { pal::red() }), (sweep2, pal::green())] {
        if sw > 0.0 && sw < 1.0 {
            let x = left + (right - left) * sw;
            let laser = if colr.0 > colr.1 { pal::cyan() } else { pal::cyan().mix(pal::green(), 0.5) };
            fb.line((x, 0.0), (x, fh), 0.35, laser.s(0.35));
            fb.splat(x, row_px, 3.5, laser.s(0.6));
            for k in 0..40u64 {
                let seed = k + (t * 40.0) as u64 * 97;
                let a = -std::f32::consts::FRAC_PI_2 + (rnd(seed) - 0.5) * 2.4;
                let life = rnd(seed + 3);
                let r = life * 9.0;
                fb.splat(x - r * 0.6 + a.cos() * r * 0.3, row_px + a.sin() * r, 0.3, laser.mix(pal::white(), 0.5).s(0.7 * (1.0 - life)));
            }
        }
    }
    if roll_out > 0.0 && roll_back < 1.0 {
        let p_total = if two { 0.0 } else { 0.0 };
        let _ = p_total;
    }
    if flash_bad > 0.0 {
        let b = 1.0 - flash_bad;
        for (k, col) in [(0.0f32, pal::red()), (0.1, pal::magenta())] {
            let bb = (b - k).max(0.0);
            let rad = ease_out(bb) * fw * 0.55;
            for s in 0..360 {
                let a = s as f32 / 360.0 * TAU;
                fb.splat(right - 4.0 + a.cos() * rad, row_px + a.sin() * rad * 0.45, 0.5, col.s(0.6 * (1.0 - bb).powi(2)));
            }
        }
        fb.splat(right - 4.0, row_px, 2.0 + 10.0 * b, pal::red().s(1.2 * flash_bad));
    }
    if verdict_good {
        let b = phase(t, 9.8, 12.0);
        for i in 0..260u64 {
            let a = rnd(i) * TAU;
            let sp = 0.25 + rnd(i + 999) * 0.75;
            let r = ease_out(b) * fw * 0.5 * sp;
            let fall = b * b * 8.0 * rnd(i + 5);
            fb.splat(fw * 0.5 + a.cos() * r * 1.3, row_px + a.sin() * r * 0.55 + fall, 0.4, pal::green().mix(pal::gold(), rnd(i + 7)).s(0.9 * (1.0 - b)));
        }
        let lock = phase(t, 9.8, 10.6);
        for k in 0..6 {
            let x = right - 6.0 + k as f32 + 0.5;
            fb.ring(x, row_px, 0.5 + 3.0 * (1.0 - lock), 0.25, pal::gold().s(0.4 * (1.0 - lock)));
        }
    }
    let mut g_shake = 0i32;
    if flash_bad > 0.4 {
        g_shake = ((t * 55.0).sin() * 2.0) as i32;
    }
    let fade = 1.0 - phase(t, LOOP - 0.6, LOOP);
    fb.fade(fade);
    let mut g = fb.finish(0.9, 0.55, (t * 30.0) as u64);

    text_center(&mut g, 1, "O N E   W R O N G   C H A R A C T E R", pal::ink().s(fade));
    let sub = if t < 2.0 {
        "this is the real address from the last scene"
    } else if t < 3.4 {
        "one character changes"
    } else if t < 5.4 {
        "the wallet recomputes the checksum"
    } else if t < 7.4 {
        "rejected: no such address. The coins cannot go to a typo."
    } else if t < 9.8 {
        "the character goes back, and the wallet checks again"
    } else {
        "valid. Any 1 wrong character is caught, and so is a swap of 2 neighbors."
    };
    let sub_col = if verdict_bad { pal::red().mix(pal::ink(), 0.3) } else if verdict_good { pal::green().mix(pal::ink(), 0.3) } else { pal::dim().mix(pal::ink(), 0.3) };
    text_center(&mut g, 2, sub, sub_col.s(fade));

    let groups: Vec<String> = shown_addr.chunks(4).map(|c| c.iter().collect()).collect();
    let line: String = groups.join(" ");
    let width = line.chars().count();
    let (lines, y0) = if width + 4 <= g.w {
        (vec![(0usize, width)], rows / 2)
    } else {
        (vec![(0usize, width / 2), (width / 2, width)], rows / 2 - 1)
    };
    let chars: Vec<char> = line.chars().collect();
    let mut idx_in_addr = vec![usize::MAX; chars.len()];
    {
        let mut k = 0;
        for (i, c) in chars.iter().enumerate() {
            if *c != ' ' {
                idx_in_addr[i] = k;
                k += 1;
            }
        }
    }
    let tiles_in = phase(t, 0.2, 1.8);
    for (li, &(a, b)) in lines.iter().enumerate() {
        let x0 = (g.w.saturating_sub(b - a) as i32 / 2 + g_shake).max(0) as usize;
        for i in a..b {
            let ai = idx_in_addr[i];
            if ai == usize::MAX {
                continue;
            }
            if (ai as f32) > tiles_in * n as f32 {
                continue;
            }
            let base = addr_colors(ai, n);
            let mut fg = base;
            let mut bg = base.s(0.12);
            let sx = |s: f32| s * n as f32;
            for (sw, colr) in [(sweep1, if valid { pal::green() } else { pal::red() }), (sweep2, pal::green())] {
                if sw > 0.0 && sw < 1.0 {
                    let d = (ai as f32 - sx(sw)).abs();
                    let k = (-(d * d) / 6.0).exp();
                    bg = bg.add(colr.s(0.5 * k));
                    fg = fg.mix(pal::white(), k);
                }
            }
            if ai == pos && roll_out > 0.0 && roll_back < 1.0 {
                bg = pal::red().s(0.45);
                fg = pal::white();
            }
            if ai >= n - 6 {
                if verdict_bad {
                    bg = pal::red().s(0.35 + 0.4 * flash);
                    fg = pal::white();
                } else if verdict_good {
                    bg = pal::green().s(0.25 + 0.4 * flash);
                    fg = pal::white();
                }
            }
            tile(&mut g, x0 + (i - a), y0 + li * 2, chars[i], fg.s(fade), bg.s(fade));
        }
    }
    if verdict_bad {
        text_center(&mut g, y0 + lines.len() * 2 + 1, "✗  CHECKSUM FAILED", pal::red().mix(pal::white(), 0.3 * flash).s(fade));
    } else if verdict_good {
        text_center(&mut g, y0 + lines.len() * 2 + 1, "✓  CHECKSUM OK", pal::green().mix(pal::white(), 0.3 * flash).s(fade));
    }
    let _ = fw;
    g
}

fn cube(fb: &mut Fb, cam: &Cam, c: [f32; 3], s: f32, col: C3, r: f32) {
    let v = |i: usize| [c[0] + if i & 1 == 1 { s } else { -s }, c[1] + if i & 2 == 2 { s } else { -s }, c[2] + if i & 4 == 4 { s } else { -s }];
    let edges = [(0, 1), (2, 3), (4, 5), (6, 7), (0, 2), (1, 3), (4, 6), (5, 7), (0, 4), (1, 5), (2, 6), (3, 7)];
    for (a, b) in edges {
        if let (Some(pa), Some(pb)) = (cam.project(v(a)), cam.project(v(b))) {
            let depth = 6.0 / pa.2.max(0.5);
            fb.line((pa.0, pa.1), (pb.0, pb.1), r, col.s(depth.min(2.0)));
        }
    }
}

pub fn registry(cols: usize, rows: usize, t: f32, w: &Wallet) -> Grid {
    const LOOP: f32 = 15.0;
    let t = t % LOOP;
    let mut fb = Fb::new(cols, rows, C3::default());
    let (fw, fh) = (fb.width(), fb.height());
    fb.sky(C3::hex(0x010309), C3::hex(0x030712), C3::hex(0x0b2a3a).s(0.5), 0.55, 0.6);
    let cam = Cam { yaw: 0.05 * (t * 0.25).sin(), pitch: 0.30, dist: 3.2, fov: 1.6, cx: fw * 0.5, cy: fh * 0.52, scale: fw * 0.20 };
    let n_blocks = 16;
    let key_block = 3usize;
    let scroll = (t * 0.08) % 1.0;
    let block_pos = |i: usize| {
        let k = i as f32 + scroll;
        [-2.6 + k * 0.62, 0.55 - k * 0.02, -0.8 + k * 1.05]
    };
    let reg = phase(t, 2.2, 4.4);
    let landed = t >= 4.4;
    let search = phase(t, 6.2, 8.4);
    let found = t >= 8.4;
    let back = phase(t, 8.6, 10.2);
    let pay = phase(t, 10.6, 12.2);

    for i in 0..n_blocks {
        let p = block_pos(i);
        let is_key = i == key_block;
        let lit = if is_key && landed { 1.0 - 0.5 * phase(t, 4.4, 6.0) + if found { 0.8 * (1.0 - phase(t, 8.4, 9.5)) } else { 0.0 } } else { 0.0 };
        let sweep = if search > 0.0 && search < 1.0 { (-(((i as f32) - search * key_block as f32).powi(2)) / 0.8).exp() } else { 0.0 };
        let col = pal::teal().s(0.5).mix(pal::gold(), lit.min(1.0)).add(pal::cyan().s(sweep * 0.9));
        cube(&mut fb, &cam, p, 0.24, col, 0.28);
        if let Some((x, y, z)) = cam.project(p) {
            fb.splat(x, y, 3.0 / z.max(0.5), col.s(0.06));
        }
        if i + 1 < n_blocks {
            let q = block_pos(i + 1);
            if let (Some(a), Some(b)) = (cam.project(p), cam.project(q)) {
                fb.line((a.0, a.1), (b.0, b.1), 0.2, pal::teal().s(0.12));
            }
        }
        if is_key && landed {
            if let Some((x, y, _)) = cam.project(p) {
                fb.splat(x, y, 1.6, pal::gold().s(0.35 + 0.6 * lit));
            }
        }
    }

    let wallet = (fw * 0.14, fh * 0.34);
    let sender = (fw * 0.86, fh * 0.34);
    let pulse = 0.6 + 0.4 * (t * 3.0).sin();
    fb.splat(wallet.0, wallet.1, 2.6, pal::magenta().s(0.55 * pulse + if pay >= 1.0 { 0.9 * (1.0 - phase(t, 12.2, 13.5)) } else { 0.0 }));
    fb.ring(wallet.0, wallet.1, 5.0, 0.35, pal::magenta().s(0.35));
    let sender_on = phase(t, 4.6, 5.4);
    if sender_on > 0.0 {
        fb.splat(sender.0, sender.1, 2.6, pal::cyan().s(0.55 * pulse * sender_on));
        fb.ring(sender.0, sender.1, 5.0, 0.35, pal::cyan().s(0.35 * sender_on));
    }

    let key_target = cam.project(block_pos(key_block)).map(|p| (p.0, p.1)).unwrap_or((fw * 0.5, fh * 0.6));
    let n_part = 160;
    for k in 0..n_part {
        let a = k as f32 / n_part as f32 * TAU + t * 1.4;
        let orbit = (wallet.0 + a.cos() * 7.0, wallet.1 + a.sin() * 3.5);
        let b = w.kem_key[k * 7 % w.kem_key.len()];
        let col = byte_color(b, false);
        if !landed {
            let lag = k as f32 / n_part as f32 * 0.35;
            let e = ease_in((reg - lag).max(0.0) / (1.0 - 0.35));
            let mid = ((orbit.0 + key_target.0) * 0.5, (orbit.1 + key_target.1) * 0.5 - fh * 0.25);
            let p1 = (orbit.0 + (mid.0 - orbit.0) * e, orbit.1 + (mid.1 - orbit.1) * e);
            let p2 = (mid.0 + (key_target.0 - mid.0) * e, mid.1 + (key_target.1 - mid.1) * e);
            let p = (p1.0 + (p2.0 - p1.0) * e, p1.1 + (p2.1 - p1.1) * e);
            fb.splat(p.0, p.1, 0.45 + 0.4 * e, col.s(0.7 + 0.8 * e));
        }
        if back > 0.0 && back < 1.0 {
            let lag = k as f32 / n_part as f32 * 0.4;
            let e = ease((back - lag).max(0.0) / 0.6);
            if e > 0.0 && e < 1.0 {
                let mid = ((key_target.0 + sender.0) * 0.5, (key_target.1 + sender.1) * 0.5 - fh * 0.2);
                let p1 = (key_target.0 + (mid.0 - key_target.0) * e, key_target.1 + (mid.1 - key_target.1) * e);
                let p2 = (mid.0 + (sender.0 - mid.0) * e, mid.1 + (sender.1 - mid.1) * e);
                let p = (p1.0 + (p2.0 - p1.0) * e, p1.1 + (p2.1 - p1.1) * e);
                fb.splat(p.0, p.1, 0.5, col.s(1.1));
            }
        }
    }
    if search > 0.0 && search < 1.0 {
        let tgt = cam.project(block_pos((search * key_block as f32) as usize)).map(|p| (p.0, p.1)).unwrap_or(key_target);
        fb.line(sender, tgt, 0.5, pal::cyan().s(0.7));
        fb.splat(tgt.0, tgt.1, 2.0, pal::cyan().s(0.6));
    }
    if pay > 0.0 && pay < 1.0 {
        let e = ease(pay);
        let mid = ((sender.0 + wallet.0) * 0.5, wallet.1 - fh * 0.18);
        let p1 = (sender.0 + (mid.0 - sender.0) * e, sender.1 + (mid.1 - sender.1) * e);
        let p2 = (mid.0 + (wallet.0 - mid.0) * e, mid.1 + (wallet.1 - mid.1) * e);
        let p = (p1.0 + (p2.0 - p1.0) * e, p1.1 + (p2.1 - p1.1) * e);
        for k in 0..14 {
            let tl = (e - k as f32 * 0.012).max(0.0);
            let q1 = (sender.0 + (mid.0 - sender.0) * tl, sender.1 + (mid.1 - sender.1) * tl);
            let q2 = (mid.0 + (wallet.0 - mid.0) * tl, mid.1 + (wallet.1 - mid.1) * tl);
            let q = (q1.0 + (q2.0 - q1.0) * tl, q1.1 + (q2.1 - q1.1) * tl);
            fb.splat(q.0, q.1, 1.2 - k as f32 * 0.06, pal::gold().s(0.5 / (1.0 + k as f32 * 0.4)));
        }
        fb.splat(p.0, p.1, 2.2, pal::gold().mix(pal::white(), 0.4).s(1.2));
    }
    let fade = 1.0 - phase(t, LOOP - 0.6, LOOP);
    fb.fade(fade);
    let mut g = fb.finish(0.9, 0.5, (t * 30.0) as u64);

    text_center(&mut g, 1, "FIRST CONTACT", pal::ink().s(fade));
    let sub = if t < 2.2 {
        "your wallet holds the full key: 1,216 bytes"
    } else if t < 4.6 {
        "you put it on the chain once. A small fee or proof of work stops spam."
    } else if t < 6.2 {
        "a friend has only your 58-character address"
    } else if t < 8.6 {
        "their wallet finds the key on the chain by the address"
    } else if t < 10.6 {
        "it checks: hash of the key = the address. Nobody can swap in a fake key."
    } else {
        "then it pays you. After that, the short address is all anyone needs."
    };
    text_center(&mut g, 2, sub, pal::dim().mix(pal::ink(), 0.3).s(fade));
    let wy = (wallet.1 / 2.0) as usize;
    let lbl = |g: &mut Grid, x: f32, y: usize, s: &str, c: C3| {
        let n = s.chars().count();
        text(g, (x as usize).saturating_sub(n / 2), y, s, c);
    };
    lbl(&mut g, wallet.0, wy + 4, "your wallet", pal::magenta().mix(pal::ink(), 0.4).s(fade));
    if sender_on > 0.0 {
        lbl(&mut g, sender.0, wy + 4, "your friend", pal::cyan().mix(pal::ink(), 0.4).s(fade * sender_on));
    }
    if t >= 4.8 {
        let typed = phase(t, 4.8, 6.0);
        let s = reveal(&w.address, typed);
        let x0 = g.w.saturating_sub(w.address.len()) / 2;
        for (i, ch) in s.chars().enumerate() {
            tile(&mut g, x0 + i, 4, ch, addr_colors(i, w.address.len()).s(fade), addr_colors(i, w.address.len()).s(0.12 * fade));
        }
    }
    if (8.6..10.8).contains(&t) {
        let a = hexs(&address::key_hash(&w.kem_key, &w.owner_key)[..16]);
        let b = hexs(&address::decode(&w.address).unwrap_or([0; 32])[..16]);
        let p = phase(t, 8.8, 10.0);
        let y = rows.saturating_sub(5);
        let x0 = g.w.saturating_sub(a.len() + 22) / 2;
        text(&mut g, x0, y, "hash(key)  ", pal::dim().s(fade));
        text(&mut g, x0, y + 1, "address    ", pal::dim().s(fade));
        for (i, (ca, cb)) in a.chars().zip(b.chars()).enumerate() {
            let on = (i as f32) < p * a.len() as f32;
            let col = if on { if ca == cb { pal::green() } else { pal::red() } } else { pal::ink().s(0.6) };
            tile(&mut g, x0 + 11 + i, y, ca, col.s(fade), C3::default());
            tile(&mut g, x0 + 11 + i, y + 1, cb, col.s(fade), C3::default());
        }
        if p >= 1.0 {
            text(&mut g, x0 + 11 + a.len() + 2, y, "✓ match", pal::green().s(fade));
        }
    }
    let _ = fh;
    g
}
