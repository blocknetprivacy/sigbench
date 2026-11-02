#![allow(dead_code)]

#[path = "../address.rs"]
mod address;
#[path = "../art/mod.rs"]
mod art;
#[path = "../gfx.rs"]
mod gfx;

use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};

use art::{pal, C3};
use gfx::*;

const FPS: u64 = 30;

struct Entry {
    step: &'static str,
    name: &'static str,
    draw: fn(usize, usize, f32, &address::Wallet) -> Grid,
}

fn entries() -> Vec<Entry> {
    vec![
        Entry { step: "Address", name: "squeeze: 1,216 bytes into 63 characters", draw: art::address::squeeze },
        Entry { step: "Address", name: "typo check: one wrong character", draw: art::address::typo },
        Entry { step: "Address", name: "registry: first contact on the chain", draw: art::address::registry },
    ]
}

fn main() {
    let mut seed = [0u8; 32];
    let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap_or_default().as_nanos();
    seed[..16].copy_from_slice(&now.to_le_bytes());
    let wallet = address::wallet(&seed);
    let list = entries();
    let steps: Vec<&str> = list.iter().fold(Vec::new(), |mut v, e| {
        if !v.contains(&e.step) {
            v.push(e.step);
        }
        v
    });
    let term = Term::open();
    let mut out = String::new();
    let mut at = 0usize;
    let mut since = Instant::now();
    let mut size = Term::size();
    let mut last_poll = Instant::now();
    while !QUIT.load(Ordering::Relaxed) {
        let frame = Instant::now();
        match KEY.swap(0, Ordering::SeqCst) {
            b'C' | b'l' | b' ' => {
                at = (at + 1) % list.len();
                since = Instant::now();
            }
            b'D' | b'h' => {
                at = (at + list.len() - 1) % list.len();
                since = Instant::now();
            }
            b'r' => since = Instant::now(),
            _ => {}
        }
        if last_poll.elapsed() > Duration::from_millis(250) {
            let s = Term::size();
            if s != size {
                size = s;
                print!("\x1b[0m\x1b[2J");
            }
            last_poll = Instant::now();
        }
        let (w, h) = (size.0.max(40), size.1.max(14));
        let e = &list[at];
        let mut g = (e.draw)(w, h, since.elapsed().as_secs_f32(), &wallet);
        let step_no = steps.iter().position(|s| *s == e.step).unwrap_or(0) + 1;
        let same: Vec<usize> = (0..list.len()).filter(|&i| list[i].step == e.step).collect();
        let opt = (b'A' + same.iter().position(|&i| i == at).unwrap_or(0) as u8) as char;
        let label = format!(" BENCH 3 DEMO  ·  step {step_no}/{}  {}  ·  option {opt}: {} ", steps.len(), e.step, e.name);
        let keys = " ← →  switch    r  restart    q  quit ";
        let y = h - 1;
        for x in 0..w {
            art::tile(&mut g, x, y, ' ', pal::ink(), C3::hex(0x070a14));
        }
        art::text(&mut g, 0, y, &label, pal::ink());
        art::text(&mut g, w.saturating_sub(keys.chars().count()), y, keys, pal::dim());
        emit(&g, &mut out);
        if let Some(rest) = Duration::from_millis(1000 / FPS).checked_sub(frame.elapsed()) {
            std::thread::sleep(rest);
        }
    }
    drop(term);
    println!("{}", wallet.address);
}
