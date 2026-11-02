use std::collections::BTreeSet;
use std::fs;
use std::io::Write;
use std::path::PathBuf;

use ab_glyph::{Font, FontRef, PxScale, ScaleFont};

const PX: f32 = 48.0;

fn main() {
    let mut chars = BTreeSet::new();
    for entry in fs::read_dir("src").expect("src") {
        let path = entry.expect("entry").path();
        if path.extension().is_some_and(|e| e == "rs") {
            println!("cargo:rerun-if-changed={}", path.display());
            for c in fs::read_to_string(&path).expect("read").chars() {
                if c as u32 > 0x7f {
                    chars.insert(c);
                }
            }
        }
    }
    println!("cargo:rerun-if-changed=assets/NotoSansSC-Regular.otf");
    let data = fs::read("assets/NotoSansSC-Regular.otf").expect("assets/NotoSansSC-Regular.otf");
    let font = FontRef::try_from_slice(&data).expect("CJK font");
    let sf = font.as_scaled(PxScale::from(PX));
    let ascent = sf.ascent();
    let line = ascent - sf.descent();
    let pad = (PX * 0.25).ceil();
    let cw = (PX + 2.0 * pad).ceil() as u32;
    let ch = (line + 2.0 * pad).ceil() as u32;
    let mut bitmap = Vec::new();
    let mut table = String::new();
    for &c in &chars {
        let id = font.glyph_id(c);
        if id.0 == 0 {
            panic!("the CJK font has no glyph for {c:?} (U+{:04X})", c as u32);
        }
        let mut cell = vec![0u8; (cw * ch) as usize];
        let glyph = id.with_scale_and_position(PxScale::from(PX), ab_glyph::point(pad, pad + ascent));
        if let Some(og) = font.outline_glyph(glyph) {
            let b = og.px_bounds();
            og.draw(|x, y, cov| {
                let xx = (b.min.x as i32 + x as i32).clamp(0, cw as i32 - 1) as u32;
                let yy = (b.min.y as i32 + y as i32).clamp(0, ch as i32 - 1) as u32;
                let p = &mut cell[(yy * cw + xx) as usize];
                *p = (*p).max((cov.clamp(0.0, 1.0) * 255.0) as u8);
            });
        }
        bitmap.extend_from_slice(&cell);
        table.push_str(&format!("    ({:?}, {:.3}),\n", c, sf.h_advance(id)));
    }
    let out = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    fs::write(out.join("cjk.bin"), &bitmap).unwrap();
    let mut f = fs::File::create(out.join("cjk.rs")).unwrap();
    writeln!(f, "pub const CJK_PX: f32 = {PX:.1};").unwrap();
    writeln!(f, "pub const CJK_PAD: f32 = {pad:.1};").unwrap();
    writeln!(f, "pub const CJK_ASCENT: f32 = {ascent:.3};").unwrap();
    writeln!(f, "pub const CJK_CELL: (u32, u32) = ({cw}, {ch});").unwrap();
    writeln!(f, "pub const CJK_BITMAP: &[u8] = include_bytes!(concat!(env!(\"OUT_DIR\"), \"/cjk.bin\"));").unwrap();
    writeln!(f, "pub const CJK_GLYPHS: &[(char, f32)] = &[\n{table}];").unwrap();
}
