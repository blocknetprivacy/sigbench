pub const LIME: u8 = 154;
const WHITE: u8 = 254;
const DIM: u8 = 244;
const FAINT: u8 = 240;

pub const LOGO: [&str; 7] = [
    "       ▄██▄     ",
    "       █████▄   ",
    "        ▀█████▄ ",
    "          ▀█████",
    "            ▀▀▀ ",
    "  ▄████████████▄",
    "  ▀████████████▀",
];
pub const LOGO_W: usize = 16;
pub const LOGO_H: usize = 7;

pub const MAST_W: usize = 58;

fn p(on: bool, n: u8, s: &str) -> String {
    if on {
        format!("\x1b[38;5;{n}m{s}\x1b[0m")
    } else {
        s.to_string()
    }
}
fn pb(on: bool, n: u8, s: &str) -> String {
    if on {
        format!("\x1b[1;38;5;{n}m{s}\x1b[0m")
    } else {
        s.to_string()
    }
}

pub fn masthead(on: bool, host: &str, cores: usize) -> Vec<String> {
    let host_line = format!("{host} · {cores} cores");
    let rows: [(String, String); LOGO_H] = [
        (String::new(), String::new()),
        ("BLOCKNET".into(), pb(on, LIME, "BLOCKNET")),
        (
            "FARADAY   ·   post-quantum signatures".into(),
            format!("{}{}", pb(on, WHITE, "FARADAY"), p(on, DIM, "   ·   post-quantum signatures")),
        ),
        (String::new(), String::new()),
        (
            "hash-based STARK · quantum-safe".into(),
            p(on, FAINT, "hash-based STARK · quantum-safe"),
        ),
        (host_line.clone(), p(on, FAINT, &host_line)),
        (String::new(), String::new()),
    ];

    (0..LOGO_H)
        .map(|i| {
            let (plain, colored) = &rows[i];
            let vis = LOGO_W + 3 + plain.chars().count();
            let pad = MAST_W.saturating_sub(vis);
            format!("{}   {}{}", p(on, LIME, LOGO[i]), colored, " ".repeat(pad))
        })
        .collect()
}
