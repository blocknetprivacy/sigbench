use crate::metrics::Stats;

const W: usize = 78;

const AMBER: u8 = 214;
const CYAN: u8 = 44;
const GREEN: u8 = 78;
const RED: u8 = 203;
const GRAY: u8 = 245;
const RULE: u8 = 240;
const WHITE: u8 = 231;

fn fg(n: u8, s: &str, on: bool) -> String {
    if on {
        format!("\x1b[38;5;{n}m{s}\x1b[0m")
    } else {
        s.to_string()
    }
}
fn bold_fg(n: u8, s: &str, on: bool) -> String {
    if on {
        format!("\x1b[1;38;5;{n}m{s}\x1b[0m")
    } else {
        s.to_string()
    }
}

struct Seg {
    vis: usize,
    s: String,
    on: bool,
}
impl Seg {
    fn new(on: bool) -> Self {
        Seg { vis: 0, s: String::new(), on }
    }
    fn t(mut self, txt: &str) -> Self {
        self.vis += txt.chars().count();
        self.s.push_str(txt);
        self
    }
    fn c(mut self, n: u8, txt: &str) -> Self {
        self.vis += txt.chars().count();
        self.s.push_str(&fg(n, txt, self.on));
        self
    }
    fn cb(mut self, n: u8, txt: &str) -> Self {
        self.vis += txt.chars().count();
        self.s.push_str(&bold_fg(n, txt, self.on));
        self
    }
    fn d(mut self, txt: &str) -> Self {
        self.vis += txt.chars().count();
        self.s.push_str(&fg(GRAY, txt, self.on));
        self
    }
    fn raw(mut self, width: usize, colored: String) -> Self {
        self.vis += width;
        self.s.push_str(&colored);
        self
    }
}

fn panel(title: Seg, lines: Vec<Seg>, on: bool) -> String {
    let mut out = String::new();
    let inner = W - 4;
    let dashes = W.saturating_sub(5 + title.vis);
    out.push_str(&fg(RULE, "╭─ ", on));
    out.push_str(&title.s);
    out.push(' ');
    out.push_str(&fg(RULE, &"─".repeat(dashes), on));
    out.push_str(&fg(RULE, "╮", on));
    out.push('\n');
    for line in lines {
        let pad = inner.saturating_sub(line.vis);
        out.push_str(&fg(RULE, "│", on));
        out.push(' ');
        out.push_str(&line.s);
        out.push_str(&" ".repeat(pad));
        out.push(' ');
        out.push_str(&fg(RULE, "│", on));
        out.push('\n');
    }
    out.push_str(&fg(RULE, "╰", on));
    out.push_str(&fg(RULE, &"─".repeat(W - 2), on));
    out.push_str(&fg(RULE, "╯", on));
    out
}

fn bar(frac: f64, width: usize, hue: u8, on: bool) -> String {
    let frac = frac.clamp(0.0, 1.0);
    let eighths = (frac * width as f64 * 8.0).round() as usize;
    let whole = eighths / 8;
    let part = eighths % 8;
    let mut filled = "█".repeat(whole.min(width));
    let mut cells = whole.min(width);
    if part > 0 && whole < width {
        filled.push(['▏', '▎', '▍', '▌', '▋', '▊', '▉'][part - 1]);
        cells += 1;
    }
    let track = width.saturating_sub(cells);
    format!("{}{}", fg(hue, &filled, on), fg(RULE, &"░".repeat(track), on))
}

fn gauge(low: f64, avg: f64, high: f64, width: usize, hue: u8, on: bool) -> String {
    let frac = if high > low { (avg - low) / (high - low) } else { 0.5 };
    let pos = (frac.clamp(0.0, 1.0) * (width - 1) as f64).round() as usize;
    let mut s = String::new();
    for i in 0..width {
        if i == pos {
            s.push_str(&fg(hue, "●", on));
        } else if i == 0 || i == width - 1 {
            s.push_str(&fg(RULE, "─", on));
        } else {
            s.push_str(&fg(RULE, "─", on));
        }
    }
    s
}

fn num(x: f64) -> String {
    if x < 10.0 {
        format!("{x:.2}")
    } else if x < 100.0 {
        format!("{x:.1}")
    } else {
        format!("{x:.0}")
    }
}
fn size(bytes: usize) -> String {
    if bytes < 10_000 {
        format!("{bytes} B")
    } else {
        format!("{:.1} KB", bytes as f64 / 1024.0)
    }
}

pub enum Side {
    Legacy,
    New,
}
impl Side {
    fn hue(&self) -> u8 {
        match self {
            Side::Legacy => AMBER,
            Side::New => CYAN,
        }
    }
    fn tag(&self) -> &'static str {
        match self {
            Side::Legacy => "LEGACY",
            Side::New => "NEW",
        }
    }
}

pub struct Op {
    pub side: Side,
    pub verb: &'static str,
    pub time: Stats,
    pub cpu: Stats,
}

pub struct HashRow {
    pub pow: crate::mining::Pow,
    pub mined: crate::miner::Mined,
    pub ran: bool,
    pub gpu: Vec<(String, Result<crate::miner::Mined, String>)>,
}

pub fn fmt_hash_time(ms: f64) -> String {
    if ms >= 1000.0 {
        format!("{:.2} s", ms / 1000.0)
    } else if ms >= 1.0 {
        format!("{ms:.0} ms")
    } else if ms >= 1e-3 {
        format!("{:.1} us", ms * 1e3)
    } else {
        format!("{:.0} ns", ms * 1e6)
    }
}

pub fn fmt_rate(hr: f64) -> String {
    if hr >= 1e9 {
        format!("{:.2} GH/s", hr / 1e9)
    } else if hr >= 1e6 {
        format!("{:.2} MH/s", hr / 1e6)
    } else if hr >= 1e3 {
        format!("{:.1} kH/s", hr / 1e3)
    } else {
        format!("{hr:.2} H/s")
    }
}

pub struct Report {
    pub sig_bytes: usize,
    pub proof_bytes: usize,
    pub ops: Vec<Op>,
    pub leg_mem_mb: Option<Stats>,
    pub new_mem_mb: Option<Stats>,
    pub hashes: Vec<HashRow>,
    pub faithful: Option<bool>,
    pub faraday: Option<FaradayReport>,
}

pub struct FaradayReport {
    pub tx_meta: usize,
    pub per_tx_proof: usize,
    pub tx_relay: usize,
    pub folded_bytes: usize,
    pub fold_secs: f64,
    pub block_n: usize,
    pub block_bytes: usize,
}

pub fn banner(on: bool, host: &str, cores: usize, n_legacy: usize, n_new: usize) {
    for ml in crate::brand::masthead(on, host, cores) {
        println!("{ml}");
    }
    println!();
    let title = Seg::new(on).cb(WHITE, "what this compares");
    let l1 = Seg::new(on)
        .c(AMBER, "legacy")
        .d("   RingCT CLSAG ring signature  (ring 16, Ristretto255)");
    let l2 = Seg::new(on)
        .c(CYAN, "new")
        .d("      Faraday unified spend STARK proof  (Plonky3, KoalaBear^5, 112-bit proven)");
    let l3 = Seg::new(on).d(&format!(
        "{n_legacy} legacy (sign+verify) · {n_new} new (prove+verify) · fold 2 spends -> 1"
    ));
    println!("{}", panel(title, vec![l1, l2, Seg::new(on), l3], on));
}

pub fn check(on: bool, ok: bool, label: &str) {
    let mark = if ok {
        fg(GREEN, "✓", on)
    } else {
        fg(RED, "✗", on)
    };
    println!("  {mark} {}", fg(GRAY, label, on));
}

fn faraday_panel(on: bool, r: &Report) {
    let Some(f) = r.faraday.as_ref() else { return };
    let title = Seg::new(on)
        .cb(WHITE, "FARADAY TX / BLOCK")
        .d("   PQC wire format, offline");
    let unfolded_mb = f.block_n as f64 * f.per_tx_proof as f64 / (1024.0 * 1024.0);
    let savings = unfolded_mb * 1024.0 * 1024.0 / (f.folded_bytes.max(1) as f64);
    let _ = f.block_bytes;
    let lines = vec![
        Seg::new(on)
            .c(CYAN, "fold     ")
            .c(WHITE, "2 spends -> 1 proof")
            .d(&format!("  {}, verified, in {:.0}s", size(f.folded_bytes), f.fold_secs)),
        Seg::new(on),
        Seg::new(on)
            .c(CYAN, "tx send  ")
            .c(WHITE, &size(f.tx_relay))
            .d(&format!("  relay  ({} metadata + {} proof)", size(f.tx_meta), size(f.per_tx_proof))),
        Seg::new(on)
            .c(CYAN, "tx chain ")
            .c(WHITE, &size(f.tx_meta))
            .d("  metadata only  (proof stripped + folded away)"),
        Seg::new(on),
        Seg::new(on)
            .c(CYAN, "block    ")
            .c(WHITE, &format!("{} txs", f.block_n))
            .d(" fit a 2 MB block")
            .c(GREEN, &format!("  O(1): saves ~{:.0}x on-chain", savings)),
    ];
    println!("\n{}", panel(title, lines, on));
}

pub fn results(on: bool, r: &Report) {
    let title = Seg::new(on)
        .cb(WHITE, "TIMING")
        .d("   low ")
        .d("·")
        .d(" avg ")
        .d("·")
        .d(" high        spread          cpu");
    let mut lines = Vec::new();
    for op in &r.ops {
        let hue = op.side.hue();
        let g = gauge(op.time.low, op.time.avg, op.time.high, 11, hue, on);
        let label = format!("{:<6} {:<6}", op.side.tag(), op.verb);
        let vals = format!(
            "{:>6} {:>6} {:>6}",
            num(op.time.low),
            num(op.time.avg),
            num(op.time.high)
        );
        let line = Seg::new(on)
            .c(hue, &label)
            .d("")
            .c(WHITE, &vals)
            .d(" ms  ")
            .raw(11, g)
            .d("   ")
            .c(cpu_hue(op.cpu.avg), &format!("{:>3.0}%", op.cpu.avg));
        lines.push(line);
    }
    println!("\n{}", panel(title, lines, on));

    let (leg_sign, new_prove) = (find(r, "sign"), find(r, "prove"));
    let (leg_ver, new_ver) = (find_side(r, &Side::Legacy, "verify"), find_side(r, &Side::New, "verify"));
    if leg_sign.is_some() && new_prove.is_some() {
        let title = Seg::new(on).cb(WHITE, "HEAD TO HEAD").d("   (average, bar scaled within each pair)");
        let mut lines = Vec::new();
        let ls = leg_sign.unwrap();
        let np = new_prove.unwrap();
        pair(
            &mut lines,
            on,
            "create",
            ("legacy sign", AMBER, ls.time.avg, format!("{} ms", num(ls.time.avg))),
            ("new prove", CYAN, np.time.avg, format!("{} ms", num(np.time.avg))),
            np.time.avg / ls.time.avg.max(f64::MIN_POSITIVE),
        );
        if let (Some(lv), Some(nv)) = (leg_ver, new_ver) {
            lines.push(Seg::new(on));
            pair(
                &mut lines,
                on,
                "verify",
                ("legacy verify", AMBER, lv.time.avg, format!("{} ms", num(lv.time.avg))),
                ("new verify", CYAN, nv.time.avg, format!("{} ms", num(nv.time.avg))),
                nv.time.avg / lv.time.avg.max(f64::MIN_POSITIVE),
            );
        }
        lines.push(Seg::new(on));
        pair(
            &mut lines,
            on,
            "size",
            ("legacy sig", AMBER, r.sig_bytes as f64, size(r.sig_bytes)),
            ("new proof", CYAN, r.proof_bytes as f64, size(r.proof_bytes)),
            r.proof_bytes as f64 / (r.sig_bytes as f64).max(1.0),
        );
        println!("\n{}", panel(title, lines, on));
    }

    if r.leg_mem_mb.is_some() || r.new_mem_mb.is_some() {
        let title = Seg::new(on).cb(WHITE, "MEMORY").d("   resident set size, sampled across each suite");
        let mut lines = Vec::new();
        let mx = r
            .leg_mem_mb
            .map(|s| s.high)
            .unwrap_or(0.0)
            .max(r.new_mem_mb.map(|s| s.high).unwrap_or(0.0))
            .max(1.0);
        if let Some(m) = r.leg_mem_mb {
            mem_row(&mut lines, on, "legacy suite", AMBER, m, mx);
        }
        if let Some(m) = r.new_mem_mb {
            mem_row(&mut lines, on, "new suite", CYAN, m, mx);
        }
        println!("\n{}", panel(title, lines, on));
    }

    faraday_panel(on, r);

    mining_panel(on, r);

    println!(
        "\n  {}",
        fg(
            GRAY,
            "one legacy signature authorizes 1 input; one new proof authorizes a whole",
            on
        )
    );
    println!(
        "  {}",
        fg(
            GRAY,
            "1-in / 1-out spend (membership + key image + range + balance).",
            on
        )
    );
}

const LIGHT: u8 = 252;

fn cpu_hue(pct: f64) -> u8 {
    if pct >= 150.0 {
        GREEN
    } else {
        LIGHT
    }
}

fn find<'a>(r: &'a Report, verb: &str) -> Option<&'a Op> {
    r.ops.iter().find(|o| o.verb == verb)
}
fn find_side<'a>(r: &'a Report, side: &Side, verb: &str) -> Option<&'a Op> {
    r.ops
        .iter()
        .find(|o| o.verb == verb && std::mem::discriminant(&o.side) == std::mem::discriminant(side))
}

#[allow(clippy::too_many_arguments)]
fn pair(
    lines: &mut Vec<Seg>,
    on: bool,
    group: &str,
    a: (&str, u8, f64, String),
    b: (&str, u8, f64, String),
    ratio: f64,
) {
    let bw = 28;
    let mx = a.2.max(b.2).max(f64::MIN_POSITIVE);
    let row_a = Seg::new(on)
        .d(&format!("{group:<8}"))
        .c(a.1, &format!("{:<15}", a.0))
        .raw(bw, bar(a.2 / mx, bw, a.1, on))
        .t(" ")
        .c(WHITE, &a.3);
    let row_b = Seg::new(on)
        .t(&" ".repeat(8))
        .c(b.1, &format!("{:<15}", b.0))
        .raw(bw, bar(b.2 / mx, bw, b.1, on))
        .t(" ")
        .c(WHITE, &b.3)
        .d(&format!("   {:.0}×", ratio));
    lines.push(row_a);
    lines.push(row_b);
}

fn mem_row(lines: &mut Vec<Seg>, on: bool, label: &str, hue: u8, s: Stats, mx: f64) {
    let bw = 26;
    lines.push(
        Seg::new(on)
            .c(hue, &format!("{label:<13}"))
            .raw(bw, bar(s.high / mx, bw, hue, on))
            .t(" ")
            .c(WHITE, &format!("{:>5.1} MB", s.high))
            .d(&format!("   low {:.1} · avg {:.1}", s.low, s.avg)),
    );
}

fn mining_panel(on: bool, r: &Report) {
    if r.hashes.is_empty() {
        return;
    }
    let title = Seg::new(on)
        .cb(WHITE, "MINING HASH")
        .d("   all CPU threads that fit in RAM, 30 s each (Argon2 t=1 · p=1 · 32-byte)");
    let mut lines = Vec::new();
    match r.faithful {
        Some(true) => lines.push(
            Seg::new(on)
                .c(GREEN, "✓")
                .d(" reproduction matches blocknet_pow_hash at 2 GiB"),
        ),
        Some(false) => lines.push(
            Seg::new(on)
                .c(RED, "✗")
                .d(" MISMATCH vs blocknet_pow_hash -- numbers suspect"),
        ),
        None => lines.push(Seg::new(on).d("faithfulness check skipped (2 GiB did not fit)")),
    }
    lines.push(Seg::new(on));
    for h in &r.hashes {
        let label = crate::mining::label(h.pow);
        if !h.ran {
            lines.push(
                Seg::new(on)
                    .c(crate::brand::LIME, &format!("{label:<27}"))
                    .d("skipped (needs more RAM than is safe on this machine)"),
            );
            continue;
        }
        lines.push(
            Seg::new(on)
                .c(crate::brand::LIME, &format!("{label:<27}"))
                .c(GREEN, &format!("{:>11}", fmt_rate(h.mined.rate())))
                .d(&format!("   on {:>2} threads   ", h.mined.threads))
                .c(WHITE, &fmt_hash_time(h.mined.ms_per_hash()))
                .d(" per hash per thread"),
        );
        for (name, g) in &h.gpu {
            let seg = Seg::new(on).d(&format!("{:<27}", "  on GPU"));
            lines.push(match g {
                Ok(m) => seg.c(GREEN, &format!("{:>11}", fmt_rate(m.rate()))).d(&format!("   {name}  ·  {} in flight", m.threads)),
                Err(e) => seg.d(&format!("not used: {e}  ({name})")),
            });
        }
    }
    println!("\n{}", panel(title, lines, on));
}
