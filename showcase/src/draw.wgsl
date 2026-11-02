struct U {
    res: vec4<f32>,
    atlas: vec4<f32>,
    img: vec4<f32>,
    uvr: vec4<f32>,
    logo: vec4<f32>,
    tint: vec4<f32>,
};

@group(0) @binding(0) var<uniform> u: U;
@group(0) @binding(1) var font: texture_2d<f32>;
@group(0) @binding(2) var lin: sampler;
@group(0) @binding(3) var field: texture_2d<f32>;
@group(0) @binding(4) var near: sampler;

const QUAD = array<vec2<f32>, 6>(vec2<f32>(0.0, 0.0), vec2<f32>(1.0, 0.0), vec2<f32>(1.0, 1.0), vec2<f32>(0.0, 0.0), vec2<f32>(1.0, 1.0), vec2<f32>(0.0, 1.0));

fn to_clip(px: vec2<f32>) -> vec4<f32> {
    return vec4<f32>(px.x / u.res.x * 2.0 - 1.0, 1.0 - px.y / u.res.y * 2.0, 0.0, 1.0);
}

struct RIn {
    @location(0) pos: vec2<f32>,
    @location(1) size: vec2<f32>,
    @location(2) col: vec4<f32>,
};

struct ROut {
    @builtin(position) pos: vec4<f32>,
    @location(0) col: vec4<f32>,
};

@vertex
fn vs_rect(@builtin(vertex_index) vi: u32, r: RIn) -> ROut {
    var o: ROut;
    o.pos = to_clip(r.pos + QUAD[vi] * r.size);
    o.col = vec4<f32>(r.col.rgb * r.col.a, r.col.a);
    return o;
}

@fragment
fn fs_rect(i: ROut) -> @location(0) vec4<f32> {
    return i.col;
}

struct IOut {
    @builtin(position) pos: vec4<f32>,
    @location(0) uv: vec2<f32>,
};

@vertex
fn vs_image(@builtin(vertex_index) vi: u32) -> IOut {
    let c = QUAD[vi];
    var o: IOut;
    o.pos = to_clip(u.img.xy + c * u.img.zw);
    o.uv = mix(u.uvr.xy, u.uvr.zw, c);
    return o;
}

@fragment
fn fs_image(i: IOut) -> @location(0) vec4<f32> {
    let v = textureSample(field, near, i.uv).r;
    let c = u.tint.rgb * (0.10 + 0.9 * v * v);
    return vec4<f32>(c * u.tint.a, u.tint.a);
}

struct GIn {
    @location(0) pos: vec2<f32>,
    @location(1) size: vec2<f32>,
    @location(2) uv: vec4<f32>,
    @location(3) col: vec4<f32>,
};

struct GOut {
    @builtin(position) pos: vec4<f32>,
    @location(0) uv: vec2<f32>,
    @location(1) col: vec4<f32>,
};

@vertex
fn vs_glyph(@builtin(vertex_index) vi: u32, g: GIn) -> GOut {
    let c = QUAD[vi];
    var o: GOut;
    o.pos = to_clip(g.pos + c * g.size);
    o.uv = mix(g.uv.xy, g.uv.zw, c);
    o.col = g.col;
    return o;
}

@fragment
fn fs_glyph(i: GOut) -> @location(0) vec4<f32> {
    let a = textureSample(font, lin, i.uv).r * i.col.a;
    return vec4<f32>(i.col.rgb * a, a);
}

struct LOut {
    @builtin(position) pos: vec4<f32>,
    @location(0) uv: vec2<f32>,
};

@vertex
fn vs_logo(@builtin(vertex_index) vi: u32) -> LOut {
    let c = QUAD[vi];
    var o: LOut;
    o.pos = to_clip(u.logo.xy + c * u.logo.z);
    o.uv = c;
    return o;
}

fn capsule(p: vec2<f32>, a: vec2<f32>, b: vec2<f32>, r: f32) -> f32 {
    let pa = p - a;
    let ba = b - a;
    let h = clamp(dot(pa, ba) / dot(ba, ba), 0.0, 1.0);
    return length(pa - ba * h) - r;
}

fn rbox(p: vec2<f32>, half: vec2<f32>, r: f32) -> f32 {
    let q = abs(p) - half + vec2<f32>(r);
    return length(max(q, vec2<f32>(0.0))) + min(max(q.x, q.y), 0.0) - r;
}

@fragment
fn fs_logo(i: LOut) -> @location(0) vec4<f32> {
    let p = i.uv * 1080.0;
    let px = 1080.0 / u.logo.z;
    let square = rbox(p - vec2<f32>(540.0), vec2<f32>(540.0), 230.0);
    let mark = min(capsule(p, vec2<f32>(300.0, 800.0), vec2<f32>(780.0, 800.0), 92.0), capsule(p, vec2<f32>(410.0, 300.0), vec2<f32>(780.0, 560.0), 92.0));
    let inside = 1.0 - smoothstep(-px, px, square);
    let hole = 1.0 - smoothstep(-px, px, mark);
    let col = mix(vec3<f32>(0.40, 1.0, 0.0), vec3<f32>(0.0), hole);
    return vec4<f32>(col * inside, inside);
}

@group(0) @binding(5) var datatex: texture_2d<f32>;

struct DIn {
    @location(0) rect: vec4<f32>,
    @location(1) uvr: vec4<f32>,
    @location(2) prm: vec4<f32>,
    @location(3) dim: vec4<f32>,
};

struct DOut {
    @builtin(position) pos: vec4<f32>,
    @location(0) uv: vec2<f32>,
    @location(1) prm: vec4<f32>,
    @location(2) dim: vec4<f32>,
    @location(3) base: vec2<f32>,
};

@vertex
fn vs_data(@builtin(vertex_index) vi: u32, d: DIn) -> DOut {
    let c = QUAD[vi];
    var o: DOut;
    o.pos = to_clip(d.rect.xy + c * d.rect.zw);
    o.uv = c;
    o.prm = d.prm;
    o.dim = d.dim;
    o.base = d.uvr.xy;
    return o;
}

fn wit_col(sec: u32) -> vec3<f32> {
    switch sec {
        case 0u, 5u: { return vec3<f32>(0.78, 0.74, 0.66); }
        case 1u: { return vec3<f32>(0.20, 0.20, 0.19); }
        case 2u: { return vec3<f32>(0.42, 0.45, 0.50); }
        case 3u: { return vec3<f32>(0.40, 1.0, 0.0); }
        case 4u: { return vec3<f32>(0.32, 0.32, 0.31); }
        case 6u, 7u: { return vec3<f32>(0.16, 0.16, 0.15); }
        case 8u: { return vec3<f32>(1.0, 1.0, 1.0); }
        default: { return vec3<f32>(0.55, 0.53, 0.50); }
    }
}

fn proof_col(sec: u32) -> vec3<f32> {
    switch sec {
        case 0u: { return vec3<f32>(0.45, 0.43, 0.40); }
        case 2u: { return vec3<f32>(0.80, 0.77, 0.70); }
        case 3u, 1u: { return vec3<f32>(0.40, 1.0, 0.0); }
        default: { return vec3<f32>(0.25, 0.24, 0.22); }
    }
}

@fragment
fn fs_data(i: DOut) -> @location(0) vec4<f32> {
    let w = i.dim.x;
    let rows = i.dim.y;
    let total = i.dim.z;
    let col = floor(i.uv.x * w);
    let row = floor(i.uv.y * rows);
    let idx = row * w + col;
    if (idx >= total) { discard; }
    let tc = vec2<i32>(i32(i.base.x + col), i32(i.base.y + row));
    let tx = textureLoad(datatex, tc, 0);
    let mode = i.prm.x;
    let alpha = i.prm.w;
    var c = vec3<f32>(0.0);
    if (mode < 0.5) {
        if (row / rows > i.prm.z) { discard; }
        let masked = row / rows < i.prm.y;
        let sec = u32(tx.b * 255.0 + 0.5);
        if (masked) {
            if (tx.g < 0.5) { discard; }
            c = vec3<f32>(0.62, 0.60, 0.56);
        } else {
            if (tx.r < 0.5) { discard; }
            c = wit_col(sec);
        }
    } else {
        if (idx / total > i.prm.z) { discard; }
        let sec = u32(tx.b * 255.0 + 0.5);
        c = proof_col(sec) * (0.2 + 0.8 * tx.r);
    }
    return vec4<f32>(c * alpha, alpha);
}
