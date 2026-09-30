//! SHA-256, RIPEMD-160, secp256k1 recovery, and secp256r1 verification for the interpreter's precompiles.

use crate::keccak::keccak256;
use crate::word::Word;

pub(crate) fn sha256(data: &[u8]) -> [u8; 32] {
    let mut state = [
        0x6a09e667u32,
        0xbb67ae85,
        0x3c6ef372,
        0xa54ff53a,
        0x510e527f,
        0x9b05688c,
        0x1f83d9ab,
        0x5be0cd19,
    ];
    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut msg = data.to_vec();
    msg.push(0x80);
    while (msg.len() % 64) != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bit_len.to_be_bytes());
    for chunk in msg.chunks(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes(chunk[i * 4..i * 4 + 4].try_into().unwrap());
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let mut a = state;
        for i in 0..64 {
            let s1 = a[4].rotate_right(6) ^ a[4].rotate_right(11) ^ a[4].rotate_right(25);
            let ch = (a[4] & a[5]) ^ (!a[4] & a[6]);
            let t1 = a[7]
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a[0].rotate_right(2) ^ a[0].rotate_right(13) ^ a[0].rotate_right(22);
            let maj = (a[0] & a[1]) ^ (a[0] & a[2]) ^ (a[1] & a[2]);
            let t2 = s0.wrapping_add(maj);
            a[7] = a[6];
            a[6] = a[5];
            a[5] = a[4];
            a[4] = a[3].wrapping_add(t1);
            a[3] = a[2];
            a[2] = a[1];
            a[1] = a[0];
            a[0] = t1.wrapping_add(t2);
        }
        for i in 0..8 {
            state[i] = state[i].wrapping_add(a[i]);
        }
    }
    let mut out = [0u8; 32];
    for (i, word) in state.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

pub(crate) fn ripemd160(data: &[u8]) -> [u8; 20] {
    let mut state = [
        0x67452301u32,
        0xefcdab89,
        0x98badcfe,
        0x10325476,
        0xc3d2e1f0,
    ];
    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut msg = data.to_vec();
    msg.push(0x80);
    while (msg.len() % 64) != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bit_len.to_le_bytes());
    for chunk in msg.chunks(64) {
        let mut x = [0u32; 16];
        for i in 0..16 {
            x[i] = u32::from_le_bytes(chunk[i * 4..i * 4 + 4].try_into().unwrap());
        }
        let mut al = state[0];
        let mut bl = state[1];
        let mut cl = state[2];
        let mut dl = state[3];
        let mut el = state[4];
        let mut ar = al;
        let mut br = bl;
        let mut cr = cl;
        let mut dr = dl;
        let mut er = el;
        for j in 0..80 {
            let t = al
                .wrapping_add(rl(j, bl, cl, dl))
                .wrapping_add(x[R[j]])
                .wrapping_add(KL[j / 16])
                .rotate_left(S[j])
                .wrapping_add(el);
            al = el;
            el = dl;
            dl = cl.rotate_left(10);
            cl = bl;
            bl = t;
            let tr = ar
                .wrapping_add(rr(j, br, cr, dr))
                .wrapping_add(x[RR[j]])
                .wrapping_add(KR[j / 16])
                .rotate_left(SR[j])
                .wrapping_add(er);
            ar = er;
            er = dr;
            dr = cr.rotate_left(10);
            cr = br;
            br = tr;
        }
        let t = state[1].wrapping_add(cl).wrapping_add(dr);
        state[1] = state[2].wrapping_add(dl).wrapping_add(er);
        state[2] = state[3].wrapping_add(el).wrapping_add(ar);
        state[3] = state[4].wrapping_add(al).wrapping_add(br);
        state[4] = state[0].wrapping_add(bl).wrapping_add(cr);
        state[0] = t;
    }
    let mut out = [0u8; 20];
    for (i, word) in state.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&word.to_le_bytes());
    }
    out
}

/// Signs `hash` with private key `key` and nonce `k`: `(v, r, s)`, with `s` in the lower
/// half of the curve order, as wallets sign.
pub(crate) fn sign(hash: Word, key: Word, k: Word) -> (u8, Word, Word) {
    let n = order();
    let c = secp256k1();
    let point = mul(&c, k, c.g);
    let r = mod_n(point.x);
    let e = mod_n(hash);
    let kinv = invmod(k, n).expect("nonce");
    let mut s = mulmod(kinv, addmod(e, mulmod(r, key, n), n), n);
    let mut v = 27 + (point.y.0[0] & 1) as u8;
    if n.shr(1).lt(s) {
        s = n.wrapping_sub(s);
        v = if v == 27 { 28 } else { 27 };
    }
    (v, r, s)
}

/// The Ethereum address of private key `key`.
pub(crate) fn address_of(key: Word) -> Word {
    let c = secp256k1();
    let point = mul(&c, key, c.g);
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(&point.x.to_be_bytes());
    buf[32..].copy_from_slice(&point.y.to_be_bytes());
    let digest = keccak256(&buf);
    let mut addr = [0u8; 32];
    addr[12..].copy_from_slice(&digest[12..]);
    Word::from_be_bytes(addr)
}

/// Recover an Ethereum address. `input` is the 128-byte precompile argument.
pub(crate) fn ecrecover(input: &[u8]) -> Option<Word> {
    if input.len() != 128 {
        return None;
    }
    let hash = Word::from_be_bytes(input[0..32].try_into().unwrap());
    let v = Word::from_be_bytes(input[32..64].try_into().unwrap());
    let r = Word::from_be_bytes(input[64..96].try_into().unwrap());
    let s = Word::from_be_bytes(input[96..128].try_into().unwrap());
    let parity = if v == Word::from_u64(27) || v == Word::from_u64(0) {
        0u64
    } else if v == Word::from_u64(28) || v == Word::from_u64(1) {
        1
    } else {
        return None;
    };
    if r.is_zero() || s.is_zero() || !r.lt(order()) || !s.lt(order()) {
        return None;
    }
    let y2 = addmod(
        mulmod(mulmod(r, r, prime()), r, prime()),
        Word::from_u64(7),
        prime(),
    );
    let mut y = powmod(y2, sqrt_exp(), prime());
    if (y.0[0] & 1) != parity {
        y = submod(prime(), y, prime());
    }
    if mulmod(y, y, prime()) != y2 {
        return None;
    }
    let point_r = Pt {
        x: r,
        y,
        inf: false,
    };
    let e = mod_n(hash);
    let rinv = invmod(r, order())?;
    let u1 = mulmod(submod(order(), e, order()), rinv, order());
    let u2 = mulmod(s, rinv, order());
    let c = secp256k1();
    let point = add(&c, mul(&c, u1, c.g), mul(&c, u2, point_r));
    if point.inf {
        return None;
    }
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(&point.x.to_be_bytes());
    buf[32..].copy_from_slice(&point.y.to_be_bytes());
    let digest = keccak256(&buf);
    let mut addr = [0u8; 32];
    addr[12..].copy_from_slice(&digest[12..]);
    Some(Word::from_be_bytes(addr))
}

/// EIP-7951 secp256r1 verification. `input` is the 160-byte precompile argument:
/// hash, r, s, and the public key's x and y.
pub(crate) fn p256_verify(input: &[u8]) -> bool {
    if input.len() != 160 {
        return false;
    }
    let word = |i: usize| Word::from_be_bytes(input[i * 32..i * 32 + 32].try_into().unwrap());
    let (hash, r, s, x, y) = (word(0), word(1), word(2), word(3), word(4));
    let c = secp256r1();
    if r.is_zero() || s.is_zero() || !r.lt(c.n) || !s.lt(c.n) || !x.lt(c.p) || !y.lt(c.p) {
        return false;
    }
    let b =
        Word::from_hex("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b").unwrap();
    let rhs = addmod(
        addmod(mulmod(mulmod(x, x, c.p), x, c.p), mulmod(c.a, x, c.p), c.p),
        b,
        c.p,
    );
    if mulmod(y, y, c.p) != rhs {
        return false;
    }
    let sinv = invmod(s, c.n).unwrap();
    let key = Pt { x, y, inf: false };
    let point = add(
        &c,
        mul(&c, mulmod(hash, sinv, c.n), c.g),
        mul(&c, mulmod(r, sinv, c.n), key),
    );
    !point.inf && mod_word(point.x, c.n) == r
}

fn mod_n(w: Word) -> Word {
    let mut w = w;
    while !w.lt(order()) {
        w = w.wrapping_sub(order());
    }
    w
}

/// `(a + b) % m` for `a, b < m`.
pub(crate) fn addmod(a: Word, b: Word, m: Word) -> Word {
    let (sum, overflow) = a.overflowing_add(b);
    if overflow || !sum.lt(m) {
        sum.wrapping_sub(m)
    } else {
        sum
    }
}

fn submod(a: Word, b: Word, m: Word) -> Word {
    if a.lt(b) {
        a.wrapping_sub(b).wrapping_add(m)
    } else {
        a.wrapping_sub(b)
    }
}

/// `(a * b) % m`, without overflow in the product: the 512-bit product, divided by `m`.
pub(crate) fn mulmod(a: Word, b: Word, m: Word) -> Word {
    let mut p = [0u64; 8];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..4 {
            let t = u128::from(a.0[i]) * u128::from(b.0[j]) + u128::from(p[i + j]) + carry;
            p[i + j] = t as u64;
            carry = t >> 64;
        }
        p[i + 4] = carry as u64;
    }
    rem512(p, m)
}

/// The remainder of a 512-bit number, little-endian limbs, by `m`, by Knuth's long
/// division in 64-bit digits (Hacker's Delight's `divmnu`). Zero for a zero `m`.
fn rem512(u: [u64; 8], m: Word) -> Word {
    let Some(top) = (0..4).rev().find(|&i| m.0[i] != 0) else {
        return Word::from_u64(0);
    };
    let n = top + 1;
    if n == 1 {
        let d = u128::from(m.0[0]);
        let r = u
            .iter()
            .rev()
            .fold(0u128, |r, &limb| ((r << 64) | u128::from(limb)) % d);
        return Word::from_u64(r as u64);
    }
    // Normalize so the divisor's top digit has its high bit set.
    let s = m.0[top].leading_zeros();
    let shl = |x: u64, below: u64| {
        if s == 0 {
            x
        } else {
            (x << s) | (below >> (64 - s))
        }
    };
    let mut v = [0u64; 4];
    for i in (0..n).rev() {
        v[i] = shl(m.0[i], if i > 0 { m.0[i - 1] } else { 0 });
    }
    let mut un = [0u64; 9];
    un[8] = if s == 0 { 0 } else { u[7] >> (64 - s) };
    for i in (0..8).rev() {
        un[i] = shl(u[i], if i > 0 { u[i - 1] } else { 0 });
    }
    let b = 1u128 << 64;
    for j in (0..=8 - n).rev() {
        let num = (u128::from(un[j + n]) << 64) | u128::from(un[j + n - 1]);
        let mut qhat = num / u128::from(v[n - 1]);
        let mut rhat = num % u128::from(v[n - 1]);
        while qhat >= b || qhat * u128::from(v[n - 2]) > (rhat << 64) + u128::from(un[j + n - 2]) {
            qhat -= 1;
            rhat += u128::from(v[n - 1]);
            if rhat >= b {
                break;
            }
        }
        // Subtract `qhat * v`; if that went below zero, add `v` back once.
        let mut k = 0i128;
        for i in 0..n {
            let p = qhat * u128::from(v[i]);
            let t = i128::from(un[i + j]) - k - i128::from(p as u64);
            un[i + j] = t as u64;
            k = (p >> 64) as i128 - (t >> 64);
        }
        let t = i128::from(un[j + n]) - k;
        un[j + n] = t as u64;
        if t < 0 {
            let mut carry = 0u128;
            for i in 0..n {
                let t = u128::from(un[i + j]) + u128::from(v[i]) + carry;
                un[i + j] = t as u64;
                carry = t >> 64;
            }
            un[j + n] = un[j + n].wrapping_add(carry as u64);
        }
    }
    let mut r = Word::from_u64(0);
    for i in 0..n {
        r.0[i] = if s == 0 {
            un[i]
        } else {
            (un[i] >> s) | (un[i + 1] << (64 - s))
        };
    }
    r
}

fn mod_word(w: Word, m: Word) -> Word {
    w.rem(m)
}

fn powmod(mut base: Word, exp: Word, m: Word) -> Word {
    let mut result = Word::from_u64(1);
    base = if base.lt(m) { base } else { mod_word(base, m) };
    for i in 0..256 {
        if exp.bit(i) {
            result = mulmod(result, base, m);
        }
        base = mulmod(base, base, m);
    }
    result
}

fn invmod(a: Word, m: Word) -> Option<Word> {
    if a.is_zero() {
        return None;
    }
    // m is prime here (P or N).
    let exp = m.wrapping_sub(Word::from_u64(2));
    Some(powmod(a, exp, m))
}

#[derive(Clone, Copy)]
struct Pt {
    x: Word,
    y: Word,
    inf: bool,
}

struct Curve {
    p: Word,
    n: Word,
    a: Word,
    g: Pt,
}

fn curve(p: &str, n: &str, a: &str, gx: &str, gy: &str) -> Curve {
    let w = |h: &str| Word::from_hex(h).unwrap();
    Curve {
        p: w(p),
        n: w(n),
        a: w(a),
        g: Pt {
            x: w(gx),
            y: w(gy),
            inf: false,
        },
    }
}

fn secp256k1() -> Curve {
    curve(
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
        "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141",
        "0",
        "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
        "483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8",
    )
}

fn secp256r1() -> Curve {
    curve(
        "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
        "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        "ffffffff00000001000000000000000000000000fffffffffffffffffffffffc",
        "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
        "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
    )
}

fn add(c: &Curve, p: Pt, q: Pt) -> Pt {
    if p.inf {
        return q;
    }
    if q.inf {
        return p;
    }
    if p.x == q.x {
        if p.y != q.y || p.y.is_zero() {
            return Pt {
                x: Word::from_u64(0),
                y: Word::from_u64(0),
                inf: true,
            };
        }
        return double(c, p);
    }
    let lam = mulmod(
        submod(q.y, p.y, c.p),
        invmod(submod(q.x, p.x, c.p), c.p).unwrap(),
        c.p,
    );
    let x3 = submod(submod(mulmod(lam, lam, c.p), p.x, c.p), q.x, c.p);
    let y3 = submod(mulmod(lam, submod(p.x, x3, c.p), c.p), p.y, c.p);
    Pt {
        x: x3,
        y: y3,
        inf: false,
    }
}

fn double(c: &Curve, p: Pt) -> Pt {
    if p.inf || p.y.is_zero() {
        return Pt {
            x: Word::from_u64(0),
            y: Word::from_u64(0),
            inf: true,
        };
    }
    let lam = mulmod(
        addmod(
            mulmod(Word::from_u64(3), mulmod(p.x, p.x, c.p), c.p),
            c.a,
            c.p,
        ),
        invmod(addmod(p.y, p.y, c.p), c.p).unwrap(),
        c.p,
    );
    let x3 = submod(mulmod(lam, lam, c.p), addmod(p.x, p.x, c.p), c.p);
    let y3 = submod(mulmod(lam, submod(p.x, x3, c.p), c.p), p.y, c.p);
    Pt {
        x: x3,
        y: y3,
        inf: false,
    }
}

fn mul(c: &Curve, k: Word, p: Pt) -> Pt {
    let mut acc = Pt {
        x: Word::from_u64(0),
        y: Word::from_u64(0),
        inf: true,
    };
    let mut base = p;
    for i in 0..256 {
        if k.bit(i) {
            acc = add(c, acc, base);
        }
        base = double(c, base);
    }
    acc
}

fn rl(j: usize, x: u32, y: u32, z: u32) -> u32 {
    match j / 16 {
        0 => x ^ y ^ z,
        1 => (x & y) | (!x & z),
        2 => (x | !y) ^ z,
        3 => (x & z) | (y & !z),
        _ => x ^ (y | !z),
    }
}

fn rr(j: usize, x: u32, y: u32, z: u32) -> u32 {
    match j / 16 {
        0 => x ^ (y | !z),
        1 => (x & z) | (y & !z),
        2 => (x | !y) ^ z,
        3 => (x & y) | (!x & z),
        _ => x ^ y ^ z,
    }
}

const KL: [u32; 5] = [0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e];
const KR: [u32; 5] = [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000];

const R: [usize; 80] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5,
    2, 14, 11, 8, 3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, 1, 9, 11, 10, 0, 8, 12, 4,
    13, 3, 7, 15, 14, 5, 6, 2, 4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13,
];
const RR: [usize; 80] = [
    5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12,
    4, 9, 1, 2, 15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13, 8, 6, 4, 1, 3, 11, 15, 0, 5,
    12, 2, 13, 9, 7, 10, 14, 12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11,
];
const S: [u32; 80] = [
    11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15,
    9, 11, 7, 13, 12, 11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, 11, 12, 14, 15, 14,
    15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12, 9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6,
];
const SR: [u32; 80] = [
    8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6, 9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12,
    7, 6, 15, 13, 11, 9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5, 15, 5, 8, 11, 14, 14,
    6, 14, 6, 9, 12, 9, 12, 5, 15, 8, 8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11,
];

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

fn prime() -> Word {
    secp256k1().p
}

fn order() -> Word {
    secp256k1().n
}

fn sqrt_exp() -> Word {
    Word::from_hex("3fffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffff0c").unwrap()
}

// Constants used by the field arithmetic. Computed once per call via functions so Word stays simple.
// Aliases below are filled by lazy comparison against function results inside ecrecover through these.
#[cfg(test)]
mod tests {
    use super::*;

    /// `mulmod` against double-and-add, for moduli of every limb count and the curves'.
    #[test]
    fn mulmod_matches_double_and_add() {
        fn slow(a: Word, b: Word, m: Word) -> Word {
            let mut result = Word::from_u64(0);
            let mut base = a.rem(m);
            for i in 0..256 {
                if b.bit(i) {
                    result = addmod(result, base, m);
                }
                base = addmod(base, base, m);
            }
            result
        }
        let mut x = 0x2545_f491_4f6c_dd1du64;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        let word = |next: &mut dyn FnMut() -> u64| {
            Word([next(), next(), next(), next()]).shr((next() % 256) as u32)
        };
        let ones = Word::from_u64(0).not();
        for _ in 0..3000 {
            let (a, b) = (word(&mut next), word(&mut next));
            for m in [
                word(&mut next),
                ones,
                prime(),
                order(),
                secp256r1().p,
                Word::from_u64(1),
            ] {
                if !m.is_zero() {
                    assert_eq!(mulmod(a, b, m), slow(a, b, m), "{a:?} * {b:?} % {m:?}");
                }
            }
        }
        // A digit estimate one too high, which only the add-back step corrects.
        let (u, m) = (
            Word([u64::MAX - 2, 1, 0, 1]),
            Word([u64::MAX, 0, 1 << 63, 0]),
        );
        for b in [Word::from_u64(1), Word([0, 1, 0, 0])] {
            assert_eq!(mulmod(u, b, m), slow(u, b, m));
        }
        assert_eq!(
            mulmod(u, Word::from_u64(1), m),
            Word([u64::MAX - 1, 0, 1 << 63, 0])
        );
        assert_eq!(mulmod(ones, ones, ones), Word::from_u64(0));
        assert_eq!(
            mulmod(ones, ones, ones.wrapping_sub(Word::from_u64(1))),
            Word::from_u64(1)
        );
    }

    #[test]
    fn sha256_abc() {
        let digest = sha256(b"abc");
        assert_eq!(
            hex(&digest),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn ripemd160_abc() {
        let digest = ripemd160(b"abc");
        assert_eq!(hex(&digest), "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc");
    }

    #[test]
    fn ecrecover_matches_geth() {
        let mut input = [0u8; 128];
        input[..32].copy_from_slice(
            &Word::from_hex("ce0677bb30baa8cf067c88db9811f4333d131bf8bcf12fe7065d211dce971008")
                .unwrap()
                .to_be_bytes(),
        );
        input[32..64].copy_from_slice(&Word::from_u64(1).to_be_bytes());
        input[64..96].copy_from_slice(
            &Word::from_hex("90f27b8b488db00b00606796d2987f6a5f59ae62ea05effe84fef5b8b0e54998")
                .unwrap()
                .to_be_bytes(),
        );
        input[96..].copy_from_slice(
            &Word::from_hex("4a691139ad57a3f0b906637673aa2f63d1f55cb1a69199d4009eea23ceaddc93")
                .unwrap()
                .to_be_bytes(),
        );
        let mut xy = [0u8; 64];
        xy[..32].copy_from_slice(
            &Word::from_hex("e32df42865e97135acfb65f3bae71bdc86f4d49150ad6a440b6f15878109880a")
                .unwrap()
                .to_be_bytes(),
        );
        xy[32..].copy_from_slice(
            &Word::from_hex("0a2b2667f7e725ceea70c673093bf67663e0312623c8e091b13cf2c0f11ef652")
                .unwrap()
                .to_be_bytes(),
        );
        let digest = keccak256(&xy);
        let mut addr = [0u8; 32];
        addr[12..].copy_from_slice(&digest[12..]);
        assert_eq!(ecrecover(&input), Some(Word::from_be_bytes(addr)));
    }

    #[test]
    fn p256_verify_matches_wycheproof() {
        let mut input: Vec<u8> = [
            "532eaabd9574880dbf76b9b8cc00832c20a6ec113d682299550d7a6e0f345e25",
            "5",
            "1",
            "4a03ef9f92eb268cafa601072489a56380fa0dc43171d7712813b3a19a1eb5e5",
            "3e213e28a608ce9a2f4a17fd830c6654018a79b3e0263d91a8ba90622df6f2f0",
        ]
        .iter()
        .flat_map(|h| Word::from_hex(h).unwrap().to_be_bytes())
        .collect();
        assert!(p256_verify(&input));
        input[63] = 6;
        assert!(!p256_verify(&input));
        assert!(!p256_verify(&input[..128]));
    }

    fn hex(bytes: &[u8]) -> String {
        const H: &[u8; 16] = b"0123456789abcdef";
        let mut s = String::new();
        for b in bytes {
            s.push(H[(b >> 4) as usize] as char);
            s.push(H[(b & 0xf) as usize] as char);
        }
        s
    }
}
