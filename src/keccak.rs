pub(crate) fn keccak256(input: &[u8]) -> [u8; 32] {
    let mut st = [0u64; 25];
    const RATE: usize = 136;
    let mut offset = 0;
    while offset + RATE <= input.len() {
        absorb(&mut st, &input[offset..offset + RATE]);
        offset += RATE;
    }
    let mut last = [0u8; RATE];
    let rest = &input[offset..];
    last[..rest.len()].copy_from_slice(rest);
    last[rest.len()] ^= 0x01;
    last[RATE - 1] ^= 0x80;
    absorb(&mut st, &last);
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[i * 8..i * 8 + 8].copy_from_slice(&st[i].to_le_bytes());
    }
    out
}

pub(crate) fn erc7201(id: &str) -> crate::word::Word {
    let inner = keccak256(id.as_bytes());
    let base = crate::word::Word::from_be_bytes(inner).wrapping_sub(crate::word::Word::from_u64(1));
    let outer = keccak256(&base.to_be_bytes());
    let mut word = crate::word::Word::from_be_bytes(outer);
    word.0[0] &= !0xff;
    word
}

/// ERC-1967 implementation slot.
pub(crate) fn erc1967_implementation() -> crate::word::Word {
    crate::word::Word::from_be_bytes([
        0x36, 0x08, 0x94, 0xa1, 0x3b, 0xa1, 0xa3, 0x21, 0x06, 0x67, 0xc8, 0x28, 0x49, 0x2d, 0xb9,
        0x8d, 0xca, 0x3e, 0x20, 0x76, 0xcc, 0x37, 0x35, 0xa9, 0x20, 0xa3, 0xca, 0x50, 0x5d, 0x38,
        0x2b, 0xbc,
    ])
}

pub(crate) fn selector(sig: &str) -> [u8; 4] {
    let h = keccak256(sig.as_bytes());
    [h[0], h[1], h[2], h[3]]
}

fn absorb(st: &mut [u64; 25], block: &[u8]) {
    for i in 0..17 {
        let mut p = [0u8; 8];
        p.copy_from_slice(&block[i * 8..i * 8 + 8]);
        st[i] ^= u64::from_le_bytes(p);
    }
    keccak_f(st);
}

const ROT: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

const PIL: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

const RC: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

fn keccak_f(a: &mut [u64; 25]) {
    for round in 0..24 {
        let mut bc = [0u64; 5];
        for i in 0..5 {
            bc[i] = a[i] ^ a[i + 5] ^ a[i + 10] ^ a[i + 15] ^ a[i + 20];
        }
        for i in 0..5 {
            let t = bc[(i + 4) % 5] ^ bc[(i + 1) % 5].rotate_left(1);
            for j in (0..25).step_by(5) {
                a[j + i] ^= t;
            }
        }
        let mut t = a[1];
        for i in 0..24 {
            let j = PIL[i];
            bc[0] = a[j];
            a[j] = t.rotate_left(ROT[i]);
            t = bc[0];
        }
        for j in (0..25).step_by(5) {
            let b = [a[j], a[j + 1], a[j + 2], a[j + 3], a[j + 4]];
            for i in 0..5 {
                a[j + i] ^= (!b[(i + 1) % 5]) & b[(i + 2) % 5];
            }
        }
        a[0] ^= RC[round];
    }
}
