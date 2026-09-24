//! 256-bit words. Little-endian limbs.

use std::hash::{Hash, Hasher};

#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub(crate) struct Word(pub [u64; 4]);

impl Hash for Word {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl Word {
    pub(crate) fn from_u64(v: u64) -> Self {
        Self([v, 0, 0, 0])
    }

    pub(crate) fn is_zero(self) -> bool {
        self.0 == [0; 4]
    }

    pub(crate) fn bit(self, i: u32) -> bool {
        if i >= 256 {
            return false;
        }
        (self.0[(i / 64) as usize] >> (i % 64)) & 1 == 1
    }

    pub(crate) fn from_be_bytes(b: [u8; 32]) -> Self {
        let mut limbs = [0u64; 4];
        for i in 0..4 {
            let mut p = [0u8; 8];
            p.copy_from_slice(&b[i * 8..i * 8 + 8]);
            limbs[3 - i] = u64::from_be_bytes(p);
        }
        Self(limbs)
    }

    /// Solidity's short `string` / `bytes` slot: data left-aligned, low byte `len * 2`.
    pub(crate) fn short_dyn(data: &[u8]) -> Self {
        let mut raw = [0u8; 32];
        let n = data.len().min(31);
        raw[..n].copy_from_slice(&data[..n]);
        raw[31] = (n * 2) as u8;
        Self::from_be_bytes(raw)
    }

    pub(crate) fn to_be_bytes(self) -> [u8; 32] {
        let mut b = [0u8; 32];
        for i in 0..4 {
            let p = self.0[3 - i].to_be_bytes();
            b[i * 8..i * 8 + 8].copy_from_slice(&p);
        }
        b
    }

    pub(crate) fn from_hex(s: &str) -> Option<Self> {
        if s.is_empty() || s.len() > 64 {
            return None;
        }
        let mut bytes = [0u8; 32];
        let padded = format!("{:0>64}", s);
        for i in 0..32 {
            bytes[i] = u8::from_str_radix(&padded[i * 2..i * 2 + 2], 16).ok()?;
        }
        Some(Self::from_be_bytes(bytes))
    }

    pub(crate) fn from_dec(s: &str) -> Option<Self> {
        let mut acc = Self::from_u64(0);
        let ten = Self::from_u64(10);
        for c in s.bytes() {
            if c == b'_' {
                continue;
            }
            if !c.is_ascii_digit() {
                return None;
            }
            let (a, ov1) = acc.overflowing_mul(ten);
            if ov1 {
                return None;
            }
            let (a, ov2) = a.overflowing_add(Self::from_u64((c - b'0') as u64));
            if ov2 {
                return None;
            }
            acc = a;
        }
        Some(acc)
    }

    pub(crate) fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let mut out = [0u64; 4];
        let mut carry = 0u128;
        for i in 0..4 {
            let s = self.0[i] as u128 + rhs.0[i] as u128 + carry;
            out[i] = s as u64;
            carry = s >> 64;
        }
        (Self(out), carry != 0)
    }

    pub(crate) fn wrapping_add(self, rhs: Self) -> Self {
        self.overflowing_add(rhs).0
    }

    pub(crate) fn wrapping_sub(self, rhs: Self) -> Self {
        self.wrapping_add(rhs.wrapping_neg())
    }

    pub(crate) fn wrapping_neg(self) -> Self {
        let (n, _) = self.not().overflowing_add(Self::from_u64(1));
        n
    }

    pub(crate) fn not(self) -> Self {
        Self([!self.0[0], !self.0[1], !self.0[2], !self.0[3]])
    }

    pub(crate) fn bitand(self, rhs: Self) -> Self {
        Self([
            self.0[0] & rhs.0[0],
            self.0[1] & rhs.0[1],
            self.0[2] & rhs.0[2],
            self.0[3] & rhs.0[3],
        ])
    }

    pub(crate) fn bitor(self, rhs: Self) -> Self {
        Self([
            self.0[0] | rhs.0[0],
            self.0[1] | rhs.0[1],
            self.0[2] | rhs.0[2],
            self.0[3] | rhs.0[3],
        ])
    }

    pub(crate) fn bitxor(self, rhs: Self) -> Self {
        Self([
            self.0[0] ^ rhs.0[0],
            self.0[1] ^ rhs.0[1],
            self.0[2] ^ rhs.0[2],
            self.0[3] ^ rhs.0[3],
        ])
    }

    pub(crate) fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let mut out = [0u64; 4];
        let mut overflow = false;
        for i in 0..4 {
            let mut carry = 0u128;
            for j in 0..4 {
                let prod = self.0[i] as u128 * rhs.0[j] as u128 + carry;
                let k = i + j;
                if k < 4 {
                    let sum = out[k] as u128 + (prod & 0xffff_ffff_ffff_ffff);
                    out[k] = sum as u64;
                    carry = (prod >> 64) + (sum >> 64);
                } else if prod != 0 {
                    overflow = true;
                    carry = prod >> 64;
                } else {
                    carry = 0;
                }
            }
            if carry != 0 {
                overflow = true;
            }
        }
        (Self(out), overflow)
    }

    pub(crate) fn wrapping_mul(self, rhs: Self) -> Self {
        self.overflowing_mul(rhs).0
    }

    pub(crate) fn lt(self, rhs: Self) -> bool {
        for i in (0..4).rev() {
            if self.0[i] != rhs.0[i] {
                return self.0[i] < rhs.0[i];
            }
        }
        false
    }

    pub(crate) fn slt(self, rhs: Self) -> bool {
        let sn = self.bit(255);
        let on = rhs.bit(255);
        if sn != on {
            return sn;
        }
        self.lt(rhs)
    }

    pub(crate) fn shr(self, n: u32) -> Self {
        if n >= 256 {
            return Self::from_u64(0);
        }
        let limbs = (n / 64) as usize;
        let bits = n % 64;
        let mut out = [0u64; 4];
        for i in 0..4 {
            let src = i + limbs;
            if src < 4 {
                out[i] = self.0[src] >> bits;
                if bits != 0 && src + 1 < 4 {
                    out[i] |= self.0[src + 1] << (64 - bits);
                }
            }
        }
        Self(out)
    }

    pub(crate) fn shl(self, n: u32) -> Self {
        if n >= 256 {
            return Self::from_u64(0);
        }
        let limbs = (n / 64) as usize;
        let bits = n % 64;
        let mut out = [0u64; 4];
        for i in (0..4).rev() {
            if i >= limbs {
                let src = i - limbs;
                out[i] = self.0[src] << bits;
                if bits != 0 && src > 0 {
                    out[i] |= self.0[src - 1] >> (64 - bits);
                }
            }
        }
        Self(out)
    }

    pub(crate) fn div(self, rhs: Self) -> Self {
        self.divmod(rhs).0
    }

    pub(crate) fn rem(self, rhs: Self) -> Self {
        self.divmod(rhs).1
    }

    fn divmod(self, rhs: Self) -> (Self, Self) {
        if rhs.is_zero() {
            return (Self::from_u64(0), Self::from_u64(0));
        }
        let mut q = Self::from_u64(0);
        let mut r = Self::from_u64(0);
        for i in (0..256).rev() {
            r = r.shl(1);
            if self.bit(i) {
                r.0[0] |= 1;
            }
            if !r.lt(rhs) {
                r = r.wrapping_sub(rhs);
                q.0[(i / 64) as usize] |= 1u64 << (i % 64);
            }
        }
        (q, r)
    }

    /// Arithmetic right shift. A shift of 256 or more yields `0` or `-1`.
    pub(crate) fn sar(self, n: u32) -> Self {
        if n == 0 {
            return self;
        }
        if n >= 256 {
            return if self.bit(255) {
                Self::from_u64(0).not()
            } else {
                Self::from_u64(0)
            };
        }
        let shifted = self.shr(n);
        if self.bit(255) {
            shifted.bitor(Self::from_u64(0).not().shl(256 - n))
        } else {
            shifted
        }
    }

    /// EVM `SIGNEXTEND`. `k` is the index of the highest sign byte.
    pub(crate) fn sign_extend(self, k: u32) -> Self {
        if k >= 31 {
            return self;
        }
        let bit = k * 8 + 7;
        let width = bit + 1;
        if self.bit(bit) {
            self.bitor(Self::from_u64(0).not().shl(width))
        } else {
            self.bitand(Self::from_u64(0).not().shr(256 - width))
        }
    }

    pub(crate) fn sdiv(self, rhs: Self) -> Self {
        if rhs.is_zero() {
            return Self::from_u64(0);
        }
        let min = Self::from_u64(1).shl(255);
        let neg1 = Self::from_u64(0).not();
        if self == min && rhs == neg1 {
            return min;
        }
        let neg = self.bit(255) ^ rhs.bit(255);
        let a = if self.bit(255) {
            self.wrapping_neg()
        } else {
            self
        };
        let b = if rhs.bit(255) {
            rhs.wrapping_neg()
        } else {
            rhs
        };
        let q = a.div(b);
        if neg {
            q.wrapping_neg()
        } else {
            q
        }
    }

    /// Remainder with the sign of the dividend. Truncates toward zero.
    pub(crate) fn smod(self, rhs: Self) -> Self {
        if rhs.is_zero() {
            return Self::from_u64(0);
        }
        let min = Self::from_u64(1).shl(255);
        let neg1 = Self::from_u64(0).not();
        if self == min && rhs == neg1 {
            return Self::from_u64(0);
        }
        let neg = self.bit(255);
        let a = if self.bit(255) {
            self.wrapping_neg()
        } else {
            self
        };
        let b = if rhs.bit(255) {
            rhs.wrapping_neg()
        } else {
            rhs
        };
        let r = a.rem(b);
        if neg {
            r.wrapping_neg()
        } else {
            r
        }
    }
}
