use super::*;

/// The runtime of `bench/fixed_point.sol`, Solady's `FixedPointMathLib` behind the same
/// entrypoints as `bench/fixed_point.lithe`. To rebuild it after editing the harness, from
/// the crate root:
///
/// ```text
/// solc --optimize --optimize-runs 200 --via-ir --no-cbor-metadata \
///   solady/=bench/vendor/solady/src/ --bin-runtime bench/fixed_point.sol
/// ```
const SOLADY: &str = include_str!("solady_fixed_point.hex");

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    /// A word of a random bit length, so small and large magnitudes are equally likely.
    fn magnitude(&mut self) -> Word {
        let w = Word([self.next(), self.next(), self.next(), self.next()]);
        w.shr(self.below(257) as u32)
    }

    fn signed(&mut self) -> Word {
        let m = self.magnitude();
        if self.next() & 1 == 0 {
            m
        } else {
            m.wrapping_neg()
        }
    }

    /// A magnitude of at most `bits` bits.
    fn bits(&mut self, bits: u32) -> Word {
        self.magnitude().shr(256 - bits)
    }

    fn pick(&mut self, from: &[Word]) -> Word {
        from[self.below(from.len() as u64) as usize]
    }
}

fn dec(s: &str) -> Word {
    match s.strip_prefix('-') {
        Some(m) => Word::from_dec(m).expect("decimal").wrapping_neg(),
        None => Word::from_dec(s).expect("decimal"),
    }
}

fn panic_data(code: u64) -> Vec<u8> {
    word_data("Panic(uint256)", &[Word::from_u64(code)])
}

/// Where Solady raises its own error and Lithe's checked arithmetic panics instead, the
/// panics that stand for it.
fn panics_for(solady: &[u8]) -> Vec<Vec<u8>> {
    let is = |sig: &str| solady == selector(sig);
    if is("SMulWadFailed()") || is("RPowOverflow()") {
        vec![panic_data(0x11)]
    } else if is("SDivWadFailed()") || is("FullMulDivFailed()") {
        vec![panic_data(0x11), panic_data(0x12)]
    } else {
        vec![solady.to_vec()]
    }
}

fn edges() -> Vec<Word> {
    let one = Word::from_u64(1);
    let max = Word::from_u64(0).not();
    let wad = dec("1000000000000000000");
    let mut out = vec![
        Word::from_u64(0),
        one,
        Word::from_u64(2),
        Word::from_u64(3),
        Word::from_u64(7),
        Word::from_u64(8),
        wad.wrapping_sub(one),
        wad,
        wad.wrapping_add(one),
        max,
        max.wrapping_sub(one),
        max.div(wad),
        max.div(wad).wrapping_add(one),
        max.div(wad.wrapping_mul(wad)),
        max.div(wad.wrapping_mul(wad)).wrapping_add(one),
    ];
    for k in [64, 128, 199, 229, 249, 255] {
        let p = one.shl(k);
        out.extend([p.wrapping_sub(one), p, p.wrapping_add(one)]);
    }
    let negated: Vec<Word> = out.iter().map(|w| w.wrapping_neg()).collect();
    out.extend(negated);
    out
}

/// Every Solady-ported entrypoint, on edge and random inputs, against Solady compiled by
/// solc: the same results, and reverts where Solady reverts.
#[test]
fn solady_fixed_point_matches() {
    let ours = deploy(&compile_file(Path::new("bench/fixed_point.lithe")).expect("compile"))
        .expect("deploy");
    let theirs = hex_decode(SOLADY.trim());
    let mut rng = Rng(0x5eed_f00d_cafe_d00d);
    let edges = edges();
    let wad = dec("1000000000000000000");
    let bases = [
        wad,
        dec("1000000000000000000000000000"),
        Word::from_u64(10),
        Word::from_u64(2),
        Word::from_u64(1),
        Word::from_u64(1).shl(64),
    ];
    type Gen = fn(&mut Rng, &[Word], &[Word]) -> Vec<Word>;
    fn arg(r: &mut Rng, e: &[Word]) -> Word {
        if r.below(4) == 0 {
            r.pick(e)
        } else {
            r.magnitude()
        }
    }
    fn signed_arg(r: &mut Rng, e: &[Word]) -> Word {
        if r.below(4) == 0 {
            r.pick(e)
        } else {
            r.signed()
        }
    }
    fn small_signed(r: &mut Rng, bits: u32) -> Word {
        let m = r.bits(bits);
        if r.next() & 1 == 0 {
            m
        } else {
            m.wrapping_neg()
        }
    }
    let any2: Gen = |r, e, _| vec![arg(r, e), arg(r, e)];
    let signed2: Gen = |r, e, _| vec![signed_arg(r, e), signed_arg(r, e)];
    let one: Gen = |r, e, _| vec![arg(r, e)];
    let exp: Gen = |r, e, _| {
        vec![match r.below(4) {
            0 => r.pick(e),
            1 => r.signed(),
            // Across the domain, (-42, 136) * 1e18.
            _ => {
                let x = Word([r.next(), r.next(), 0, 0]).rem(dec("178000000000000000000"));
                x.wrapping_sub(dec("42000000000000000000"))
            }
        }]
    };
    let ln: Gen = |r, e, _| {
        vec![match r.below(8) {
            0 | 1 => r.pick(e),
            2 => r.signed(),
            _ => r.bits(255),
        }]
    };
    let pow: Gen = |r, e, _| {
        let x = if r.below(8) == 0 {
            r.pick(e)
        } else {
            r.bits(90)
        };
        let y = match r.below(8) {
            0 => r.pick(e),
            1 => r.signed(),
            _ => small_signed(r, 66),
        };
        vec![x, y]
    };
    let rpow: Gen = |r, e, bases| {
        let base = if r.below(4) == 0 {
            r.magnitude().bitor(Word::from_u64(1))
        } else {
            r.pick(bases)
        };
        let x = match r.below(4) {
            0 => r.pick(e),
            1 => r.magnitude(),
            _ => base
                .wrapping_add(r.bits(64))
                .wrapping_sub(r.bits(64))
                .shr(r.below(3) as u32),
        };
        let n = match r.below(4) {
            0 => r.pick(e),
            1 => r.magnitude(),
            _ => Word::from_u64(r.below(300)),
        };
        vec![x, n, base]
    };
    let gcd: Gen = |r, e, _| {
        if r.below(8) > 0 {
            return vec![arg(r, e), arg(r, e)];
        }
        // Consecutive Fibonacci numbers take the most steps.
        let (mut a, mut b) = (Word::from_u64(1), Word::from_u64(0));
        while let (next, false) = a.overflowing_add(b) {
            (a, b) = (next, a);
        }
        vec![a, b]
    };
    let lerp: Gen = |r, e, _| {
        let small = r.below(2) == 0;
        (0..5)
            .map(|_| match r.below(5) {
                0 => r.pick(e),
                _ if small => r.bits(40),
                _ => r.magnitude(),
            })
            .collect()
    };
    let lerp_int: Gen = |r, e, _| {
        let small = r.below(2) == 0;
        (0..5)
            .map(|_| match r.below(5) {
                0 => r.pick(e),
                _ if small => small_signed(r, 40),
                _ => r.signed(),
            })
            .collect()
    };
    let cases: &[(&str, Gen)] = &[
        ("wadMulUp(uint256,uint256)", any2),
        ("wadDivUp(uint256,uint256)", any2),
        ("divWad(uint256,uint256)", any2),
        ("sMulWad(int256,int256)", signed2),
        ("sDivWad(int256,int256)", signed2),
        ("expWad(int256)", exp),
        ("lnWad(int256)", ln),
        ("powWad(int256,int256)", pow),
        ("sqrtWad(uint256)", one),
        ("cbrtWad(uint256)", one),
        ("cbrt(uint256)", one),
        ("rpow(uint256,uint256,uint256)", rpow),
        ("dist(uint256,uint256)", any2),
        ("distInt(int256,int256)", signed2),
        ("gcd(uint256,uint256)", gcd),
        ("saturatingAdd(uint256,uint256)", any2),
        ("saturatingSub(uint256,uint256)", any2),
        ("saturatingMul(uint256,uint256)", any2),
        ("lerp(uint256,uint256,uint256,uint256,uint256)", lerp),
        ("lerpInt(int256,int256,int256,int256,int256)", lerp_int),
    ];
    let steps = differential::steps_from_env("SOLADY_STEPS", 2000);
    let run = |code: &[u8], data: &[u8]| {
        exec(
            code,
            data,
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .unwrap_or_else(|e| panic!("{}: {e}", hex(data)))
    };
    for (sig, gen) in cases {
        let mut both_ok = 0;
        for step in 0..steps {
            let mut args = gen(&mut rng, &edges, &bases);
            // Every one-word argument also takes each edge once.
            if step < edges.len() && args.len() == 1 {
                args[0] = edges[step];
            }
            let data = word_data(sig, &args);
            let want = run(&theirs, &data);
            let got = run(&ours, &data);
            let ctx = format!("{sig} {args:?}");
            if !want.reverted {
                assert!(
                    !got.reverted,
                    "{ctx}: Solady returned {}, Lithe reverted {}",
                    hex(&want.returndata),
                    hex(&got.returndata)
                );
                assert_eq!(hex(&want.returndata), hex(&got.returndata), "{ctx}");
                both_ok += 1;
                continue;
            }
            assert!(
                got.reverted,
                "{ctx}: Solady reverted {}, Lithe returned {}",
                hex(&want.returndata),
                hex(&got.returndata)
            );
            assert!(
                panics_for(&want.returndata).contains(&got.returndata),
                "{ctx}: Solady reverted {}, Lithe {}",
                hex(&want.returndata),
                hex(&got.returndata)
            );
        }
        assert!(
            both_ok > steps / 4,
            "{sig}: only {both_ok} of {steps} inputs succeeded"
        );
    }
}

/// Solady's `rpow` divides by `base` without a check, so a zero base gives 0 or `x`;
/// Lithe's division panics once a product needs rounding by it.
#[test]
fn rpow_zero_base_panics() {
    let ours = deploy(&compile_file(Path::new("bench/fixed_point.lithe")).expect("compile"))
        .expect("deploy");
    let w = Word::from_u64;
    let out = call(&ours, "rpow(uint256,uint256,uint256)", &[w(5), w(1), w(0)]);
    assert_eq!(hex(&out.returndata), hex(&w(5).to_be_bytes()));
    let out = call(&ours, "rpow(uint256,uint256,uint256)", &[w(5), w(2), w(0)]);
    assert!(out.reverted);
    assert_eq!(out.returndata, panic_data(0x12));
    let out = call(&ours, "rpow(uint256,uint256,uint256)", &[w(5), w(7), w(0)]);
    assert_eq!(out.returndata, panic_data(0x12));
    // The square's narrowing comes before its division, as in every later step.
    let out = call(
        &ours,
        "rpow(uint256,uint256,uint256)",
        &[w(1).shl(128), w(2), w(0)],
    );
    assert_eq!(out.returndata, panic_data(0x11));
}
