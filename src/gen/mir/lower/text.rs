//! The string routines the standard library names as intrinsics: case, search, replace,
//! escapes, and joins. Each works on bytes in the arena and writes its result at the
//! arena's top, as Solady's `LibString` and `LibBytes` do theirs.

use super::*;

impl Lower<'_> {
    /// A loop that carries words from pass to pass while `go` holds of them. Becomes their
    /// values when it ends.
    fn loop_while(
        &mut self,
        cx: &mut Cx,
        carried: Vec<V>,
        go: impl FnOnce(&mut Cx, &[V]) -> V,
        body: impl FnOnce(&mut Self, &mut Cx, &[V]) -> Result<Vec<V>, Error>,
    ) -> Result<Vec<V>, Error> {
        let head = cx.b.block();
        cx.b.forget_storage();
        cx.b.jump(head, carried.clone());
        cx.b.enter(head);
        let params: Vec<V> = carried
            .iter()
            .map(|_| cx.b.block_param(head, 256))
            .collect();
        let go = go(cx, &params);
        let (inside, after) = (cx.b.block(), cx.b.block());
        cx.b.branch(go, inside, after);
        let state = cx.b.state();
        cx.nested += 1;
        cx.b.enter(inside);
        let next = body(self, cx, &params)?;
        cx.nested -= 1;
        if !cx.b.dead {
            cx.b.jump(head, next);
        }
        cx.b.restore(&state);
        cx.b.forget_storage();
        cx.b.enter(after);
        Ok(params)
    }

    /// One byte of a string being escaped, the first of the word `w` read at `i`, written
    /// at `o` as it is or as its escape. Becomes the place after it and after what it wrote.
    fn escape_byte(
        &mut self,
        cx: &mut Cx,
        html: bool,
        set: V,
        w: V,
        i: V,
        o: V,
    ) -> Result<Val, Error> {
        let l = self;
        let zero = cx.b.num(0);
        let c = cx.b.op2(BYTE, zero, w);
        let one = cx.b.num(1);
        let bit = cx.b.op2(SHL, c, one);
        let special = cx.b.op2(AND, bit, set);
        let next = l.branch(
            cx,
            special,
            |l, cx| {
                if html {
                    // Each of `"&'<>` finds, at its value modulo 9, where
                    // its entity starts in the text and how long it is.
                    let mut text = [0u8; 32];
                    text[..24].copy_from_slice(b"&quot;&amp;&#39;&lt;&gt;");
                    let text = cx.b.word(Word::from_be_bytes(text));
                    let entry =
                        |k: u32, bits: u64, n: u64| Word::from_u64(bits << 8 | n).shl(16 * k);
                    let table = entry(7, 0, 6)
                        .bitor(entry(2, 48, 5))
                        .bitor(entry(3, 88, 5))
                        .bitor(entry(6, 128, 4))
                        .bitor(entry(8, 160, 4));
                    let table = cx.b.word(table);
                    let nine = cx.b.num(9);
                    let k = cx.b.op2(MOD, c, nine);
                    let four = cx.b.num(4);
                    let k = cx.b.op2(SHL, four, k);
                    let e = cx.b.op2(SHR, k, table);
                    let (low, eight) = (cx.b.num(0xff), cx.b.num(8));
                    let n = cx.b.op2(AND, e, low);
                    let by = cx.b.op2(SHR, eight, e);
                    let by = cx.b.op2(AND, by, low);
                    let word = cx.b.op2(SHL, by, text);
                    l.mstore(cx, o, word);
                    return Ok(Val::Word(cx.b.op2(ADD, o, n)));
                }
                // A quote or a backslash after a backslash, the letter
                // of `\b\t\n\f\r`, or `\u00` and two hex digits.
                let mut letters = [0u8; 32];
                letters[26..].copy_from_slice(b"btn\0fr");
                let letters = cx.b.word(Word::from_be_bytes(letters));
                let k = cx.b.num(18);
                let k = cx.b.op2(ADD, c, k);
                let letter = cx.b.op2(BYTE, k, letters);
                let most = cx.b.num(0x1f);
                let printed = cx.b.op2(GT, c, most);
                let own = cx.b.op2(MUL, c, printed);
                let e = cx.b.op2(OR, letter, own);
                l.branch(
                    cx,
                    e,
                    |l, cx| {
                        let slash = cx.b.num(0x5c00);
                        let pair = cx.b.op2(OR, slash, e);
                        let k = cx.b.num(240);
                        let word = cx.b.op2(SHL, k, pair);
                        l.mstore(cx, o, word);
                        Ok(Val::Word(l.add(cx, o, 2)))
                    },
                    |l, cx| {
                        let four = cx.b.num(4);
                        let hi = cx.b.op2(SHR, four, c);
                        let fifteen = cx.b.num(15);
                        let lo = cx.b.op2(AND, c, fifteen);
                        let nine = cx.b.num(9);
                        let letter = cx.b.op2(GT, lo, nine);
                        let gap = cx.b.num(39);
                        let lift = cx.b.op2(MUL, letter, gap);
                        let lo = cx.b.op2(ADD, lo, lift);
                        // `\u00`, then the digits from `0`.
                        let head = cx.b.num(0x5c75_3030_3030);
                        let eight = cx.b.num(8);
                        let hi = cx.b.op2(SHL, eight, hi);
                        let digits = cx.b.op2(ADD, hi, lo);
                        let six = cx.b.op2(ADD, head, digits);
                        let k = cx.b.num(208);
                        let word = cx.b.op2(SHL, k, six);
                        l.mstore(cx, o, word);
                        Ok(Val::Word(l.add(cx, o, 6)))
                    },
                )
            },
            |l, cx| {
                cx.b.effect(Op::MStore8, vec![o, c], 0);
                Ok(Val::Word(l.add(cx, o, 1)))
            },
        )?;
        let Val::Word(next) = next else {
            unreachable!()
        };
        Ok(Val::Tuple(vec![
            Val::Word(l.add(cx, i, 1)),
            Val::Word(next),
        ]))
    }

    /// The first word of a needle, the shift that keeps its `n % 32` bytes of a word, and
    /// its hash when it is 32 bytes or more: what a place in a subject is compared with.
    fn needle(&mut self, cx: &mut Cx, at: V, n: V) -> Result<(V, V, V, V), Error> {
        let word = cx.b.effect(Op::MLoad, vec![at], 1);
        let (low, whole, three) = (cx.b.num(31), cx.b.num(32), cx.b.num(3));
        let part = cx.b.op2(AND, n, low);
        let keep = cx.b.op2(SUB, whole, part);
        let shift = cx.b.op2(SHL, three, keep);
        let short = cx.b.op2(LT, n, whole);
        let big = cx.b.is_zero(short);
        let hash = self.branch(
            cx,
            big,
            |_, cx| Ok(Val::Word(cx.b.effect(Op::Keccak, vec![at, n], 1))),
            |_, cx| Ok(Val::Word(cx.b.num(0))),
        )?;
        let Val::Word(hash) = hash else {
            unreachable!()
        };
        Ok((word, shift, big, hash))
    }

    /// Whether the needle is at `p`: its first bytes there, and its hash when it is long.
    fn found(&mut self, cx: &mut Cx, p: V, n: V, needle: (V, V, V, V)) -> Result<V, Error> {
        let (word, shift, big, hash) = needle;
        let there = cx.b.effect(Op::MLoad, vec![p], 1);
        let differ = cx.b.op2(XOR, there, word);
        let differ = cx.b.op2(SHR, shift, differ);
        let near = cx.b.is_zero(differ);
        let hit = self.branch(
            cx,
            near,
            |l, cx| {
                l.branch(
                    cx,
                    big,
                    |_, cx| {
                        let h = cx.b.effect(Op::Keccak, vec![p, n], 1);
                        Ok(Val::Word(cx.b.op2(EQ, h, hash)))
                    },
                    |_, cx| Ok(Val::Word(cx.b.num(1))),
                )
            },
            |_, cx| Ok(Val::Word(cx.b.num(0))),
        )?;
        let Val::Word(hit) = hit else { unreachable!() };
        Ok(hit)
    }

    /// Bytes written from `at` to `end` at the arena's top, as a value.
    fn written(&self, cx: &mut Cx, at: V, len: V) -> Val {
        cx.any_mem = true;
        cx.top = cx.b.op2(ADD, at, len);
        cx.at_top = Some((at, len));
        Val::MemBytes(at, len)
    }

    pub(super) fn text(&mut self, cx: &mut Cx, b: Builtin, args: &[Expr]) -> Result<Val, Error> {
        match b {
            // Each byte flips its `0x20` bit where the letters' bit is set in the flags,
            // read at the byte's own value plus 5. Bytes past `0x7f` are left alone.
            Builtin::StringCase(upper) => {
                let val = self.expr(cx, &args[0])?;
                let at = cx.top;
                let end = self.raw_bytes(cx, &val, at)?;
                let len = cx.b.op2(SUB, end, at);
                let flags = Word::from_u64(0x3ff_ffff).shl(70 + 32 * u32::from(upper));
                let flags = cx.b.word(flags);
                let f = self.helper(Helper::Case, 3, |l, cx, a| {
                    let zero = cx.b.num(0);
                    l.each(cx, zero, a[1], Vec::new(), |_, cx, i, _| {
                        let p = cx.b.op2(ADD, a[0], i);
                        let w = cx.b.effect(Op::MLoad, vec![p], 1);
                        let zero = cx.b.num(0);
                        let c = cx.b.op2(BYTE, zero, w);
                        let bit = cx.b.op2(SHR, c, a[2]);
                        let mask = cx.b.num(0x20);
                        let bit = cx.b.op2(AND, bit, mask);
                        let c = cx.b.op2(XOR, c, bit);
                        cx.b.effect(Op::MStore8, vec![p, c], 0);
                        Ok(Vec::new())
                    })?;
                    Ok(Vec::new())
                })?;
                cx.b.effect(Op::Call(f), vec![at, len, flags], 0);
                Ok(self.written(cx, at, len))
            }
            // The first place at or after `from` where the needle is, or the greatest
            // `uint`. An empty needle is found at `from`, or at the end.
            Builtin::StringIndexOf => {
                let (subject, needle) = (self.expr(cx, &args[0])?, self.expr(cx, &args[1])?);
                let from = self.word(cx, &args[2])?;
                let (top, at_top) = (cx.top, cx.at_top);
                let (src, len) = self.bytes_in_memory(cx, &subject)?;
                let (nsrc, n) = self.bytes_in_memory(cx, &needle)?;
                let f = self.helper(Helper::IndexOf, 5, |l, cx, a| {
                    let (src, len, nsrc, n, from) = (a[0], a[1], a[2], a[3], a[4]);
                    let none = cx.b.word(Word::from_u64(0).not());
                    let empty = cx.b.is_zero(n);
                    let out = l.branch(
                        cx,
                        empty,
                        |_, cx| {
                            // The lesser of `from` and the length.
                            let past = cx.b.op2(GT, from, len);
                            let (a, b) = (cx.b.op2(MUL, past, len), cx.b.is_zero(past));
                            let b = cx.b.op2(MUL, b, from);
                            Ok(Val::Word(cx.b.op2(ADD, a, b)))
                        },
                        |l, cx| {
                            // The last start is `src + len - n`.
                            let one = cx.b.num(1);
                            let end = cx.b.op2(ADD, src, len);
                            let end = cx.b.op2(SUB, end, n);
                            let end = cx.b.op2(ADD, end, one);
                            let first = cx.b.op2(ADD, src, from);
                            let (x, y) = (cx.b.op2(LT, first, end), cx.b.op2(LT, from, len));
                            let z = cx.b.op2(GT, n, len);
                            let z = cx.b.is_zero(z);
                            let fits = cx.b.op2(AND, x, y);
                            let fits = cx.b.op2(AND, fits, z);
                            l.branch(
                                cx,
                                fits,
                                |l, cx| {
                                    let needle = l.needle(cx, nsrc, n)?;
                                    let zero = cx.b.num(0);
                                    let out = l.loop_while(
                                        cx,
                                        vec![first, zero],
                                        |cx, c| {
                                            let more = cx.b.op2(LT, c[0], end);
                                            let open = cx.b.is_zero(c[1]);
                                            cx.b.op2(AND, more, open)
                                        },
                                        |l, cx, c| {
                                            let hit = l.found(cx, c[0], n, needle)?;
                                            let miss = cx.b.is_zero(hit);
                                            Ok(vec![cx.b.op2(ADD, c[0], miss), hit])
                                        },
                                    )?;
                                    let at = cx.b.op2(SUB, out[0], src);
                                    let (a, b) = (cx.b.op2(MUL, out[1], at), cx.b.is_zero(out[1]));
                                    let b = cx.b.op2(MUL, b, none);
                                    Ok(Val::Word(cx.b.op2(ADD, a, b)))
                                },
                                |_, _| Ok(Val::Word(none)),
                            )
                        },
                    )?;
                    let Val::Word(out) = out else { unreachable!() };
                    Ok(vec![out])
                })?;
                let at = cx.b.effect(Op::Call(f), vec![src, len, nsrc, n, from], 1);
                (cx.top, cx.at_top) = (top, at_top);
                Ok(Val::Word(at))
            }
            // The subject with each place the needle is at replaced, scanned from its
            // start. An empty needle is before every byte, and at the end.
            Builtin::StringReplace => {
                let vals = [
                    self.expr(cx, &args[0])?,
                    self.expr(cx, &args[1])?,
                    self.expr(cx, &args[2])?,
                ];
                let (src, len) = self.bytes_in_memory(cx, &vals[0])?;
                let (nsrc, n) = self.bytes_in_memory(cx, &vals[1])?;
                let (rsrc, rlen) = self.bytes_in_memory(cx, &vals[2])?;
                let out = cx.top;
                let f = self.helper(Helper::Replace, 7, |l, cx, a| {
                    let (src, len, nsrc, n) = (a[0], a[1], a[2], a[3]);
                    let (rsrc, rlen, out) = (a[4], a[5], a[6]);
                    let one = cx.b.num(1);
                    let end = cx.b.op2(ADD, src, len);
                    // One past the last place a needle can start: nowhere when it is
                    // longer than the subject.
                    let fits = cx.b.op2(GT, n, len);
                    let fits = cx.b.is_zero(fits);
                    let stop = cx.b.op2(SUB, end, n);
                    let stop = cx.b.op2(ADD, stop, one);
                    let stop = cx.b.op2(MUL, stop, fits);
                    let needle = l.needle(cx, nsrc, n)?;
                    let step = cx.b.is_zero(n);
                    let step = cx.b.is_zero(step);
                    let at = l.loop_while(
                        cx,
                        vec![src, out],
                        |cx, c| cx.b.op2(LT, c[0], stop),
                        |l, cx, c| {
                            let (i, o) = (c[0], c[1]);
                            let hit = l.found(cx, i, n, needle)?;
                            let o = l.branch(
                                cx,
                                hit,
                                |_, cx| {
                                    cx.b.effect(Op::MCopy, vec![o, rsrc, rlen], 0);
                                    Ok(Val::Word(cx.b.op2(ADD, o, rlen)))
                                },
                                |_, _| Ok(Val::Word(o)),
                            )?;
                            let Val::Word(o) = o else { unreachable!() };
                            // Past a needle that was there; else the byte is kept, where
                            // there is one.
                            let skip = cx.b.op2(AND, hit, step);
                            let next = l.branch(
                                cx,
                                skip,
                                |_, cx| {
                                    Ok(Val::Tuple(vec![
                                        Val::Word(cx.b.op2(ADD, i, n)),
                                        Val::Word(o),
                                    ]))
                                },
                                |_, cx| {
                                    let w = cx.b.effect(Op::MLoad, vec![i], 1);
                                    let zero = cx.b.num(0);
                                    let c = cx.b.op2(BYTE, zero, w);
                                    cx.b.effect(Op::MStore8, vec![o, c], 0);
                                    let inside = cx.b.op2(LT, i, end);
                                    let one = cx.b.num(1);
                                    Ok(Val::Tuple(vec![
                                        Val::Word(cx.b.op2(ADD, i, one)),
                                        Val::Word(cx.b.op2(ADD, o, inside)),
                                    ]))
                                },
                            )?;
                            let mut next_words = Vec::new();
                            l.flatten(&next, &mut next_words)?;
                            Ok(next_words)
                        },
                    )?;
                    // The rest of the subject, where the scan stopped short of its end.
                    let (i, o) = (at[0], at[1]);
                    let left = cx.b.op2(LT, i, end);
                    let rest = cx.b.op2(SUB, end, i);
                    let rest = cx.b.op2(MUL, rest, left);
                    cx.b.effect(Op::MCopy, vec![o, i, rest], 0);
                    let o = cx.b.op2(ADD, o, rest);
                    Ok(vec![cx.b.op2(SUB, o, out)])
                })?;
                let size =
                    cx.b.effect(Op::Call(f), vec![src, len, nsrc, n, rsrc, rlen, out], 1);
                Ok(self.written(cx, out, size))
            }
            Builtin::StringEscape(html) => {
                let quoted = match args.get(1) {
                    Some(q) => self.word(cx, q)?,
                    None => cx.b.num(0),
                };
                let val = self.expr(cx, &args[0])?;
                let (src, len) = self.bytes_in_memory(cx, &val)?;
                let out = cx.top;
                let f = self.helper(Helper::Escape(html), 4, |l, cx, a| {
                    let (src, len, out, quoted) = (a[0], a[1], a[2], a[3]);
                    let (zero, quote) = (cx.b.num(0), cx.b.num(0x22));
                    cx.b.effect(Op::MStore8, vec![out, quote], 0);
                    let start = cx.b.op2(ADD, out, quoted);
                    // The bytes that are escaped, as a bit each at the byte's own value.
                    let set = if html {
                        Word::from_u64(0x5000_00c4_0000_0000)
                    } else {
                        let one = Word::from_u64(1);
                        Word::from_u64(0xffff_ffff)
                            .bitor(one.shl(0x22))
                            .bitor(one.shl(0x5c))
                    };
                    let set = cx.b.word(set);
                    let more = |cx: &mut Cx, v: &[V]| cx.b.op2(LT, v[0], len);
                    let end = l.loop_while(cx, vec![zero, start], more, |l, cx, v| {
                        let (i, o) = (v[0], v[1]);
                        // A whole word with no byte to escape is copied as it is; any
                        // other stretch goes byte by byte, to the word's end or the
                        // string's.
                        let past = l.add(cx, i, 32);
                        let short = cx.b.op2(GT, past, len);
                        let slow = l.branch(
                            cx,
                            short,
                            |_, cx| Ok(Val::Word(cx.b.num(1))),
                            |_, cx| {
                                let p = cx.b.op2(ADD, src, i);
                                let w = cx.b.effect(Op::MLoad, vec![p], 1);
                                // A byte of `y` is zero exactly where the high bit of
                                // `(y & 0x7f..) + 0x7f.. | y` is clear, with no carry
                                // between bytes.
                                let bytes = |b: u8| Word::from_be_bytes([b; 32]);
                                let tests: &[(u8, u8)] = match html {
                                    true => &[
                                        (XOR, 0x22),
                                        (XOR, 0x26),
                                        (XOR, 0x27),
                                        (XOR, 0x3c),
                                        (XOR, 0x3e),
                                    ],
                                    false => &[(AND, 0xe0), (XOR, 0x22), (XOR, 0x5c)],
                                };
                                let low = cx.b.word(bytes(0x7f));
                                let mut all = None;
                                for &(op, c) in tests {
                                    let k = cx.b.word(bytes(c));
                                    let y = cx.b.op2(op, w, k);
                                    let t = cx.b.op2(AND, y, low);
                                    let t = cx.b.op2(ADD, t, low);
                                    let t = cx.b.op2(OR, t, y);
                                    all = Some(match all {
                                        Some(all) => cx.b.op2(AND, all, t),
                                        None => t,
                                    });
                                }
                                let none = cx.b.op1(NOT, all.expect("a test"));
                                let high = cx.b.word(bytes(0x80));
                                Ok(Val::Word(cx.b.op2(AND, none, high)))
                            },
                        )?;
                        let Val::Word(slow) = slow else {
                            unreachable!()
                        };
                        let step = l.branch(
                            cx,
                            slow,
                            |l, cx| {
                                let over = cx.b.op2(GT, past, len);
                                let stop = l.branch(
                                    cx,
                                    over,
                                    |_, _| Ok(Val::Word(len)),
                                    |_, _| Ok(Val::Word(past)),
                                )?;
                                let Val::Word(stop) = stop else {
                                    unreachable!()
                                };
                                let end = l.each(cx, i, stop, vec![o], |l, cx, j, o| {
                                    let p = cx.b.op2(ADD, src, j);
                                    let w = cx.b.effect(Op::MLoad, vec![p], 1);
                                    match l.escape_byte(cx, html, set, w, j, o[0])? {
                                        Val::Tuple(step) => match step[..] {
                                            [_, Val::Word(o)] => Ok(vec![o]),
                                            _ => unreachable!(),
                                        },
                                        _ => unreachable!(),
                                    }
                                })?;
                                Ok(Val::Tuple(vec![Val::Word(stop), Val::Word(end[0])]))
                            },
                            |l, cx| {
                                let p = cx.b.op2(ADD, src, i);
                                let w = cx.b.effect(Op::MLoad, vec![p], 1);
                                l.mstore(cx, o, w);
                                let o = l.add(cx, o, 32);
                                Ok(Val::Tuple(vec![Val::Word(past), Val::Word(o)]))
                            },
                        )?;
                        match step {
                            Val::Tuple(step) => match step[..] {
                                [Val::Word(i), Val::Word(o)] => Ok(vec![i, o]),
                                _ => unreachable!(),
                            },
                            _ => unreachable!(),
                        }
                    })?;
                    cx.b.effect(Op::MStore8, vec![end[1], quote], 0);
                    let end = cx.b.op2(ADD, end[1], quoted);
                    Ok(vec![cx.b.op2(SUB, end, out)])
                })?;
                let size = cx.b.effect(Op::Call(f), vec![src, len, out, quoted], 1);
                Ok(self.written(cx, out, size))
            }
            // The values of a list of strings or bytes, one after another.
            Builtin::Join(_) => {
                let elem = self.c.types[self.peel(args[0].ty())].elem.unwrap_or(0);
                let (at, len) = match self.expr(cx, &args[0])? {
                    Val::Empty => return Ok(Val::Lit(Vec::new())),
                    Val::ListOf(vals) => {
                        return Ok(Val::Packed(vals.into_iter().map(|v| (v, elem)).collect()))
                    }
                    val => self.in_memory(cx, &val, args[0].ty())?,
                };
                let (out, zero) = (cx.top, cx.b.num(0));
                let end = self.each(cx, zero, len, vec![out], |l, cx, i, o| {
                    let off = l.words(cx, i, 2);
                    let pos = cx.b.op2(ADD, at, off);
                    let from = cx.b.effect(Op::MLoad, vec![pos], 1);
                    let pos = l.add(cx, pos, 32);
                    let n = cx.b.effect(Op::MLoad, vec![pos], 1);
                    cx.b.effect(Op::MCopy, vec![o[0], from, n], 0);
                    Ok(vec![cx.b.op2(ADD, o[0], n)])
                })?;
                let size = cx.b.op2(SUB, end[0], out);
                Ok(self.written(cx, out, size))
            }
            _ => unsupported("this string routine"),
        }
    }
}
