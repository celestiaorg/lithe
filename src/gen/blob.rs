use super::*;

impl<'a> Gen<'a> {
    /// `[len]` is on the stack. Leaves the header pointer, with `len` stored at it.
    pub(super) fn alloc_blob(&mut self) -> Result<(), Error> {
        self.call_sub(Sub::AllocBlob);
        Ok(())
    }

    /// `[len, ret]` becomes `[ptr]`. The bump pointer is kept relative to the blob area,
    /// so zeroed memory is already a valid, empty heap.
    pub(super) fn sub_alloc_blob(&mut self) {
        self.op(SWAP1);
        self.op(DUP1);
        self.push_u64(32 + 31);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        // [ret, len, size]
        self.mload(self.blob_ptr);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.mstore_off(self.blob_ptr);
        // [ret, len, offset]
        self.push_mem(self.blob_base);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(MSTORE);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// `[word, ret]`: the bytes in the high part of `word`, twice their count in its low
    /// byte, become a tagged blob.
    pub(super) fn sub_short_blob(&mut self) -> Result<(), Error> {
        self.op(SWAP1);
        self.op(DUP1);
        self.push_u64(0xff);
        self.op(AND);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(XOR);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(SHR);
        self.alloc_blob()?;
        // [ret, data, header]
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.tag_blob();
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// A packed short string becomes its value: a blob, or the zero word when it is empty.
    pub(super) fn push_short(&mut self, w: Word) {
        self.push_word(w);
        if !w.is_zero() {
            self.call_sub(Sub::ShortBlob);
        }
    }

    /// A literal too long for one word becomes a blob copied from the code, where its
    /// bytes sit zero-padded to whole words, so the blob's last word is clean.
    pub(super) fn push_long(&mut self, bytes: &[u8]) -> Result<(), Error> {
        let mut padded = bytes.to_vec();
        padded.resize(bytes.len().div_ceil(32) * 32, 0);
        let len = padded.len() as u64;
        let marker = self.embed(padded);
        self.copy_long(bytes.len() as u64, len, marker)
    }

    /// A long literal only a revert reads: the helper copies just its bytes to where
    /// everything past them is clean, so the code holds no padding.
    pub(super) fn push_long_unpadded(&mut self, bytes: &[u8]) -> Result<(), Error> {
        let mut padded = bytes.to_vec();
        padded.resize(bytes.len().div_ceil(32) * 32, 0);
        let (len, marker) = match self.literals.get(&padded) {
            Some(&marker) => (padded.len() as u64, marker),
            None => (bytes.len() as u64, self.embed(bytes.to_vec())),
        };
        self.copy_long(bytes.len() as u64, len, marker)
    }

    fn copy_long(&mut self, bytes: u64, len: u64, marker: Word) -> Result<(), Error> {
        self.push_u64(bytes);
        self.alloc_blob()?;
        self.push_u64(len);
        self.push_word(marker);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(CODECOPY);
        self.tag_blob();
        Ok(())
    }

    /// Where `bytes` are appended to the code, once however often they are used. Creation
    /// code keeps them ahead of its end, where its arguments begin.
    fn embed(&mut self, bytes: Vec<u8>) -> Word {
        if let Some(&marker) = self.literals.get(&bytes) {
            return marker;
        }
        let marker = self.data_marker();
        let end = self
            .init
            .then(|| self.data.iter().position(|(m, ..)| *m == self.code_end));
        let at = end.flatten().unwrap_or(self.data.len());
        self.data.insert(at, (marker, bytes.clone(), String::new()));
        self.literals.insert(bytes, marker);
        marker
    }

    /// Header pointer on the stack becomes `(ptr << 1) | 1`.
    pub(super) fn tag_blob(&mut self) {
        self.push_u64(1);
        self.op(SHL);
        self.push_u64(1);
        self.op(OR);
    }

    /// `[len, data, start, end]`, or `[len, data, start]` for a slice to the end, becomes
    /// a copy of the bytes between, checked as Solidity checks a calldata slice.
    pub(super) fn slice_inline(&mut self, end: bool) -> Result<(), Error> {
        if end {
            self.op(DUP1 + 3);
            self.op(DUP1 + 1);
            self.op(GT);
            self.op(DUP1 + 1);
            self.op(DUP1 + 3);
            self.op(GT);
            self.op(OR);
        } else {
            self.op(DUP1 + 2);
            self.op(DUP1 + 1);
            self.op(GT);
        }
        self.revert_if_panic(0x32)?;
        // A slice to the end already has its end, the length, at the bottom.
        if end {
            self.op(SWAP1 + 2);
            self.op(POP);
        }
        // [end, data, start]
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(SUB);
        self.slice_copy()
    }

    /// `[value, start, end, ret]`, or `[value, start, ret]`, becomes the slice.
    pub(super) fn sub_slice(&mut self, end: bool) -> Result<(), Error> {
        self.op(if end { SWAP1 + 2 } else { SWAP1 + 1 });
        self.bytes_span();
        // [ret, start, end, len, data], or [ret, start, len, data]
        if end {
            self.op(DUP1 + 1);
            self.op(DUP1 + 3);
            self.op(GT);
            self.op(DUP1 + 3);
            self.op(DUP1 + 5);
            self.op(GT);
            self.op(OR);
        } else {
            self.op(DUP1 + 1);
            self.op(DUP1 + 3);
            self.op(GT);
        }
        self.revert_if_panic(0x32)?;
        if end {
            self.op(SWAP1);
            self.op(POP);
        }
        // [ret, start, end, data]
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(SWAP1);
        self.op(SUB);
        self.slice_copy()?;
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// `[src, n]` becomes a blob holding the `n` bytes at `src`.
    fn slice_copy(&mut self) -> Result<(), Error> {
        self.op(DUP1);
        self.alloc_blob()?;
        self.op(SWAP1 + 1);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(MCOPY);
        self.tag_blob();
        Ok(())
    }

    /// A bytes or string word becomes `[len, data]` with `data` on top.
    pub(super) fn bytes_span(&mut self) {
        self.call_sub(Sub::BytesSpan);
    }

    /// Counts the digits, then writes them from the end, a `-` first when negative.
    pub(super) fn sub_decimal_string(&mut self, signed: bool) -> Result<(), Error> {
        let [count, counted, fill] = std::array::from_fn(|_| self.fresh());
        self.op(SWAP1);
        if signed {
            // [ret, n] becomes [ret, neg, |n|]: `(n ^ -neg) + neg`.
            self.op(DUP1);
            self.push_u64(255);
            self.op(SHR);
            self.op(DUP1);
            self.op(PUSH0);
            self.op(SUB);
            self.op(DUP1 + 2);
            self.op(XOR);
            self.op(DUP1 + 1);
            self.op(ADD);
            self.op(SWAP1 + 1);
            self.op(POP);
            self.op(SWAP1);
        }
        self.push_u64(1);
        if signed {
            self.op(DUP1 + 2);
            self.op(ADD);
        }
        self.op(DUP1 + 1);
        // [n, len, t] while `t >= 10`
        self.jumpdest(count);
        self.push_u64(10);
        self.op(DUP1 + 1);
        self.op(LT);
        self.push_label(counted);
        self.op(JUMPI);
        self.push_u64(10);
        self.op(SWAP1);
        self.op(DIV);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(ADD);
        self.op(SWAP1);
        self.push_label(count);
        self.op(JUMP);
        self.jumpdest(counted);
        self.op(POP);
        self.op(DUP1);
        self.alloc_blob()?;
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        // [n, ptr, end]: one digit per round, from the last, until `n` is zero.
        self.jumpdest(fill);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.push_u64(10);
        self.op(DUP1 + 3);
        self.op(MOD);
        self.push_u64(48);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.op(MSTORE8);
        self.op(SWAP1 + 1);
        self.push_u64(10);
        self.op(SWAP1);
        self.op(DIV);
        self.op(SWAP1 + 1);
        self.op(DUP1 + 2);
        self.push_label(fill);
        self.op(JUMPI);
        self.op(POP);
        self.op(SWAP1);
        self.op(POP);
        if signed {
            let positive = self.fresh();
            self.op(SWAP1);
            self.op(ISZERO);
            self.push_label(positive);
            self.op(JUMPI);
            self.push_u64(0x2d);
            self.op(DUP1 + 1);
            self.push_u64(32);
            self.op(ADD);
            self.op(MSTORE8);
            self.jumpdest(positive);
        }
        self.tag_blob();
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// Solady's `Base64.encode`: each round turns three bytes into four characters, looked
    /// up in a table whose byte for index `i` sits at `i + 31`, so `MLOAD(i)` ends in it.
    /// The word after the data is zeroed while the rounds read past its end, then restored.
    pub(super) fn sub_base64_encode(&mut self) {
        const ALPHABET: &[u8; 64] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let t = self.base64_tbl;
        let [empty, round, short, done] = std::array::from_fn(|_| self.fresh());
        // [data, file_safe, no_padding, ret]. `0x0670` turns "+/" into "-_".
        self.op(SWAP1 + 1);
        self.push_u64(0x0670);
        self.op(MUL);
        self.push_word(Word::from_be_bytes(ALPHABET[32..].try_into().unwrap()));
        self.op(XOR);
        self.push_mem(t + 0x3f);
        self.op(MSTORE);
        self.push_word(Word::from_be_bytes(ALPHABET[..32].try_into().unwrap()));
        self.push_mem(t + 0x1f);
        self.op(MSTORE);
        self.op(SWAP1 + 1);
        self.bytes_span();
        // [no_padding, ret, len, data]
        self.op(DUP1 + 1);
        self.op(ISZERO);
        self.push_label(empty);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.push_u64(3);
        self.push_u64(2);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(DIV);
        self.push_u64(2);
        self.op(SHL);
        self.op(DUP1);
        self.call_sub(Sub::AllocBlob);
        // [no_padding, ret, len, data, data_end, size, out]
        self.op(SWAP1 + 2);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(DUP1 + 3);
        self.op(MLOAD);
        self.op(PUSH0);
        self.op(DUP1 + 5);
        self.op(MSTORE);
        self.op(SWAP1 + 2);
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        // [no_padding, ret, len, out, data_end, saved, end, ptr, data]
        self.jumpdest(round);
        self.op(DUP1);
        self.op(MLOAD);
        for (k, shift) in [250u64, 244, 238, 232].into_iter().enumerate() {
            if k < 3 {
                self.op(DUP1);
            }
            self.push_u64(shift);
            self.op(SHR);
            if k > 0 {
                self.push_u64(63);
                self.op(AND);
            }
            self.op(MLOAD);
            self.push_mem(t + k as i32);
            self.op(MSTORE8);
        }
        self.push_mem(t);
        self.op(MLOAD);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.push_u64(3);
        self.op(ADD);
        self.op(SWAP1);
        self.push_u64(4);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(LT);
        self.push_label(round);
        self.op(JUMPI);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1 + 1);
        self.op(MSTORE);
        // [no_padding, ret, len, out, end]. Pad with `[0, 2, 1][len % 3]` '='s, then zero
        // what follows the string, dropping the padding if asked.
        self.push_u64(3);
        self.op(DUP1 + 3);
        self.op(MOD);
        self.push_u64(2);
        self.op(DIV);
        self.push_u64(0x3d3d);
        self.push_u64(240);
        self.op(SHL);
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.op(SUB);
        self.op(MSTORE);
        self.op(DUP1 + 5);
        self.op(MUL);
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.op(SUB);
        self.op(MSTORE);
        self.op(SWAP1);
        self.op(SUB);
        self.push_u64(32);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.short_or_blob(short, done);
        // [no_padding, ret, len, result]
        self.op(SWAP1 + 2);
        self.op(POP);
        self.op(POP);
        self.op(JUMP);
        self.jumpdest(empty);
        self.op(POP);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(JUMP);
    }

    /// Solady's `Base64.decode`, which accepts both alphabets, with or without padding, and
    /// ',' for 63 as RFC 3501 does, and does not reject other characters. Each round turns four characters into three bytes
    /// through a table at their own addresses: the byte at a character's address is its
    /// six bits, shifted up two. The table's top byte, at `[`, is `0xfc`, so its last word
    /// doubles as the mask for those bits.
    pub(super) fn sub_base64_decode(&mut self) {
        let mut table = [0u8; 0x80];
        for (i, c) in b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
            .iter()
            .enumerate()
        {
            table[*c as usize] = (i as u8) << 2;
        }
        table[b'-' as usize] = 62 << 2;
        table[b'_' as usize] = 63 << 2;
        table[b',' as usize] = 63 << 2;
        table[b'[' as usize] = 0xfc;
        let word = |at: usize| Word::from_be_bytes(table[at..at + 32].try_into().unwrap());
        let t = self.base64_tbl;
        let [empty, unpadded, sized, round, short, done] = std::array::from_fn(|_| self.fresh());
        self.op(SWAP1);
        self.bytes_span();
        // [ret, len, data]
        self.op(DUP1 + 1);
        self.op(ISZERO);
        self.push_label(empty);
        self.op(JUMPI);
        self.push_u64(3);
        self.op(DUP1 + 2);
        self.push_u64(2);
        self.op(SHR);
        self.op(MUL);
        self.push_u64(3);
        self.op(DUP1 + 3);
        self.op(AND);
        self.op(DUP1);
        self.push_label(unpadded);
        self.op(JUMPI);
        // A length that is a multiple of four may end in one or two '='s.
        self.op(POP);
        self.push_u64(0x3d3d);
        self.push_u64(2);
        self.op(DUP1 + 4);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(SUB);
        self.op(MLOAD);
        self.push_u64(240);
        self.op(SHR);
        self.op(XOR);
        self.op(DUP1);
        self.push_u64(30);
        self.op(BYTE);
        self.op(ISZERO);
        self.op(SWAP1);
        self.push_u64(31);
        self.op(BYTE);
        self.op(ISZERO);
        self.op(ADD);
        self.op(SWAP1);
        self.op(SUB);
        self.push_label(sized);
        self.op(JUMP);
        self.jumpdest(unpadded);
        self.op(ADD);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.jumpdest(sized);
        // [ret, len, data, size]
        self.op(DUP1);
        self.call_sub(Sub::AllocBlob);
        let mask = word(0x5b);
        self.push_word(mask);
        self.op(DUP1);
        self.push_mem(t + 0x5b);
        self.op(MSTORE);
        self.push_word(word(0x3b));
        self.push_mem(t + 0x3b);
        self.op(MSTORE);
        self.push_word(word(0x1a));
        self.push_mem(t + 0x1a);
        self.op(MSTORE);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 5);
        // [ret, len, data, size, out, mask, end, ptr, data]
        self.jumpdest(round);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1);
        self.push_u64(3);
        self.op(BYTE);
        self.op(MLOAD);
        self.push_u64(6);
        self.op(SHR);
        for k in [2u64, 1] {
            self.op(DUP1 + 1);
            self.push_u64(k);
            self.op(BYTE);
            self.op(MLOAD);
            self.op(DUP1 + 6);
            self.op(AND);
            self.op(OR);
            self.push_u64(6);
            self.op(SHR);
        }
        self.op(SWAP1);
        self.op(PUSH0);
        self.op(BYTE);
        self.op(MLOAD);
        self.op(DUP1 + 5);
        self.op(AND);
        self.op(OR);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.push_u64(4);
        self.op(ADD);
        self.op(SWAP1);
        self.push_u64(3);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(LT);
        self.push_label(round);
        self.op(JUMPI);
        self.op(POP);
        self.op(POP);
        self.op(PUSH0);
        self.op(SWAP1);
        self.op(MSTORE);
        self.op(POP);
        self.op(SWAP1);
        self.short_or_blob(short, done);
        // [ret, len, data, result]
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
        self.jumpdest(empty);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// `[out, len]`, with `len` stored at `out`, becomes the tagged blob.
    fn short_or_blob(&mut self, short: u32, done: u32) {
        self.push_u64(32);
        self.op(DUP1 + 1);
        self.op(LT);
        self.push_label(short);
        self.op(JUMPI);
        self.op(POP);
        self.tag_blob();
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(short);
        self.push_u64(1);
        self.op(SHL);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(OR);
        self.call_sub(Sub::ShortBlob);
        self.jumpdest(done);
    }

    /// `[word, ret]` becomes `[len, data]`.
    pub(super) fn sub_bytes_span(&mut self) {
        self.op(SWAP1);
        self.bytes_span_inline();
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        self.op(JUMP);
    }

    fn bytes_span_inline(&mut self) {
        let short = self.fresh();
        let done = self.fresh();
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(short);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SHR);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(short);
        // Only the empty value is a word: its length and data address are both zero.
        self.op(PUSH0);
        self.jumpdest(done);
    }

    pub(super) fn prepend_selector(&mut self, sel: &Expr) -> Result<(), Error> {
        self.mload(self.scratch_a);
        self.mstore_off(self.scratch_b);
        self.compile_value(sel)?;
        self.mstore_off(self.scratch_val);
        self.prepend_saved_selector()
    }

    pub(super) fn prepend_saved_selector(&mut self) -> Result<(), Error> {
        self.mload(self.scratch_b);
        self.op(MLOAD);
        self.push_u64(4);
        self.op(ADD);
        self.alloc_blob()?;
        self.mstore_off(self.scratch_a);
        self.mload(self.scratch_val);
        self.push_u64(224);
        self.op(SHL);
        self.mload(self.scratch_a);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.mload(self.scratch_b);
        self.op(MLOAD);
        self.mload(self.scratch_b);
        self.push_u64(32);
        self.op(ADD);
        self.mload(self.scratch_a);
        self.push_u64(36);
        self.op(ADD);
        self.op(MCOPY);
        self.mload(self.scratch_a);
        self.tag_blob();
        Ok(())
    }

    pub(super) fn precompile(
        &mut self,
        addr: u64,
        off: i32,
        len: i32,
        out: u64,
    ) -> Result<(), Error> {
        self.push_u64(out);
        self.push_mem(self.ret_scratch);
        self.mload(len);
        self.mload(off);
        self.push_u64(addr);
        self.op(GAS);
        self.op(STATICCALL);
        self.op(ISZERO);
        self.revert_if_true()?;
        self.mload(self.ret_scratch);
        Ok(())
    }
}
