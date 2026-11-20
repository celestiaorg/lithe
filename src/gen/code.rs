//! The instructions the dispatcher and the stubs around it are written with.

use super::*;

impl<'a> Gen<'a> {
    pub(super) fn revert_empty(&mut self) {
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(REVERT);
    }

    pub(super) fn push_selector(&mut self, sel: [u8; 4]) {
        self.push_u64(u64::from(u32::from_be_bytes(sel)));
    }

    pub(super) fn push_word(&mut self, w: Word) {
        self.code.push(Inst::Push(w));
    }

    pub(super) fn push_u64(&mut self, n: u64) {
        self.push_word(Word::from_u64(n));
    }

    pub(super) fn op(&mut self, b: u8) {
        if b == PUSH0 {
            self.push_u64(0);
        } else if b == CALLDATASIZE && self.cd_tail > 0 {
            // A facet's calldata ends where the immutables its router appended begin.
            self.push_u64(self.cd_tail);
            self.code.push(Inst::Op(CALLDATASIZE));
            self.code.push(Inst::Op(SUB));
        } else {
            self.code.push(Inst::Op(b));
        }
    }

    pub(super) fn fresh(&mut self) -> u32 {
        self.next_label += 1;
        self.next_label
    }

    pub(super) fn push_label(&mut self, id: u32) {
        self.code.push(Inst::PushLabel(id));
    }

    /// Reads a storage leaf as a full word, unpacking it from a shared slot.
    pub(super) fn sload_leaf(&mut self, leaf: u32) {
        self.push_word(self.checked.leaf_keys[leaf as usize]);
        self.op(SLOAD);
        self.unpack(self.checked.leaf_pack[leaf as usize]);
    }

    /// A slot's word on the stack becomes the value packed at `pack`.
    pub(super) fn unpack(&mut self, pack: Pack) {
        if pack.is_full() {
            return;
        }
        if pack.offset > 0 {
            self.push_u64(u64::from(pack.offset) * 8);
            self.op(SHR);
        }
        if pack.signed {
            self.push_u64(u64::from(pack.width) - 1);
            self.op(SIGNEXTEND);
        } else if pack.offset + pack.width < 32 {
            self.push_word(byte_mask(pack.width));
            self.op(AND);
        }
    }

    pub(super) fn jumpdest(&mut self, id: u32) {
        self.code.push(Inst::Label(id));
    }
}
