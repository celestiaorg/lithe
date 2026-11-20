//! What an upgradeable contract's code adds to its entrypoints: `deploy` and its
//! migrations, each of which runs once, and OpenZeppelin's UUPS pair, `proxiableUUID` and
//! `upgradeToAndCall`.

use super::*;

/// An entrypoint that runs once.
#[derive(Clone, Copy, PartialEq)]
pub(super) enum Once {
    /// `deploy`, while the proxy calling it has no code yet: inside the proxy's
    /// constructor, against the proxy's storage.
    Deploy,
    /// A migration, while the upgrade that calls it runs.
    Migrate,
}

impl Lower<'_> {
    /// The address the implementation was created at, which the creation code writes.
    fn own_address(&self, cx: &mut Cx) -> V {
        cx.b.imm(immutable::SELF_MARK, 20)
    }

    /// Reverts with an error that has no parameters, or one word.
    fn revert_with(&self, cx: &mut Cx, sig: &str, arg: Option<V>) {
        let sel = cx.b.num(u64::from(u32::from_be_bytes(selector(sig))));
        let (zero, word) = (cx.b.num(0), cx.b.num(32));
        self.mstore(cx, zero, sel);
        if let Some(arg) = arg {
            self.mstore(cx, word, arg);
        }
        let (at, n) = (cx.b.num(28), cx.b.num(if arg.is_some() { 36 } else { 4 }));
        cx.b.exit(Term::RevertAt(vec![at, n]));
    }

    /// What lets an entrypoint that runs once run.
    pub(super) fn gate(&mut self, cx: &mut Cx, once: Once) {
        match once {
            Once::Migrate => {
                let slot = cx.b.num(UPGRADE_SLOT);
                let flag = cx.b.load(slot, true);
                let one = cx.b.num(1);
                let open = cx.b.op2(EQ, flag, one);
                let shut = cx.b.is_zero(open);
                self.guard(cx, shut, |l, cx| l.revert_empty(cx));
            }
            Once::Deploy => {
                let here = cx.b.env(ADDRESS);
                let size = cx.b.effect(Op::Evm(EXTCODESIZE), vec![here], 1);
                self.guard(cx, size, |l, cx| l.revert_empty(cx));
            }
        }
    }

    /// OpenZeppelin's `notDelegated`: only the implementation itself answers, so a proxy
    /// can't be upgraded to another proxy.
    pub(super) fn proxiable(&mut self) -> Result<Func, Error> {
        let mut cx = Cx::new("proxiableUUID", Vec::new());
        self.refuse_value(&mut cx, false);
        let (own, here) = (self.own_address(&mut cx), cx.b.env(ADDRESS));
        let other = cx.b.op2(XOR, own, here);
        self.guard(&mut cx, other, |l, cx| {
            l.revert_with(cx, "UUPSUnauthorizedCallContext()", None)
        });
        let slot = cx.b.word(crate::keccak::erc1967_implementation());
        let (zero, word) = (cx.b.num(0), cx.b.num(32));
        self.mstore(&mut cx, zero, slot);
        cx.b.exit(Term::ReturnAt(vec![zero, word]));
        Ok(cx.b.f)
    }

    /// OpenZeppelin 5.1's `upgradeToAndCall`, in its order: the arguments decode, the call
    /// runs through a proxy that points at this implementation (`onlyProxy`), the guard
    /// passes, and the new implementation's `proxiableUUID` is the implementation slot.
    pub(super) fn upgrade(&mut self) -> Result<Func, Error> {
        self.journaled(|l| l.upgrade_in())
    }

    fn upgrade_in(&mut self) -> Result<Func, Error> {
        let mut cx = Cx::new("upgradeToAndCall", Vec::new());
        self.upgrade_body(&mut cx)?;
        Ok(cx.b.f)
    }

    fn upgrade_body(&mut self, cx: &mut Cx) -> Result<(), Error> {
        cx.b.journal = self.journal.map(|(load, store, _)| (load, store));
        let size = cx.b.env(CALLDATASIZE);
        let need = cx.b.num(68);
        let short = cx.b.op2(LT, size, need);
        let to = cx.b.cd_word(4);
        let k = cx.b.num(160);
        let high = cx.b.op2(SHR, k, to);
        let bad = cx.b.op2(OR, short, high);
        self.guard(cx, bad, |l, cx| l.revert_empty(cx));
        let Val::CdBytes(data, len) = self.decode_bytes(cx, 1)? else {
            unreachable!()
        };
        let slot = cx.b.word(crate::keccak::erc1967_implementation());
        let (own, here) = (self.own_address(cx), cx.b.env(ADDRESS));
        let direct = cx.b.op2(EQ, own, here);
        let current = cx.b.load(slot, false);
        let other = cx.b.op2(XOR, current, own);
        let wrong = cx.b.op2(OR, direct, other);
        self.guard(cx, wrong, |l, cx| {
            l.revert_with(cx, "UUPSUnauthorizedCallContext()", None)
        });
        let Some(guard) = &self.c.prog.guard else {
            return Err(error(
                1,
                1,
                "upgradeable contract requires an upgrade guard",
            ));
        };
        self.top(cx, &guard.stmts, None)?;
        self.finish(cx);
        if cx.b.dead {
            return Ok(());
        }
        // What follows is the upgrade's own, made as it is written.
        cx.b.journal = None;
        // A failed call is `ERC1967InvalidImplementation`; an answer too short to decode
        // reverts with nothing, as Solidity's `try` does.
        let (zero, word) = (cx.b.num(0), cx.b.num(32));
        let sel =
            cx.b.num(u64::from(u32::from_be_bytes(selector("proxiableUUID()"))));
        self.mstore(cx, zero, sel);
        let (at, four) = (cx.b.num(28), cx.b.num(4));
        let ok = cx.b.effect(Op::StaticAt, vec![to, at, four, zero, word], 1);
        let failed = cx.b.is_zero(ok);
        self.guard(cx, failed, |l, cx| {
            l.revert_with(cx, "ERC1967InvalidImplementation(address)", Some(to))
        });
        let answered = cx.b.effect(Op::RetSize, Vec::new(), 1);
        let less = cx.b.op2(LT, answered, word);
        self.guard(cx, less, |l, cx| l.revert_empty(cx));
        let uuid = cx.b.effect(Op::MLoad, vec![zero], 1);
        let differs = cx.b.op2(XOR, uuid, slot);
        self.guard(cx, differs, |l, cx| {
            l.revert_with(cx, "UUPSUnsupportedProxiableUUID(bytes32)", Some(uuid))
        });
        cx.b.store(slot, to, false);
        // ERC-1967's `Upgraded(address indexed implementation)`, before the migration runs.
        let topic = Word::from_be_bytes(crate::keccak::keccak256(b"Upgraded(address)"));
        let topic = cx.b.word(topic);
        let none = Enc {
            sel: None,
            abi: true,
            parts: Vec::new(),
        };
        cx.b.effect(Op::Log(2, none), vec![topic, to], 0);
        self.branch(
            cx,
            len,
            |l, cx| {
                // The flag a migration checks is set only for the migration's call, so
                // no one can call one later in the transaction.
                let (gate, one, zero) = (cx.b.num(UPGRADE_SLOT), cx.b.num(1), cx.b.num(0));
                cx.b.store(gate, one, true);
                let at = cx.top;
                cx.b.effect(Op::CdCopy, vec![at, data, len], 0);
                let ok =
                    cx.b.effect(Op::DelegateAt, vec![to, at, len, zero, zero], 1);
                // A failed migration's revert data goes back as it is, or `FailedCall()`
                // when it has none, as OpenZeppelin's `Address` bubbles it.
                let failed = cx.b.is_zero(ok);
                l.guard(cx, failed, |l, cx| {
                    let size = cx.b.effect(Op::RetSize, Vec::new(), 1);
                    let none = cx.b.is_zero(size);
                    l.guard(cx, none, |l, cx| l.revert_with(cx, "FailedCall()", None));
                    cx.b.effect(Op::RetCopy, vec![zero, zero, size], 0);
                    cx.b.exit(Term::RevertAt(vec![zero, size]));
                });
                cx.b.store(gate, zero, true);
                cx.b.exit(Term::Stop);
                Ok(Val::Unit)
            },
            |l, cx| {
                // With no migration to take it, value is refused, as `ERC1967Utils`
                // refuses it.
                let value = cx.b.env(CALLVALUE);
                l.guard(cx, value, |l, cx| {
                    l.revert_with(cx, "ERC1967NonPayable()", None)
                });
                cx.b.exit(Term::Stop);
                Ok(Val::Unit)
            },
        )?;
        Ok(())
    }
}
