# Security

Lithe is experimental, and neither the compiler nor the standard library has been audited. Don't rely on it to secure real value yet.

## Reporting a vulnerability

Report it privately through [GitHub's security advisories](https://github.com/celestiaorg/lithe/security/advisories/new), not in a public issue.

Include:

- the Lithe version (`lithe --version`);
- the smallest source that shows the problem, and the command you ran;
- what the contract should do and what it does instead, for example a transaction that succeeds when it should revert, or the wrong storage slot written.

Expect a reply within a week. We will tell you once there is a fix, and credit you in the advisory unless you would rather we didn't.

## Scope

In scope:

- **Miscompilation:** bytecode that doesn't do what the source says, such as a skipped check, wrong arithmetic, a storage collision, or a deferred call that runs early.
- **Checks the compiler claims but doesn't enforce:** effects, declared errors, access rules, or the upgrade guards.
- **The standard library:** a module that breaks its documented behavior.
- **`lithe prove`:** a claim reported as proved that the bytecode violates.
- **Distribution:** the release binaries, `install.sh`, and the `@lithe-lang/hardhat` package.

Out of scope:

- bugs in contracts written in Lithe, unless the compiler or standard library causes them;
- compiler crashes and rejected programs that don't produce bytecode (file a [regular issue](https://github.com/celestiaorg/lithe/issues));
- the docs site and playground, except for anything that would run attacker-supplied code in a visitor's browser.

## Supported versions

Only the latest release gets fixes.
