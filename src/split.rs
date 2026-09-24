//! Contracts over the code size limit. The compiler keeps what fits in a router and puts the
//! rest in parts, which the router reaches with `delegatecall`. Parts are deployed with
//! `CREATE2` through a factory, so their addresses are known here and built into the router.

use std::collections::{HashMap, HashSet};

use crate::check::Checked;
use crate::gen::{self, Built, Entrypoint, Group};
use crate::keccak::keccak256;
use crate::word::Word;
use crate::{error, Error};

/// EIP-170's limit on deployed code.
pub const SIZE_LIMIT: usize = 24_576;

/// The deterministic deployment proxy Foundry uses: calldata is a 32-byte salt, then the
/// creation code, and it returns the created address.
pub const DEPLOYER: [u8; 20] = [
    0x4e, 0x59, 0xb4, 0x48, 0x47, 0xb3, 0x79, 0x57, 0x85, 0x88, 0x92, 0x0c, 0xa7, 0x8f, 0xbf,
    0x26, 0xc0, 0xb4, 0x95, 0x6c,
];

/// How contracts are fitted to the size limit.
#[derive(Clone, Debug)]
pub struct Options {
    /// The most runtime code the router or any part may have. Creation code may have twice
    /// this, as EIP-3860 allows.
    pub size_limit: usize,
    /// Split a contract over the limit. Without it, such a contract is an error.
    pub split: bool,
    /// The `CREATE2` factory parts are deployed through.
    pub deployer: [u8; 20],
}

impl Default for Options {
    fn default() -> Self {
        Self {
            size_limit: SIZE_LIMIT,
            split: true,
            deployer: DEPLOYER,
        }
    }
}

/// What one build compiles: every entrypoint, or a router's or a part's share.
#[derive(Clone, Default)]
pub(crate) struct Shape {
    /// The selectors this code runs itself. `None` runs every one.
    pub keep: Option<HashSet<[u8; 4]>>,
    /// Selectors forwarded to a part, by the part's index.
    pub forward: Vec<([u8; 4], usize)>,
    /// The parts' addresses.
    pub parts: Vec<Word>,
    /// A part: its creation code only copies it, since `deploy` belongs to the router.
    pub part: bool,
    pub opts: Options,
}

/// A part: its name, its `CREATE2` address, its code, and the entrypoints it runs.
#[derive(Clone)]
pub(crate) struct Part {
    pub name: String,
    pub address: [u8; 20],
    pub init: Vec<u8>,
    pub runtime: Vec<u8>,
    pub entries: Vec<Entrypoint>,
    /// Parts of contracts this part creates.
    pub needs: Vec<Part>,
}

/// A contract as it deploys: the router's code, and its parts. A contract that fits has no
/// parts, and its router is exactly the code an unsplit build produces.
pub(crate) struct Split {
    pub creation: Vec<u8>,
    pub runtime: Vec<u8>,
    /// The entrypoints the router runs itself, when it has parts.
    pub entries: Vec<Entrypoint>,
    pub parts: Vec<Part>,
    /// Parts of contracts the router creates.
    pub needs: Vec<Part>,
    /// The unsplit runtime's size, when it had to split and could be assembled at all.
    pub whole: Option<usize>,
}

impl Split {
    /// Everything to deploy before the router: the parts of what it creates, then its own,
    /// each address once.
    pub(crate) fn prerequisites(&self) -> Vec<Part> {
        let mut out: Vec<Part> = Vec::new();
        let mut seen = HashSet::new();
        let mut add = |part: &Part, out: &mut Vec<Part>| {
            if seen.insert(part.address) {
                out.push(part.clone());
            }
        };
        for need in &self.needs {
            add(need, &mut out);
        }
        for part in &self.parts {
            for need in &part.needs {
                add(need, &mut out);
            }
        }
        for part in &self.parts {
            add(part, &mut out);
        }
        out
    }
}

/// Compiles a contract, splitting it when it does not fit.
pub(crate) fn build(checked: &Checked, name: &str, opts: &Options) -> Result<Split, Error> {
    let whole_shape = Shape {
        opts: opts.clone(),
        ..Shape::default()
    };
    let whole = match gen::codegen(checked, &whole_shape) {
        Ok(built) if fits(&built, opts.size_limit) => {
            return Ok(Split {
                creation: built.code,
                runtime: built.runtime,
                entries: Vec::new(),
                parts: Vec::new(),
                needs: built.needs,
                whole: None,
            });
        }
        Ok(built) => Some(built.runtime.len()),
        Err(err) if too_large(&err) => None,
        Err(err) => return Err(err),
    };
    let entries = gen::entrypoints(checked)?;
    let groups = groups(checked, &entries);
    if !opts.split {
        return Err(oversized(checked, name, opts, &entries, &groups, whole));
    }
    let mut planner = Planner {
        checked,
        opts,
        entries: &entries,
        parts: HashMap::new(),
    };
    let (pinned, rest): (Vec<_>, Vec<_>) = groups
        .into_iter()
        .partition(|(group, _)| *group == Group::Upgrade);
    let pinned: Vec<usize> = pinned.into_iter().flat_map(|(_, idx)| idx).collect();
    // The router takes whole groups, in order, while the next still fits. Measured with
    // every other selector forwarded to one stand-in part at the widest address.
    let wide = Word::from_be_bytes([0xff; 32]).shr(96);
    let mut take = 0;
    while take < rest.len() {
        let keep = router_keep(&pinned, &rest[..=take]);
        let forward = entries
            .iter()
            .enumerate()
            .filter(|(i, _)| !keep.contains(i))
            .map(|(_, entry)| (entry.sel, 0))
            .collect();
        let shape = Shape {
            keep: Some(sels(&entries, &keep)),
            forward,
            parts: vec![wide],
            part: false,
            opts: opts.clone(),
        };
        if planner.measure(&shape)?.is_none() {
            break;
        }
        take += 1;
    }
    // The real parts can need more stubs than the stand-in did. Then the router gives
    // back its last group, and the parts are packed again.
    loop {
        let placed = planner.pack(&rest[take..], name)?;
        let keep = router_keep(&pinned, &rest[..take]);
        let mut forward = Vec::new();
        let mut addresses = Vec::new();
        for (i, part) in placed.iter().enumerate() {
            for entry in &part.entries {
                forward.push((entry.sel, i));
            }
            addresses.push(address_word(part.address));
        }
        let shape = Shape {
            keep: Some(sels(&entries, &keep)),
            forward,
            parts: addresses,
            part: false,
            opts: opts.clone(),
        };
        if let Some(router) = planner.measure(&shape)? {
            return Ok(Split {
                creation: router.code,
                runtime: router.runtime,
                entries: keep.iter().map(|&i| entries[i].clone()).collect(),
                parts: placed,
                needs: router.needs,
                whole,
            });
        }
        if take == 0 {
            let built = gen::codegen(checked, &shape).ok();
            return Err(error(
                0,
                0,
                format!("contract `{name}`'s router {}", too_big(built.as_ref(), opts)),
            ));
        }
        take -= 1;
    }
}

/// The router's entrypoints, in dispatch order.
fn router_keep(pinned: &[usize], groups: &[(Group, Vec<usize>)]) -> Vec<usize> {
    let mut keep: Vec<usize> = pinned.to_vec();
    keep.extend(groups.iter().flat_map(|(_, idx)| idx.iter().copied()));
    keep.sort_unstable();
    keep
}

fn sels(entries: &[Entrypoint], idx: &[usize]) -> HashSet<[u8; 4]> {
    idx.iter().map(|&i| entries[i].sel).collect()
}

fn fits(built: &Built, limit: usize) -> bool {
    built.runtime.len() <= limit && built.code.len() <= 2 * limit
}

/// The assembler's own limit: jump targets are at most two bytes.
fn too_large(err: &Error) -> bool {
    err.line == 0 && err.message == "contract too large"
}

/// The groups in placement order: upgrade machinery, the contract's own functions, then
/// each module in `use` order. Entrypoints keep dispatch order within a group.
fn groups(checked: &Checked, entries: &[Entrypoint]) -> Vec<(Group, Vec<usize>)> {
    let mut order = vec![Group::Upgrade, Group::Contract];
    for module in &checked.prog.compose {
        order.push(Group::Module(module.name.clone()));
    }
    for entry in entries {
        if !order.contains(&entry.group) {
            order.push(entry.group.clone());
        }
    }
    order
        .into_iter()
        .filter_map(|group| {
            let idx: Vec<usize> = entries
                .iter()
                .enumerate()
                .filter(|(_, entry)| entry.group == group)
                .map(|(i, _)| i)
                .collect();
            (!idx.is_empty()).then_some((group, idx))
        })
        .collect()
}

struct Planner<'a> {
    checked: &'a Checked,
    opts: &'a Options,
    entries: &'a [Entrypoint],
    /// Each part compiled so far, by its entrypoints: `None` when it does not fit.
    parts: HashMap<Vec<usize>, Option<Built>>,
}

impl Planner<'_> {
    /// Compiles `shape`, or `None` when the code does not fit.
    fn measure(&self, shape: &Shape) -> Result<Option<Built>, Error> {
        match gen::codegen(self.checked, shape) {
            Ok(built) if fits(&built, self.opts.size_limit) => Ok(Some(built)),
            Ok(_) => Ok(None),
            Err(err) if too_large(&err) => Ok(None),
            Err(err) => Err(err),
        }
    }

    fn part_shape(&self, idx: &[usize]) -> Shape {
        Shape {
            keep: Some(sels(self.entries, idx)),
            forward: Vec::new(),
            parts: Vec::new(),
            part: true,
            opts: self.opts.clone(),
        }
    }

    fn part(&mut self, idx: &[usize]) -> Result<Option<&Built>, Error> {
        if !self.parts.contains_key(idx) {
            let built = self.measure(&self.part_shape(idx))?;
            self.parts.insert(idx.to_vec(), built);
        }
        Ok(self.parts[idx].as_ref())
    }

    fn fits(&mut self, idx: &[usize]) -> Result<bool, Error> {
        Ok(self.part(idx)?.is_some())
    }

    /// `fits` for each set, compiling the ones not seen yet in parallel.
    fn fits_all(&mut self, sets: &[Vec<usize>]) -> Result<Vec<bool>, Error> {
        let new: Vec<&Vec<usize>> = sets
            .iter()
            .filter(|idx| !self.parts.contains_key(*idx))
            .collect();
        let this = &*self;
        let built: Vec<_> = std::thread::scope(|s| {
            let handles: Vec<_> = new
                .iter()
                .map(|idx| {
                    std::thread::Builder::new()
                        .stack_size(64 << 20)
                        .spawn_scoped(s, move || this.measure(&this.part_shape(idx)))
                        .expect("spawn a codegen thread")
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_else(|e| std::panic::resume_unwind(e)))
                .collect()
        });
        for (idx, built) in new.into_iter().zip(built) {
            self.parts.insert(idx.clone(), built?);
        }
        Ok(sets.iter().map(|idx| self.parts[idx].is_some()).collect())
    }

    /// Fills parts with whole groups in order. A group that does not fit in the current part
    /// starts the next one; a group that fits in no part is split by entrypoint.
    fn pack(&mut self, groups: &[(Group, Vec<usize>)], name: &str) -> Result<Vec<Part>, Error> {
        let mut placed: Vec<Vec<usize>> = Vec::new();
        let mut current: Vec<usize> = Vec::new();
        for (_, idx) in groups {
            if !current.is_empty() {
                let mut grown = current.clone();
                grown.extend(idx);
                if self.fits(&grown)? {
                    current = grown;
                    continue;
                }
                placed.push(std::mem::take(&mut current));
            }
            if self.fits(idx)? {
                current = idx.clone();
                continue;
            }
            // Each probe is a full build, so the longest prefix that still fits is found by
            // searching several prefix lengths at once. Code only grows with entrypoints, so
            // this matches adding one at a time.
            let ways = std::thread::available_parallelism().map_or(1, |n| (n.get() / 2).max(1));
            let mut rest = &idx[..];
            while !rest.is_empty() {
                let (mut lo, mut hi) = (0, rest.len());
                while lo < hi {
                    let mut probes: Vec<usize> = (1..=ways)
                        .map(|j| lo + ((hi - lo) * j).div_ceil(ways + 1))
                        .collect();
                    probes.dedup();
                    let sets: Vec<Vec<usize>> = probes
                        .iter()
                        .map(|&m| [&current[..], &rest[..m]].concat())
                        .collect();
                    for (m, ok) in probes.into_iter().zip(self.fits_all(&sets)?) {
                        if !ok {
                            hi = m - 1;
                            break;
                        }
                        lo = m;
                    }
                }
                if lo == 0 && current.is_empty() {
                    let one = rest[0];
                    let shape = Shape {
                        keep: Some(sels(self.entries, &[one])),
                        part: true,
                        opts: self.opts.clone(),
                        ..Shape::default()
                    };
                    let built = gen::codegen(self.checked, &shape).ok();
                    return Err(error(
                        0,
                        0,
                        format!(
                            "entrypoint `{}` {}",
                            self.entries[one].name,
                            too_big(built.as_ref(), self.opts)
                        ),
                    ));
                }
                current.extend(&rest[..lo]);
                rest = &rest[lo..];
                if !rest.is_empty() {
                    placed.push(std::mem::take(&mut current));
                }
            }
        }
        if !current.is_empty() {
            placed.push(current);
        }
        let (deployer, entries) = (self.opts.deployer, self.entries);
        let mut parts = Vec::new();
        for (i, idx) in placed.into_iter().enumerate() {
            let built = self
                .part(&idx)?
                .ok_or_else(|| error(0, 0, "internal: a placed part does not fit"))?;
            parts.push(Part {
                name: format!("{name}.{}", i + 1),
                address: create2(&deployer, &built.code),
                init: built.code.clone(),
                runtime: built.runtime.clone(),
                entries: idx.iter().map(|&e| entries[e].clone()).collect(),
                needs: built.needs.clone(),
            });
        }
        Ok(parts)
    }
}

/// With splitting off: the size, and what each group adds to it.
fn oversized(
    checked: &Checked,
    name: &str,
    opts: &Options,
    entries: &[Entrypoint],
    groups: &[(Group, Vec<usize>)],
    whole: Option<usize>,
) -> Error {
    let limit = thousands(opts.size_limit);
    let Some(whole) = whole else {
        return error(
            0,
            0,
            format!("contract `{name}` is over 65,535 bytes; the limit is {limit}"),
        );
    };
    let mut rows: Vec<(String, usize)> = Vec::new();
    for (group, idx) in groups {
        let rest: Vec<usize> = (0..entries.len()).filter(|i| !idx.contains(i)).collect();
        let shape = Shape {
            keep: Some(sels(entries, &rest)),
            opts: opts.clone(),
            ..Shape::default()
        };
        let without = gen::codegen(checked, &shape).map_or(0, |built| built.runtime.len());
        rows.push((label(group, name), whole.saturating_sub(without)));
    }
    rows.sort_by_key(|row| std::cmp::Reverse(row.1));
    let attributed: usize = rows.iter().map(|(_, n)| n).sum();
    rows.push((
        "(dispatch and shared code)".to_string(),
        whole.saturating_sub(attributed),
    ));
    let width = rows.iter().map(|(label, _)| label.len()).max().unwrap_or(0);
    let digits = rows
        .iter()
        .map(|(_, n)| thousands(*n).len())
        .max()
        .unwrap_or(0);
    let mut msg = format!(
        "contract `{name}` is {} bytes; the limit is {limit}",
        thousands(whole)
    );
    for (label, n) in rows {
        msg.push_str(&format!("\n  {label:width$}  {:>digits$}", thousands(n)));
    }
    error(0, 0, msg)
}

/// Why code on its own does not fit: its runtime, or its creation code, is over the limit.
fn too_big(built: Option<&Built>, opts: &Options) -> String {
    let limit = opts.size_limit;
    match built {
        Some(built) if built.runtime.len() <= limit => format!(
            "has {} bytes of creation code on its own; the limit is {}",
            thousands(built.code.len()),
            thousands(2 * limit)
        ),
        Some(built) => format!(
            "is {} bytes on its own; the limit is {}",
            thousands(built.runtime.len()),
            thousands(limit)
        ),
        None => format!(
            "is over 65,535 bytes on its own; the limit is {}",
            thousands(limit)
        ),
    }
}

/// How a group is listed: the module's name, the contract's, or `upgrade`.
pub(crate) fn label(group: &Group, contract: &str) -> String {
    match group {
        Group::Upgrade => "upgrade".to_string(),
        Group::Contract => contract.to_string(),
        Group::Module(module) => module.clone(),
    }
}

/// `31204` as `31,204`.
pub(crate) fn thousands(n: usize) -> String {
    let digits = n.to_string();
    let mut out = String::new();
    for (i, ch) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(ch);
    }
    out
}

/// Where the factory creates `init` with a zero salt.
pub(crate) fn create2(deployer: &[u8; 20], init: &[u8]) -> [u8; 20] {
    let mut buf = vec![0xff];
    buf.extend_from_slice(deployer);
    buf.extend_from_slice(&[0u8; 32]);
    buf.extend_from_slice(&keccak256(init));
    let hash = keccak256(&buf);
    let mut out = [0u8; 20];
    out.copy_from_slice(&hash[12..]);
    out
}

pub(crate) fn address_word(address: [u8; 20]) -> Word {
    let mut word = [0u8; 32];
    word[12..].copy_from_slice(&address);
    Word::from_be_bytes(word)
}
