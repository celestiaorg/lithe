"""Prints a synthetic contract of N independent entrypoints, each with a loop, a map
write, and an event, for measuring how compile time scales: `python3 scripts/gen_scaling.py N`."""

import sys

n = int(sys.argv[1])
out = ['import "std/evm";', '', 'error Bad;', '', 'storage is record {']
for i in range(n):
    out += [f'  a{i} : uint;', f'  m{i} : map(address, uint);']
out += ['}', '']
for i in range(n):
    out.append(f'''event E{i} of record {{
  who : address;
  v : uint;
}}

external function f{i}(const x : uint; const y : uint) : uint
  raises Bad
is {{
  assert(x > y, Bad);
  const old : uint := storage.a{i};
  var acc : uint := old;
  for k : uint in 0 .. x bound 64 do {{
    acc := acc + (k * y) / (x + 1);
  }}
  storage.a{i} := acc;
  storage.m{i}[Evm.sender()] := storage.m{i}[Evm.sender()] + acc;
  emit E{i} {{
    who = Evm.sender();
    v = acc;
  }};
}} with acc - old

external view function g{i}(const who : address) : uint is
  storage.m{i}[who] + storage.a{i}
''')
print('\n'.join(out))
