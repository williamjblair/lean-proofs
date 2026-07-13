# Erdős 686, k=22 Archimedean Core Plan

## Scope

Generate an isolated ordinary-kernel formalization of the audited k=22
Archimedean reduction.  The only Lean outputs are uniquely named
`Erdos686EvenK22Defs`, `Erdos686EvenK22FiniteStripS*`,
`Erdos686EvenK22FiniteStrip`, and `Erdos686EvenK22Core` modules.

## Exact theorem surface

1. Export `evenTable22S` and `evenTable22T` in
   `Erdos686.Erdos686Variant`.
2. Prove the centered product identity at scale `2^22 = 4194304` and the
   square identity `T^2 = 256^2 S + D`.
3. Prove `33 | T(2a+1)`, prove 33 is maximal by a Bezout combination of
   `T(1)` and `T(3)`, and prove `T(2a+1)` is odd.
4. Route gaps 22 through 26 to the already proved quadratic-strip theorem.
5. Certify all exact finite-strip cases for gaps 27 through 249 by ordinary
   `decide` shards and route them through one finite-strip theorem.
6. For gaps at least 250, prove the Runge reduction to an odd natural
   candidate `t` satisfying `1 <= t <= 3795146531` and
   `T(w)-2T(v) = -33t`.

## Verification order

1. Run the exact Python verifier and compare every constant to the existing
   independent sieve probe.
2. Generate Lean files deterministically.
3. Compile definitions, every finite shard, the router, and the core with
   `lake env lean`; no `native_decide` is permitted.
4. Inspect declarations with `#print axioms` and grep generated files for
   disallowed mechanisms.

## Deliberate stopping point

This task does not formalize the packed local cover.  Its exact output gap is
the finite contradiction for odd `t <= 3795146531` satisfying the centered
equation and error equation.  The separate packed-cover work consumes the
exported S/T definitions and oddness witness.
