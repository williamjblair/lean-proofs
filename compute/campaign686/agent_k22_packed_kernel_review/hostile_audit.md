# Hostile review: original k=22 packed-kernel probe

## Verdict

The generic bit semantics in `PackedPeriodicCover.lean` are sound and pass the
ordinary axiom gate.  The concrete zero claim in `ActualShardProbe.lean` is
reproduced by independent exact arithmetic, but the file is **not presently a
kernel-checked certificate**: its 20,000,000-bit `decide +kernel` theorem
stack-overflows Lean before an `.olean` or axiom report is produced.

The isolated file `P23ParityDecomposition.lean` does kernel-check the exact
parity plus `p = 23` decomposition

```text
t = 46*q+a,  a in {17,21,25,29}.
```

## Dependency tree

| Node | Exact statement | Verdict |
|---|---|---|
| B1 | A true local residue bit implies the corresponding packed bit is true for every `i < min(w,p*2^e)`. | PASS, Lean checked |
| B2 | No converse from a packed bit to a local residue bit is used. Extra true bits can only make a zero intersection harder to prove. | PASS |
| E | Early exit at a zero accumulator is sound. A tracked true bit proves the current accumulator is nonzero, so the semantic induction cannot take the early-zero branch. Zero itself is absorbing. | PASS, Lean checked |
| W | In the concrete file, `w=20,000,000`, `e=18`, and the least period is `83`, so `83*2^18=21,757,952>w`. Every required strict bound follows from `i<w`. | PASS, exact arithmetic |
| P | Every one of the 132 patterns is below `2^p`, hence is a genuine one-period low-bit-first mask. All 132 `(p,pattern)` pairs match an independent reconstruction from the displayed `S,T` polynomials. | PASS, exact arithmetic |
| Z | The exact 20,000,000-bit intersection is zero; it first becomes zero after the `p=857` mask. | PASS as exact-arithmetic reproduction |
| K | `actualShardIntersection_zero` compiles and its axioms can be inspected. | **FAIL: stack overflow** |
| M23 | Direct enumeration of all 529 `(w,v)` pairs modulo 23 gives exactly `{2,6,17,21}`, mask numeral `2,228,292`. | PASS, independent exact arithmetic |
| D46 | Odd parity combined with M23 is exactly the four classes `{17,21,25,29}` modulo 46. | PASS, Lean checked |

## One-direction semantics

The generator sets bit `r` precisely by adding `2^r`, so masks are
low-bit-first. `periodicPowMask_getLsbD_true` proves only

```text
pattern.testBit (i % p) = true
  -> (periodicPowMask w p pattern e).getLsbD i = true
```

under `i<w` and `i<p*2^e`. It never assumes the reverse implication. This is
the correct direction for exclusion: if a genuine candidate survives every
local condition, its index bit survives every packed mask; a certified zero
intersection then contradicts that fact. Bits above the first period would
only introduce false positives, not false exclusions. In the concrete file
they are absent anyway because every pattern is less than `2^p`.

## Early-zero logic

The recursive intersection returns zero immediately when its accumulator is
zero. In the induction proving preservation of a tracked bit, the hypothesis

```text
acc.getLsbD i = true
```

implies `acc != 0`; after the next bitwise `and`, the tracked bit remains true,
so the same argument repeats. Thus early exit cannot skip a mask along a
hypothetical surviving candidate. The isolated theorem
`intersectPeriodicItems_zero` additionally checks that zero is absorbing.

## Width and exponent boundary

The proof requires a strict bound for every item:

```text
i < p * 2^18.
```

The concrete theorem assumes `i<20,000,000`. The smallest period is 83, and

```text
83 * 2^18 = 21,757,952 > 20,000,000.
```

All other periods are larger. There is no endpoint loss: the largest admitted
index is 19,999,999. The generator's docstring still describes a one-million
index probe, while the checked source contains a 20-million index probe; this
is stale prose, not a semantic mismatch.

## Concrete kernel failure and axiom gate

These commands were run on Lean 4.29.1:

```text
lake env lean -s 65520 compute/campaign686/agent_k22_packed_kernel/ActualShardProbe.lean
lake env lean -s 262144 compute/campaign686/agent_k22_packed_kernel/ActualShardProbe.lean
```

Both abort with `Stack overflow detected. Aborting.` The failure is inside the
concrete `decide +kernel` theorem: the same file truncated before that theorem
elaborates, and a mechanically scaled 1,000,000-bit / exponent-14 instance
does compile.

The generic bridge has exactly the allowed axioms:

```text
periodicPowMask_getLsbD_true:
  [propext, Quot.sound]
intersectPeriodicItems_getLsbD_true:
  [propext, Quot.sound]
no_index_of_intersection_zero:
  [propext, Classical.choice, Quot.sound]
```

The scaled one-million-bit concrete instance likewise reports only
`[propext, Quot.sound]` for the zero equality and the standard three allowed
axioms for its exclusion theorem. No `native_decide` occurs. However, axioms
for the actual 20-million-bit theorem cannot be claimed because that theorem
does not finish elaboration.

## Exact p=23 decomposition

The independent verifier evaluates

```text
S(W)=product_(j=1)^11 (W^2-(2j-1)^2)
T(W)=256W^11-226688W^9+67609696W^7-8111362160W^5
     +352497378310W^3-6055670906453W
```

at all pairs modulo 23 satisfying `S(w)=4*S(v)`. Multiplying
`T(w)-2*T(v)` by `(-33)^(-1)` yields exactly `{2,6,17,21}`. The Lean file
decodes the corresponding numeral mask, then uses parity in each of those four
cases to construct `q=t/46` and the representatives `25,29,17,21`,
respectively.

Its main theorem is

```text
parity_p23Mask_branch_decomposition
  (t : Nat) (hodd : t % 2 = 1)
  (hmask : auditedP23Mask.testBit (t % 23) = true) :
  exists q a, a in {17,21,25,29} and t = 46*q+a.
```

The companion theorem `parity_p23Mask_branch_iff` proves the converse as well,
so this is an exact decomposition rather than only a cover. Both theorems'
axiom reports are exactly
`[propext, Classical.choice, Quot.sound]`.

## Exact remaining gap

To promote `ActualShardProbe.lean` from an exact-arithmetic reproduction to a
kernel certificate, replace or split the single 20,000,000-bit equality by a
proof that compiles under the repository's ordinary Lean invocation and then
re-run the axiom gate. Even after that repair, this file excludes only
`0 <= i < 20,000,000` in the branch `t=46*i+17`; it is one shard, not the
complete 82,503,186-index branch or the other three branches.

## Reproduction

```text
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_k22_packed_kernel_review/test_review_verify.py
lake env lean \
  compute/campaign686/agent_k22_packed_kernel_review/P23ParityDecomposition.lean
```
