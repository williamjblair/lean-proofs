# Hostile audit: Erdős 686 MultiOwnerExtension

Audit date: 2026-07-10.

## Verdict

**PASS as a generic partial package.** The ten public Lean theorems are sound
at their stated interfaces, the full-family target zero exclusion is valid,
and the producer correctly leaves every nonzero multi-owner branch open.

One prose scope needs to remain explicit during integration: the family
`(2^N,3^N,5^N,7^N)` is a counterfamily only to a bounded-complement inference
from product averaging and component-square bounds. It is not an exact
step-three residual or full short-window fixture. The producer's surrounding
argument ultimately says this, but the phrase "product-and-window
counterfamily" can be overread.

No mathematical defect was found in the finite-family composition, target
zero exclusion, exact subset scan, or CRT route falsifier.

## Frozen producer verification

The hostile verifier checks these digests before doing any work:

```text
eb1672572473b14ab4ffb19a15573e577afa5e6fba093e6559fa781bc7ac051c
  ErdosProblems/Erdos686MultiOwnerExtension.lean
23c3b0c480278390cbb4d0286221f31862268e0dd9ca3c7771bf19179dadc2d1
  compute/campaign686/multi_owner_extension_verify.py
4da0d02ccf15838acb1a3cc25d7656974699c6ec2f50816f0e594d718b5fb97b
  compute/campaign686/test_multi_owner_extension_verify.py
72d9fd5cf24cfc9963844db73cbf73192c96a1e3906e911bc5e391e332c2be5a
  compute/campaign686/multi_owner_extension_findings.md
d20c7ffe82b6601bc0d8340297d661ed694a887fe3750d6d23a1cc3d28e42b53
  docs/plans/2026-07-10-erdos686-multi-owner-extension.md
```

The producer files were not modified.

## Dependency tree and node verdicts

```text
N0  Full Erdős 686 closure                                      OPEN / not claimed
 ├─ N1  Opposite residual-product congruence mod P_s^2            PASS / Lean
 ├─ N2  Arbitrary-family second obstruction P_s | O_s             PASS / Lean
 ├─ N3  Arbitrary-family third obstruction P_s^2 | F_s            PASS / Lean
 ├─ N4  Residual lower product g^2(5d)^t < A d^2                  PASS / Lean
 ├─ N5  Uniform C,D,Delta coefficient ceiling                     PASS
 ├─ N6  Full-family target exclusion O_s != 0 for 4<=t<=15        PASS / Lean
 ├─ N7  Every target subset/slope/collision finite scan           PASS / exact
 ├─ N8  Nonzero-obstruction direct size closure                   FAIL / rejected
 ├─ N9  Bounded complement from selecting three components        FAIL / rejected
 └─ N10 Congruences alone force short window or block equation     FAIL / CRT falsifier
```

## Independent composition audit

The hostile verifier imports no producer code. It reconstructs the Taylor
coefficients, CRT square progression, signed owner delta, local lifts, and
composed obstructions. For each owner it independently checks

```text
product_{u!=s}(a_u P_u^2)
  = (-3)^(t-1) Delta_s                         (mod P_s^2),

product_{u!=s}(a_u) * local_second_s
  = O_s                                        (mod P_s),

product_{u!=s}(a_u) * local_third_s
  = F_s                                        (mod P_s^2).
```

Nineteen owner congruences pass across four adversarial families containing:

- non-prefix and permuted owner sets;
- reflected endpoints and row centers;
- positive and negative cleaned components;
- negative loss and zero loss;
- components divisible by `2` and by `3`.

This extends beyond the producer's prefix-family fixture grid. Signs agree
with the Lean definitions:

```text
O_s = 3 C_s A - 4 D_s g^2 (-3)^(t-1) Delta_s,
F_s = -3 O_s + 20 E_s g^2 d (-3)^(t-1) Delta_s.
```

## Full target coefficient and slope scan

An independent enumeration of every subset of cardinality `4..k` in the six
target rows reproduces exactly:

```text
42,274 subsets,
309,329 owner slopes,
154,654 positive slopes,
327 subsets with a repeated positive slope,
maximum positive multiplicity 2,
maximum positive slope 1,807,743,205,183,749,120.
```

The minimum exact ratio between the equation-level target lower bound and a
positive zero slope is

```text
859375 * 10^238 / 3515199 > 1.
```

It occurs at `k=15`, owners `(1,2,3,15)`, distinguished owner `15`. No
floating-point comparison is used.

The hostile coefficient scan also supplies the exact actual maxima:

```text
max |C_s|     = 87,178,291,200,
max |D_s|     = 283,465,647,360,
max |Delta_s| = 87,178,291,200.
```

Hence every actual `C_s` is nonzero, `|D_s|<10^12`, and
`|Delta_s|<=15^14`. The six zero linear coefficients are exactly the row
centers `(5,3),(7,4),(9,5),(11,6),(13,7),(15,8)`.

The reflected collision at `k=5`, owners `(1,2,4,5)`, is reproduced exactly:
both endpoint zero slopes are `900`. This confirms that the earlier
three-owner uniqueness-of-zero pattern does not extend, while the target
lower bound excludes each zero separately.

## Hostile audit of the target zero inequality

The producer's uniform coefficient is exactly

```text
K = 4*10^12*3^14*15^14+1
  = 558515440794946289062500000000000001.
```

The weakest target boundary is `t=4,d=10^120`. Exact arithmetic gives

```text
K < 5^4 * (10^120)^2 = 625 * 10^240.
```

The Lean theorem `multi_owner_cofactor_product_scaled_lower` supplies
`g^2(5d)^t < A d^2`. The hostile importer independently proves

```text
K d^2 < (5d)^t  and  g^2(5d)^t < A d^2
  => K g^2 < A,
```

using only `g>0,d>0`. It also proves the final natAbs-level contradiction

```text
3|C|A = coeff*g^2,
|coeff| < K,
K g^2 < A,
C != 0
```

is impossible. Negative `C`, negative `D`, `D=0`, row centers, and reflected
delta signs are covered by natAbs or the independent exact scan.

The loss ceiling is genuinely unnecessary for this zero branch: the same
`g^2` occurs on both sides. This does not extend to a useful bound for a
nonzero obstruction.

## Independent CRT falsifier reconstruction

Without importing producer functions, the hostile verifier reconstructs

```text
k=5,
owners=(1,2,4,5),
components=(101^16,103^16,107^16,109^16),
g=1.
```

It obtains the same 130-digit gap

```text
2205474220935356988722497885428160025770701632629547097778915063286735417113828847388008212536791307861015482562878387550877008961
```

and a 517-digit `n` whose decimal SHA-256 is
`19a60511c39f9e68c01aab641e2db28489379b628ffdbcbe0859c4576e3ae07c`.

Direct integer evaluation confirms:

- every lower-factor, second-local, and third-local congruence;
- every composed second and third congruence;
- every composed second obstruction is nonzero;
- the lower window `X_s>5d` holds;
- the upper window `X_s<14d` fails;
- the block equation fails.

Thus the fixture is a valid falsifier for congruences-alone closure. It is not
a target counterexample and does not challenge the zero-exclusion theorem.

## Selection counterfamily scope

For `(P_1,P_2,P_3,P_4)=(2^N,3^N,5^N,7^N)` and `d=210^N`, the components are
pairwise coprime, each `P_i^2<=d`, and the complement to the largest three is
`2^N`. This disproves a bounded complement from those product and
component-square facts.

No `a_i` or step-three residual progression is supplied, so this family
should not be cited as a full short-window pseudo-witness. The producer's
actual conclusion only needs the narrower scope: product averaging and the
component-square consequence of the window cannot by themselves bound the
complement.

## Integration constraints

1. `target_multi_owner_second_obstruction_ne_zero` requires the complete
   selected decomposition `d=g*product(P_s)`. It cannot be applied to an
   arbitrary subset while absorbing unselected components into `g`.
2. The theorem takes `C!=0` and `|D|<10^12` as hypotheses. The hostile scan
   verifies them for every target coefficient, but the public theorem does
   not perform that row lookup itself.
3. The finite 42,274-subset scan is exact Python evidence, not a
   kernel-enumerated row certificate. The generic zero theorem is
   kernel-checked.
4. `O_s!=0` plus `P_s|O_s` does not bound the gap at useful degree for
   `t>=4`; no full target closure follows.

## Reproduction and kernel gate

```bash
python3 -m pytest -q compute/campaign686/test_multi_owner_extension_verify.py
python3 -m pytest -q compute/campaign686/test_multi_owner_extension_hostile_verify.py
python3 -m py_compile \
  compute/campaign686/multi_owner_extension_verify.py \
  compute/campaign686/multi_owner_extension_hostile_verify.py \
  compute/campaign686/test_multi_owner_extension_hostile_verify.py
python3 compute/campaign686/multi_owner_extension_hostile_verify.py
lake build ErdosProblems.Erdos686MultiOwnerExtension
lake env lean ErdosProblems/Erdos686MultiOwnerExtensionHostileAudit.lean
```

All ten public producer theorems and both independent hostile arithmetic
lemmas report only the allowed axiom subset
`[propext, Classical.choice, Quot.sound]`. No executable `sorry`, `admit`,
`axiom`, `native_decide`, `ofReduceBool`, or `unsafe` declaration is present.
