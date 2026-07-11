# Erdős 686 all-owner assembly

Status: **complete compositional bridge, kernel-checked; no closure claim.**

Every cleaned prime-power owner is assembled on the literal full grid
`Icc 1 k`.  The original `globalResidualGroupedLoss k d` is preserved; no
unselected component is absorbed into it.  The resulting exact residual
quotients instantiate the generic multi-owner second and third obstructions
at every grid index, and the target-size zero-obstruction branch is excluded.
The remaining nonzero obstruction branch is open.

## Frozen producer artifacts

```text
ErdosProblems/Erdos686AllOwnerAssembly.lean
  a63011061fc8af531036374a238ae776ef861f3d21df937def40f156b50c88bf
compute/campaign686/all_owner_assembly_verify.py
  29ea556f2cca67366243c283f8fbce85f18358eb157e22d221cf6d8d45b1860b
compute/campaign686/test_all_owner_assembly_verify.py
  57170689925795ca7315f2127135aa736aa1ee619811745f09b10026327386f8
docs/plans/2026-07-10-erdos686-all-owner-assembly.md
  b87e233a080aeaf55295f2f980f80831d03734e2bf33a6f76a5c55befd5ea3a3
```

The producer has exactly two direct imports:

```text
ErdosProblems.Erdos686MultiOwnerExtension
ErdosProblems.Erdos686TwoOwnerGrouping
```

No shared import registry, root audit file, frontier, progress file, manifest,
campaign registry, or attestation file was changed by this checkpoint.

## Exact assembly

For a supplied `GlobalResidualOwnerAssignment k n d owner`, define

```text
S   = Icc 1 k,
g   = globalResidualGroupedLoss k d,
P_i = globalResidualGroupedLeft k d owner i,
a_i = localResidual n d i / P_i^2.
```

For every `p in d.primeFactors`, put

```text
t_p = globalResidualCleanExponent p (d.factorization p) k.
```

The assignment gives `owner p in S`.  The finite product over the full grid
therefore has exactly one nonunit candidate:

```text
product_{i in S} (if owner p=i then p^t_p else 1) = p^t_p.   (1)
```

This includes `t_p=0`: every factor in (1) is then literally one.  Commuting
the prime and owner products and using
`p^(v_p(d)-t_p) p^t_p = p^v_p(d)` gives the exact kernel theorem

```text
d = g * product_{i in S} P_i.                              (2)
```

The upstream pairwise-coprime loss proof remains unchanged, so for the six
target rows

```text
0 < g <= targetAggregateLoss k.                            (3)
```

There is no owner-range restriction in (1) through (3) beyond the certified
membership `owner p in Icc 1 k`.

## Exact residual and local-lift interface

The assignment supplies `P_i | n+i` and `P_i^2 | localResidual n d i` for
every natural index.  Exact natural division gives

```text
X_i = localResidual n d i = a_i P_i^2.                     (4)
```

Under `5<=k<=d` and the multiplier-four equation, the already verified bound
`2d<n` implies `X_i>5d>0`.  Hence `a_i>0`, natural subtraction casts without
truncation, and for every `i,j in S`

```text
a_i P_i^2 - a_j P_j^2 = 3(i-j)                            (5)
```

in signed integers.  Erasing `i` from (2) gives the exact local quotient

```text
d = P_i * (g * product_{j in S, j!=i} P_j).                (6)
```

Equations (4) and (6), `P_i | n+i`, and the block equation instantiate the
existing local Taylor theorems without any extra lemma:

```text
P_i | 3 C_i a_i - 4 D_i (g product_{j!=i} P_j)^2,          (7)

P_i^2 | -3[3 C_i a_i - 4 D_i (g product_{j!=i} P_j)^2]
          + 20 E_i P_i (g product_{j!=i} P_j)^3.           (8)
```

## Integer-grid transport and composed obstructions

The map `Nat -> Int` is injective on `S`.  The module proves exact cardinal,
full-product, and erase-product transport, rather than relying on an informal
identification:

```text
card(image Int.ofNat S) = k,
product_{z in image S} P_z = product_{i in S} P_i,
product_{z in image S, z!=i} P_z = product_{j in S, j!=i} P_j.   (9)
```

Thus the generic finite-family algebra applies on the full integer grid.  If

```text
A       = product_{j in S} a_j,
Delta_i = product_{j in S, j!=i} (i-j),
r       = k-1,

O_i = 3 C_i A - 4 D_i g^2 (-3)^r Delta_i,
F_i = -3 O_i + 20 E_i g^2 d (-3)^r Delta_i,
```

then Lean proves for every `i in S`

```text
P_i | O_i,                                                 (10)
P_i^2 | F_i.                                               (11)
```

At `d>=10^120`, all `k` target rows have `5<=k<=15`, every integer owner lies
in `[1,15]`, every residual exceeds `5d`, `C_i!=0`, and `|D_i|<10^12`.
The audited generic zero exclusion therefore gives

```text
O_i != 0                                                   (12)
```

for every grid index.  Empty buckets are included: when `P_i=1`, (10) and
(11) are tautological divisibilities, while (4), (5), and (12) remain exact.
No theorem calls an empty bucket a nontrivial cleaned owner.

`AllOwnerAssemblyCertificate` packages the assignment, (2) through (5),
(10), (11), and (12).  The theorem
`exists_allOwnerAssemblyCertificate` constructs this package from only the
target-row disjunction, `d>=10^120`, and the exact multiplier-four equation.

## Dependency tree and per-node verdict

```text
exists_allOwnerAssemblyCertificate                                  PASS
|- exists_globalResidualOwnerAssignment                             PASS (existing)
|- one-prime full-grid placement (1)                                PASS
|  `- exact owner membership from the assignment
|- prime/owner product commutation and gap reconstruction (2)       PASS
|  |- globalResidualGroupedLossFactor_mul_clean
|  `- Nat.prod_factorization_pow_eq_self
|- unchanged loss positivity and target ceiling (3)                 PASS
|- square quotient reconstruction (4)                               PASS
|- positivity, signed cast, and pairwise progression (5)            PASS
|  `- twice_gap_lt_n_of_four_solution
|- per-owner gap quotient (6)                                       PASS
|- second and third local lifts (7), (8)                             PASS
|- injective Nat-to-Int full/erase product bridge (9)                PASS
|- generic multi-owner compositions (10), (11)                      PASS
|- target-size zero exclusion (12)                                  PASS
`- eliminate the nonzero obstruction branch                         OPEN
```

There is no private lemma or unquantified uniformity in the public
certificate.  Every phrase above involving all owners is represented by an
explicit finite-set universal quantifier in Lean.

## Boundary audit

- **`d=1`: PASS for the arithmetic layer.** `primeFactors 1` is empty,
  `g=1`, and every bucket is one, so (2) is `1=1`.  The target certificate is
  intentionally guarded by `10^120<=d`.
- **Zero clean exponent: PASS.** The retained factor is `p^0=1`; assigning it
  to one grid index neither duplicates nor removes mass.
- **Empty owner bucket: PASS.** A finite product of unit factors is exactly
  one.  Its cofactor is the whole positive residual.
- **All primes at one owner: PASS.** That bucket receives all retained mass;
  every other bucket remains one.
- **Bases 2 and 3: PASS.** Assembly uses the upstream exact clean exponent.
  In particular it does not replace the special base-3 loss rule with the
  ordinary factorial rule.
- **Primes at least `k`: PASS.** Their zero loss exponent leaves the full
  prime power in exactly one bucket.
- **Endpoints `1` and `k`: PASS.** Membership and erase transport do not use
  an interior-owner hypothesis.
- **Center owners: PASS.** No local coefficient is cancelled; the structural
  proof `C_i!=0` uses the signed factorial formula at every grid index.
- **Natural subtraction: PASS.** Casting (4) into (5) is performed only after
  proving the local residual positive, so no truncated subtraction is hidden.
- **Four-or-more finite-family theorem: PASS.** The full grid has cardinality
  `k>=5`; unit buckets do not change (2) and are permitted by the generic
  algebra.

## Exact arithmetic reproduction

The standalone verifier independently factors every `1<=d<=500` in all six
rows and applies five deterministic owner strategies to every factorization.
It checks:

```text
15,000 gap/assignment fixtures,
15,430 zero-clean component occurrences,
136,028 empty bucket occurrences,
7,500 fixtures containing base 2,
4,980 fixtures containing base 3,
11,950 fixtures containing a prime at least k,
9,829 fixtures using owner 1,
5,728 fixtures using owner k,
5,988 nonempty fixtures putting all primes at one owner,
6 d=1 rows.
```

Every factorization satisfies (1) and (2), and every bucket with no nonunit
clean component is exactly one.

Six independent CRT square-progressions, one on each complete target grid,
check 60 owner congruences.  Every fixture reproduces exact quotient recovery,
all pairwise step-three differences, and both generic compositions (10) and
(11).  These are algebra fixtures, not asserted block-equation solutions.

## Kernel and test gates

- Direct `lake env lean ErdosProblems/Erdos686AllOwnerAssembly.lean` passes.
- All 30 public theorem surfaces are frozen by the verifier.
- Every printed axiom surface is contained in
  `[propext, Classical.choice, Quot.sound]`.
- The source gate finds no executable `sorry`, `admit`, `axiom`, or
  `native_decide`.
- The focused verifier has 6 passing tests and both Python files compile.

## Exact remaining gap

This checkpoint deliberately stops before the following single quantified
lemma:

```text
allOwnerCertificate_below_cutoff:
  forall k n d,
    (k=5 or k=7 or k=9 or k=11 or k=13 or k=15) ->
    blockProduct k (n+d) = 4 * blockProduct k n ->
    AllOwnerAssemblyCertificate k n d ->
    d < 10^120.
```

No proof of this lemma is supplied.  With
`exists_allOwnerAssemblyCertificate`, it is target-strength for the remaining
large-gap case and therefore is not counted as a reduction or partial
resolution.  The already falsified direct size route remains dead: the exact
upper bound for a nonzero `O_i` grows like `g^2 d^(k-2)`, so `P_i|O_i` does
not by itself yield a closing product bound.  Any genuine next step must use
new joint information from the nonzero `O_i`, the square divisibilities
`P_i^2|F_i`, and the short residual window; merely renaming that interaction
as a lemma would be circular.
