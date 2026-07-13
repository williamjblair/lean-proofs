# Erdős 686: high prime-power component packet

## Verdict

**MATHEMATICAL AUDIT PASS; LEAN-BANKED.**

The GPT-Pro high-component theorem is a genuine uniform no-solution theorem,
not a target-equivalent reduction.  It handles every prime base, including
`2` and `3`, under an explicit dominance inequality on one full prime-power
component of the gap.  The particularly clean family

```text
d = p^(k+t),  k >= 16,  p prime,  t >= 0
```

is therefore closed for every natural `n` (and in fact for odd as well as even
`k`).  This packet independently checks every constant, exhausts the finite
exceptional modular branches, and samples the general residue identities.

The complete trichotomy is now formalized in
`ErdosProblems/Erdos686HighPrimePowerComponent.lean`.  The public dispatcher

```lean
no_four_solution_of_highPrimePower_component
```

and the three branch theorems

```lean
no_four_solution_of_highTwoPower_component
no_four_solution_of_highThreePower_component
no_four_solution_of_highPrimePower_ge_five_component
```

compile with exactly `[propext, Classical.choice, Quot.sound]`.  The module
also exports the three exact residual-lift witnesses used by the size
contradiction:

```lean
highTwoPower_exists_residual_lift
highThreePower_exists_residual_lift
highPrimePower_ge_five_exists_residual_lift
```

The simpler square conditions and the clean infinite family are kernel
theorems too.  In particular:

```lean
theorem no_four_solution_primePowerGap
    {p k t n : ℕ} (hp : p.Prime) (hk : 16 ≤ k) :
    blockProduct k (n + p ^ (k + t)) ≠ 4 * blockProduct k n
```

The separate Nair-Shorey short-gap strip is **EXTERNAL/PAPER-ONLY**.  This
packet checks only the rational arithmetic surrounding the quoted result; it
does not verify the published greatest-prime-factor theorem and does not count
the strip as banked progress.

## Exact theorem surface audited

Write

```text
P_k(x) = product_(i=1)^k (x+i)
R_k(d) = (13k-6)d + 18(k-1).
```

For a prime `p`, let `lambda_p(k)` be the unique integer satisfying

```text
p^lambda_p(k) <= k-1 < p^(lambda_p(k)+1),
```

and for `p=3` let

```text
mu_3(k,e) = min(lambda_3(k), e-2).
```

Let `k>=16`, `d>=k`, `p^e || d`, `q=p^e>=k`, and `m=d/q`, so `p` does not
divide `m`.  Then `P_k(n+d) != 4 P_k(n)` under any one of

```text
p=2:   R_k(d) <= 24 * 2^(2e-lambda_2(k));
p=3:   R_k(d) <=  6 * 3^(2e-mu_3(k,e)-1);
p>=5:  R_k(d) <=  6 * p^(2e-lambda_p(k)).
```

The non-strict `<=` on the hypothesis is intentional: every surviving owner
would yield a strictly positive multiple that is strictly smaller than the
same modulus.

## Dependency tree

```text
high prime-power component theorem                         [LEAN BANKED]
|
+- equation P_k(n+d)=4P_k(n)
|  +- product ratio identity
|  +- 3n>d                                                [EXACT]
|  `- 18(n+1)<13kd                                        [EXACT]
|     `- 412769/103259 = 4-267/103259                    [EXACT]
|
+- q=p^e>=k gives at most one q-multiple in lower block   [EXACT]
|
+- p>=5 maximum-valuation trichotomy                      [MODULAR PASS]
|  +- s<e: p-free products fixed mod p, but U'=4U
|  +- s>e: unique q-owner loses valuation
|  `- s=e: unique owner and p^(e-lambda) | (3a-m)
|
+- p=2 maximum-valuation trichotomy                       [MODULAR PASS]
|  +- s<e: total valuation cannot gain v_2(4)=2
|  +- s>e: unique q-owner loses valuation
|  `- s=e: v_2(a+m)=2 and 2^(e-lambda+2) | (3a-m)
|
+- p=3 four-way split                                     [MODULAR PASS]
|  +- s<=e-2: p-free products fixed mod 9, but U'=4U
|  +- s>e: unique q-owner loses valuation
|  +- s=e: reduced equation forces 3|m
|  `- s=e-1
|     +- at most two h=3^(e-1) owners
|     +- two owners impossible modulo 9
|     `- singleton gives 3^(e-mu-1) | (a-m)
|
+- exact positive upper bounds on 3a-m or a-m             [EXACT]
`- strict-small-positive-multiple contradiction           [EXACT]

simple component conditions                               [LEAN BANKED]
`- R_k(d)<15kd and p^lambda,3^mu<k                        [EXACT]

d=p^(k+t) family                                           [LEAN BANKED]
`- three elementary exponential inductions                [EXACT]

Nair-Shorey linear strip                                   [PAPER-ONLY]
+- sharp ratio arithmetic                                  [EXACT]
`- quoted greatest-prime-factor theorem                    [EXTERNAL]

Lean formalization                                         [PASS]
|-- p=2 residual lift and exclusion                        [LEAN BANKED]
|-- p=3 half-owner classification, lift, and exclusion     [LEAN BANKED]
|-- p>=5 residual lift and exclusion                       [LEAN BANKED]
|-- all-prime dispatcher                                   [LEAN BANKED]
`-- square criteria and d=p^(k+t) corollary                [LEAN BANKED]
```

## Exact archimedean constants

From an assumed equation,

```text
4 = product_(i=1)^k (1 + d/(n+i)).
```

If `3n<=d`, then every factor is at least `7/4`; already
`(7/4)^3=343/64>4`, so `3n>d`.

For the second bound, the binomial/exponential estimate is entirely rational:

```text
sum_(j=0)^3 (18/13)^j/j!                  = 8317/2197
((18/13)^4/4!) / (1-18/65)               = 21870/103259
total                                      = 412769/103259
4-total                                    = 267/103259 > 0.
```

Thus `(1+18/(13k))^k<4`.  If `18(n+1)>=13kd`, every factor in the product
ratio is at most `1+18/(13k)`, a contradiction.  Therefore

```text
18(n+1) < 13kd,
18(n+i) < 13kd + 18(k-1)  for 1<=i<=k.
```

The exact verifier reconstructs these four fractions from `Fraction` objects,
not from decimal approximations.

## Exhaustive modular classification

Let `s=max_i v_p(n+i)`.  Translation by `d=p^e m` preserves both valuation
and normalized unit for every term with valuation `<e`; a term with valuation
`>e` drops to exactly `e` because `p` does not divide `m`.

### `p>=5`

The cases `s<e`, `s=e`, and `s>e` are exhaustive.

- `s<e`: after stripping powers of `p`, `U'=U (mod p)` and `U'=4U`.
  Hence `3U=0 (mod p)`, impossible for a unit when `p>=5`.
- `s>e`: there is only one `q`-multiple in the lower block; its valuation
  decreases and no other valuation changes.
- `s=e`: the unique owner is `n+i=qa`, with both `a` and `a+m` units.  Every
  nonowner has valuation at most `lambda_p(k)`, so cancellation modulo
  `p^(e-lambda_p(k))` gives

  ```text
  p^(e-lambda_p(k)) | (3a-m).
  ```

The verifier exhausts all units modulo `p` for every prime `5<=p<=47`, and
all owner residue pairs modulo `p^L` for `p in {5,7,11}` and `L in {1,2}`.
The tested congruence is equivalent residue by residue to `m=3a (mod p^L)`.

### `p=2`

Again the cases `s<e`, `s=e`, and `s>e` are exhaustive.  The first and third
cannot supply the required total valuation increase of two.  In the middle
case write `n+i=2^e a`.  Equality forces `v_2(a+m)=2`; with
`b=(a+m)/4`, the odd-part equation gives `b=a (mod 2^(e-lambda_2(k)))`.
Equivalently,

```text
2^(e-lambda_2(k)+2) | (3a-m).
```

The verifier exhausts every odd pair `(a,m)` modulo `2^(L+2)` for
`1<=L<=6`, retaining exactly the residue pairs with `v_2(a+m)=2`, and checks
this equivalence for every retained pair.

### `p=3`

Here `q>=k>=16` forces `e>=3`.  The cases

```text
s<=e-2,  s=e-1,  s=e,  s>e
```

are exhaustive.

- `s<=e-2`: the stripped product is fixed modulo `9`; `U'=4U` would make
  `9|3U`, impossible for a 3-adic unit.
- `s>e`: the unique `q`-owner loses valuation.
- `s=e`: the unique-owner equation modulo `3` forces `3|m`, contrary to
  `p^e || d`.
- `s=e-1`: put `h=3^(e-1)`.  There are one or two `h`-owners.  Three would
  include one multiple of `3h=q` within the interval, contradicting `s=e-1`.
  If there are two, their normalized units occupy the two nonzero residue
  classes modulo `3`; their inverse sum is zero, while the reduced equation
  requires it to equal `m^(-1)`.  Thus there is exactly one owner.

For the singleton, all nonowners have valuation at most
`mu=min(lambda_3(k),e-2)`.  Cancellation modulo `3^(e-mu)` yields

```text
3^(e-mu-1) | (a-m).
```

The verifier exhausts all six units modulo `9`, all singleton and admissible
two-owner tuples modulo `9`, and every singleton pair modulo `3^L` for
`2<=L<=5`.  Counts are:

```text
low branch unit residues:                6, all contradictory
q-owner admissible unit pairs mod 3:     2, all contradictory
half-q singleton tuples mod 9:          36, 18 congruence solutions
half-q two-owner tuples mod 9:         108,  0 congruence solutions
singleton lifts L=2,3,4,5: solutions 18,54,162,486.
```

These solution counts are expected: the singleton congruence is not itself a
contradiction.  Its nonzero divisible quantity is then eliminated by size.

## Size contradiction

For `p>=5` and `p=2`, the owner `n+i=qa` satisfies

```text
0 < 3a-m < R_k(d)/(6q).
```

For `p=3`, the singleton owner `n+i=3^(e-1)a` satisfies

```text
0 < a-m < R_k(d)/(6q).
```

The lower inequalities are exactly `3n>d` specialized at the owner.  The
upper inequalities follow from `18(n+i)<13kd+18(k-1)`; no `O(kd)` or
“essentially” estimate is used.  Combining them with the modular divisors
gives the three displayed HC thresholds verbatim.

## Cleaner conditions and infinite family

For `d>=k>=16`,

```text
15kd - R_k(d)
  = (2k+6)d - 18(k-1)
 >= 2(k-3)^2
 > 0.
```

Also `p^lambda_p(k)<k` and `3^mu_3(k,e)<k`.  Therefore each simple condition

```text
p=2:   8q^2 >=  5k^2d
p=3:   2q^2 >= 15k^2d
p>=5:  2q^2 >=  5k^2d
```

implies its exact HC condition.  Even the weakest implies
`q^2 >= (5/8)k^3 > k^2`, so the prerequisite `q>=k` is automatic.

For `d=q=p^e` these become the three conditions in display (27) of the source
output.  Taking `e=k+t` is uniform because

```text
2^k >= k^2             (k>=4),
3^k >= 8k^2            (k>=5),
5^k >= (5/2)k^2        (k>=2).
```

The verifier freezes each base case and the exact quadratic induction-step
margin.  A further sweep checks all `13,875` tuples with `16<=k<=200`,
`p<=47`, and `0<=t<=4`, including bases `2` and `3`.

## Reproduction

```sh
lake env lean ErdosProblems/Erdos686HighPrimePowerComponent.lean

PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_t2_high_component/high_component_verify.py

PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_t2_high_component/test_high_component_verify.py
```

Focused result: `7 passed in 0.20s`.

Every printed high-component theorem has axiom set exactly
`[propext, Classical.choice, Quot.sound]`; the formalization uses neither
`native_decide` nor a custom theorem axiom.

The broad simple-to-exact sweep checks `98,172` full components, of which
`35,087` satisfy a simple antecedent.  Every one satisfies the exact HC
inequality.  The ordinary strip arithmetic checks `113,074` integer pairs;
the exceptional `k=82` arithmetic checks `200` pairs.  These latter counts do
not verify the external prime-factor theorem.

Frozen SHA-256 values:

- GPT-Pro source attachment:
  `2262670ee74a62fb537493672abea66322eb6f79f0827d531814e2c96d220df6`;
- exact verifier:
  `9351e898bf968ce53cf0a0df58ac63bb777cd347787d4ee4ddb936ef99574b9a`;
- focused tests:
  `f5e94beb554484ed8776e02b2a694baf67a116be328d32dfc813028e554a8e8b`;
- canonical JSON audit payload:
  `dcd0557aaa23dd460dfcfb8f01ee7062619c3b0094df3ade5adbb2e495c6775a`.
