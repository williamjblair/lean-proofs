# Erdős 686 fourth-local-lift attack

Status: **exact fourth congruence and cyclic three-owner composition proved;
proper local strengthening; no new congruence-only bound.**

The isolated Lean module is
`ErdosProblems/Erdos686FourthLocalLift.lean`.  The independent exact-integer
reproduction is `fourth_local_lift_verify.py`, with focused tests in
`test_fourth_local_lift_verify.py`.  These files are intentionally not wired
into shared imports, manifests, attestations, or campaign dashboards pending
hostile audit.

## 1. Exact local congruence

Write the signed local cofactor through cubic order as

```text
Q_i(z) = C + D z + E z^2 + F z^3  (mod z^4).
```

Let

```text
L = H X,       d = H M,       3X-M = A H,
(L+HM) Q_i(L+HM) = 4 L Q_i(L).
```

The fourth-power cofactor remainder makes the last equation divisible by
`H^5`.  After cancelling the common `H^2`, put

```text
T4 = -CA + D[(X+M)^2-4X^2]
         + H E[(X+M)^3-4X^3]
         + H^2 F[(X+M)^4-4X^4].
```

Then `H^3 | T4`.  Substituting `M=3X-AH` and clearing the denominator with
`27` gives the exact identity

```text
27 T4 = G4
  + H^3 [80 A F M^3
         + H(-3 A^3 E + 24 A^2 F M^2)
         - A^4 F H^3],
```

where

```text
T3 = -3(3 C A - 4 D M^2) + 20 E H M^3,

G4 = 3 T3
   + H^2(-9 D A^2 + 36 E A M^2 + 84 F M^4).          (F4)
```

Therefore

```text
H^3 | G4.                                               (8)
```

No division by `3` occurs, so (8) is valid even when `3|H`.  The three terms
inside the `H^2` correction are not optional.  In particular, the tempting
formula obtained by putting `A=0` is false for the actual cleaned residual
`A=a>0`.

Lean proves:

```text
localOffsetCofactor_fourth_order
fourth_order_local_algebra
fourth_order_local_lift
```

All three report axioms contained in
`[propext, Classical.choice, Quot.sound]`.

## 2. Cyclic square-residual composition

For one owner, write

```text
X_i = aP^2,  X_j = bQ^2,  X_l = cR^2,
d = gPQR,
delta_1 = i-j,  delta_2 = i-l,  t = abc.
```

The two exact residual differences give

```text
Z := (bQ^2)(cR^2)
   = a^2 P^4 - 3aP^2(delta_1+delta_2)
     + 9 delta_1 delta_2.                               (9)
```

Let the already banked composed third obstruction be

```text
F_i = -3 O_i + 180 E_i g^2 delta_1 delta_2 d,
O_i = 3[C_i t - 12D_i g^2 delta_1 delta_2].
```

At fourth order one must multiply by `(bc)^2`; multiplying only by `bc`
leaves the integral term `bc Q^4R^4` uneliminated.  Applying (9) at precisions
`P^3` and `P` gives

```text
P^3 | 3bc F_i + P^2 J_i,                                (10)
```

with

```text
J_i = -9D_i t^2
      -108D_i t g^2(delta_1+delta_2)
      +324E_i t g^2 delta_1 delta_2
      +6804F_i g^4(delta_1 delta_2)^2.                  (11)
```

Here the last `F_i` in (11) denotes the cubic Taylor coefficient, not the
composed third obstruction; the Lean source uses `F` and the explicit
definition to avoid this notational collision.  Relabeling the three owners
gives (10) cyclically at `P,Q,R`.  Lean proves the generic signed-integer
theorem

```text
three_bucket_fourth_obstruction_dvd_cube.
```

The Python verifier reconstructs the Taylor coefficients independently and
checks **7,020** signed denominator-clearing fixtures and **30,528** signed
three-bucket compositions.

## 3. The lift is proper but is not a bounded resultant

The fourth congruence is not implied by the banked third congruence.  On the
existing target-size CRT pattern

```text
k=5,  (i,j,l)=(1,2,4),
P=101^20, Q=103^20, R=107^20, g=1,
```

the representative satisfying all third congruences has nonzero fourth
quotient residues

```text
439987804685666293694081422867534157888,
7797703725030760165134404338142874334319,
35218501497772032758465410169995205298447.
```

Nevertheless it lifts by one more owner-adic digit.  If the square-residual
CRT parameter is `s`, the third congruence determines `s mod P_i^2` with unit
derivative

```text
-9 C_i (d/P_i)^2.
```

After combining those residues, write `s=s_0+d^2u`.  Divide (F4) by `P_i^2`.
Its derivative with respect to `u`, modulo `P_i`, is exactly

```text
-27 C_i (d/P_i)^4.                                    (12)
```

For the three bases above and the local constants `24,-6,-6`, (12) is a unit
for every exponent `e>=1`.  CRT therefore chooses `u mod PQR` so all three
fourth congruences hold.  Adding a multiple of `d^3` to `s` preserves them and
selects the residue needed to reconstruct integral `n`.

The exact verifier checks exponents

```text
e = 1,2,3,5,8,10,12,16,20,24,
```

with gap digit lengths from `7` through `146`.  Every checked member satisfies
the square residuals, all second/third/fourth local congruences, all three
composed congruences (10), and directly

```text
P_i^5 | B(5,n+d)-4B(5,n)
```

at each selected owner.  The `e=20` member has the exact 121-digit gap

```text
8528006514942991411329818759017663024603296760011487105481658555774743359211568625230878556970868752918452276874633718401.
```

It is **not** an Erdős 686 solution: direct integer evaluation says the block
equation is false.  Its reconstructed `n` has 604 digits, and its residuals
fail `X_s<14d`.  Thus it is also outside the verified short window.

This gives the exact route verdict:

- (8) and (10) are proper new necessary conditions;
- they do not produce a fixed nonzero resultant or any congruence-only upper
  bound for `d`;
- the fourth lift has not falsified or proved the short-CRT lemma, because the
  one input that kills the CRT family is still the archimedean short window.

## 4. Exact remaining gap

The strongest proper next statement is the existing three-bucket short-CRT
lemma with the three additional cyclic conditions (10):

> For a target row, exclude `d>=10^120`, `1<=g<=G_k`, pairwise-coprime
> `P,Q,R>1`, distinct owners, and positive `a,b,c` when the three square
> residuals lie in the verified short window and satisfy the second, third,
> and fourth local divisibilities.

Removing the short window from that statement is false by the exact family
above.  Returning (8) or (10) as a closure would therefore be the same
congruence-only error already identified at third order.

## 5. Boundary audit

- **Nonzero residual cofactor.** Signed fixtures include `A!=0`; the exact
  identity retains every `A` correction.
- **Base 3.** The Lean theorem does not cancel `3`.  The CRT falsifier uses
  components coprime to `3` only to make the explicit Hensel derivatives
  invertible.
- **Signs and zero coefficients.** The generic algebra is over `ℤ`; signed
  fixtures include negative components, cofactors, and losses.  Target
  positivity is not smuggled into an algebraic cancellation.
- **Centers and reflections.** The theorem is index-generic.  No center or
  reflected triple is excluded; the route verdict does not depend on the
  finite slope table.
- **Unit cleaned components.** The identity remains valid at `P=±1`; the
  quantified short-CRT gap still separately requires `P,Q,R>1`.
- **Telescopes and row-prefix witnesses.** No claim is made about the `d=1`
  telescopes or the large-`k` row-prefix examples; both lie outside this
  exactly-three-owner target-size slice.
- **No native evaluation.** The Lean source contains no `native_decide`,
  `sorry`, `admit`, new axiom, or unsafe declaration.

## 6. Reproduction

```bash
python3 -m pytest compute/campaign686/test_fourth_local_lift_verify.py -q
python3 compute/campaign686/fourth_local_lift_verify.py --pretty
lake env lean ErdosProblems/Erdos686FourthLocalLift.lean
lake build ErdosProblems.Erdos686FourthLocalLift
```
