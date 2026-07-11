# Erdős 730 first-power routes: independent hostile audit

Verdict: **PASS as an accurate partial-proof artifact.  The full #730 gate
remains OPEN.**

This audit freezes and independently checks the producer result.  It does
not promote the finite `8/3` or `p<=1000` observations to theorems, and it
does not claim the still-missing family coverage bridge or residual budget.

## 1. Frozen producer boundary

The independent verifier refuses to run its full report if any producer hash
differs.

```text
ba313bb107c06cec137efced15da5a3c334c77082e981ac351b2d8db659d1825
  ErdosProblems/Erdos730FirstPowerRoutes.lean
a63bb168682ba6aca047f35dd073c3c4d713cd20ee80367637865886cac43dc0
  compute730/campaign_uniform/repair/far/first_power_routes.py
bf2798b0cf28d53587df528aaa1a720f48d517e20c8eebac9c1b2b5b19b07495
  compute730/campaign_uniform/repair/far/test_first_power_routes.py
d273db26c9fc15f6783e778e12df25d70cb4500f33b3042ab471c411e0abccc1
  compute730/campaign_uniform/repair/far/first_power_routes_findings.md
9865c076593f273afbecc85828d1805f598784ab48a7ef67601d24432ac6e4a3
  docs/plans/2026-07-10-erdos730-first-power-short-top.md
```

Frozen auditor-side artifacts, excluding this self-referential report:

```text
b0fef6cc9da98448f1d1aab15a0e4a4c3fd3afd4452ed60559ef0b306c065447
  ErdosProblems/Erdos730FirstPowerRoutesAudit.lean
f31f242f4ffba598e7a520b83a4bf2c8f59412db389ace427ae6a0131484248b
  compute730/campaign_uniform/repair/far/first_power_routes_hostile_verify.py
699aed201b83c26019214d8831ebd96100164f69c3cb23d160d1e75eff1e2889
  compute730/campaign_uniform/repair/far/test_first_power_routes_hostile_verify.py
5f63a9b34f6586cb99d5ae68ca957bee3c9bc58c0d0c523a2a98fcf212022bf3
  docs/plans/2026-07-10-erdos730-first-power-routes-hostile-audit.md
```

The hostile Python verifier imports neither the producer verifier nor its
tests.  It independently defines the four branch maps, p-adic roots,
rational logarithm bounds, restricted-digit masks, and periodic windows.

## 2. Dependency tree and per-node verdicts

```text
H0  producer hash boundary                                           PASS
|
+- H1 fixed upper-slope identity                                     LEAN-PROVED
|
+- H2 higher-power endpoint
|  +- N>=10P+6 -> cleared factor 6/5                                 LEAN-PROVED
|  +- prime series plus tail <29/500                                 EXACT
|  `- four-branch payment <174/625                                   PAPER/EXACT
|
+- H3 aligned a=1 discrepancy
|  +- uniform 2*mean                                                 FALSE
|  `- 8/3 on 18 retained cases                                       EXACT-CHECKED ONLY
|
+- H4 r=1 shortest blocks
|  +- fixed-slope correlation on complete p-blocks                   LEAN/PAPER-EXACT
|  +- arbitrary-start endpoint term +2(H-1)                          REQUIRED
|  +- uninflated main                                                FALSE
|  `- inflated Q/S target through p<=1000                            EXACT-CHECKED ONLY
|
+- H5 Q/S top boundary
|  +- low-digit inequalities                                         LEAN-PROVED
|  +- c^2<p thresholds 66 and 1856                                  LEAN-PROVED
|  +- finite top exceptions                                          OPEN
|  `- all non-top/no-maximal-r short classes                         RETAINED/OPEN
|
`- H6 family closure
   +- common (branch,p,a)-event coverage bridge (23)                 OPEN
   `- FirstPowerFar/X + ShortTop/X <=1779/2500-delta                 OPEN
```

## 3. Higher-power endpoint and budget

The rational atanh series independently proves `log(5)>8/5`.  Hence for
`r>=a>=2`, `P=p^r>=25` and the critical length satisfies

```text
N > (256/25)P >= 10P+6.
```

The last inequality is exact because

```text
256P-25(10P+6)=6P-150 >=0  for P>=25.
```

The Lean audit independently clears denominators:

```text
CP<=M(N+2P), q(N-1)<=X, N>=10P+6
  -> 5CqP<=6MX.
```

The hostile verifier then recomputes, over all 166 primes from 5 through
997,

```text
sum_p (p+1)/(p(p-1)(2p+1)) <57/1000.
```

For `p>1000`, dropping primality and telescoping costs `1/1000`, so one
branch costs less than `29/500`.  Four branches and the endpoint factor give

```text
4*(6/5)*(prime sum + 1/1000) <174/625.
```

After the separately audited strict-band ceiling `1/100`, the exact
remaining arithmetic is

```text
1-1/100-174/625 =1779/2500.
```

The generic `6/5` implication and terminal rational identities are kernel
theorems.  The infinite prime/root aggregation into `174/625` remains a
paper-and-exact-arithmetic result; this audit does not mislabel it as a
kernel-expanded family theorem.

## 4. Aligned first-power falsification

An independent exact scan of 18 Q/S cases reproduces ten violations of the
tempting `2*mean` bound.  The first retained violation is

```text
Q, p=5, r=2: max=5, mean=54/25, ratio=125/54>2.
```

The worst retained violation is

```text
Q, p=7, r=3: max=23, mean=3072/343,
ratio=7889/3072>2.
```

All 18 ratios are at most `8/3`, and Lean checks
`7889/3072<8/3`.  This is a finite falsification boundary only.  No uniform
`8/3` discrepancy theorem is claimed.

## 5. Shortest blocks and logarithmic allowance

The signed 588-fixture grid and the independent Lean theorem reproduce

```text
G(u+pz)-G(u)-pzB = A p^2(2uz+pz^2).
```

Thus complete aligned `p`-blocks reduce to the stated finite-field
correlation.  An arbitrary interval still has two partial endpoints; the
residual must pay the exact cover term `2(H-1)`.

The independent Q/S scan covers 328 admissible cases through prime 1000.
It reproduces 291 failures of the uninflated main, with worst ratio

```text
S, p=19, N=165, start=109, hits=56,
ratio=5054/4125>1.
```

No scanned case violates the logarithmically inflated target.  The closest
is

```text
S, p=751, N=32927, start=42280, hits=9095,
certified target ratio <1.
```

The scan uses a rational upper bound `log_upper(p)`.  Therefore

```text
1+1/log_upper(p) <1+1/log(p),
```

and passing this smaller target is a rigorous finite check.  It is not a
uniform theorem in `p`.

## 6. Q/S top thresholds and retained short classes

The independent Lean audit reproves the Q/S digit inequalities and

```text
c^2<p, p>=66    ->41c<5p;
c^2<p, p>=1856  ->43c+6<p.
```

The Python split proof checks the small ranges `c<=8` and `c<=43`; for the
large ranges the controlling polynomials start positive:

```text
5*9^2-41*9=36,
44^2-43*44-6=38,
```

and have positive forward differences.  The predecessor witnesses
`(p,c)=(65,8)` and `(1855,43)` show both natural-number envelopes are sharp
without primality.

These top lemmas cannot delete arbitrary short Q/S classes.  Trial division
independently certifies that `p=30000001` is prime.  At `X=2^57`, both Q and
S root classes have length

```text
4803839443 <8892451300 = ceil(p(log p)^2),
```

so no admissible `r=1` critical block exists.  Nevertheless:

```text
Q: x=304699465, c=3867733,
   L(x)=p*c, p does not divide c,
   Phi digits [714754,12202043,290876];

S: x=101483822, c=1288195,
   L(x)=p*c, p does not divide c,
   Phi digits [12883968,343247,32267].
```

Every displayed digit is below `H=15000001`, the exact-valuation forbidden
least digit is avoided, and both cofactors satisfy `c^2>p`.  Lean checks the
primality, linear identities, Phi numerators, digit decompositions, and
literal class-length arithmetic.  All no-maximal-`r` short classes across
all branches, primes, and exponents therefore remain in `ShortTop` unless
separately bounded.

## 7. Exact remaining gap

All terms below count obstruction events with common `(branch,p,a)`
multiplicity.  Campaign closure still requires the exhaustive bridge

```text
BadFamilyCount(X) <= ObstructionEventCount(X)
 <= StrictBand(X)+HigherPowerFar(X)
    +FirstPowerFar(X)+ShortTop(X).                    (23)
```

After that bridge, one must prove an explicit `delta>0` such that, uniformly
for every `X>=2^57`,

```text
FirstPowerFar(X)/X + ShortTop(X)/X
 <=1779/2500-delta.                                  (24)
```

`FirstPowerFar` must pay arbitrary starts and the `2(H-1)` `r=1` endpoints.
`ShortTop` must include every no-maximal-`r` short class, P/R top classes,
finite Q/S top exceptions, and any event not already placed by a proved
partition.  Inequality (24) alone is insufficient without (23).  Neither is
proved by this artifact.

## 8. Kernel and execution audit

`Erdos730FirstPowerRoutesAudit.lean` independently proves fourteen audit
theorems.  Every `#print axioms` result is contained in

```text
[propext, Classical.choice, Quot.sound].
```

There is no `native_decide`, `sorry`, `admit`, custom axiom, or unsafe proof.

Frozen reproduction commands:

```bash
lake env lean ErdosProblems/Erdos730FirstPowerRoutesAudit.lean

python3 -m pytest \
  compute730/campaign_uniform/repair/far/test_first_power_routes_hostile_verify.py -q

python3 compute730/campaign_uniform/repair/far/first_power_routes_hostile_verify.py \
  --pretty

# Original related producer scope: 43 tests.
python3 -m pytest \
  compute730/campaign_uniform/repair/far/test_first_power_routes.py \
  compute730/campaign_uniform/repair/far/test_unit_range_block.py \
  compute730/campaign_uniform/repair/far/test_unit_range_block_hostile_verify.py \
  compute730/campaign_uniform/repair/far/test_far_fourier.py \
  compute730/campaign_uniform/repair/far/test_stronger_affine_counterexample.py -q
```

Frozen results:

```text
independent hostile suite: 8 passed
original related producer scope: 43 passed
Lean audit: PASS, allowed axioms only
producer hashes: 5/5 match
```
