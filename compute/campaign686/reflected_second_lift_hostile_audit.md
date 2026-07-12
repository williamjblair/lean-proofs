# Hostile audit: reflected second and third lifts

Verdict: **PASS as exact equation-level second- and third-order necessary
conditions, including the cyclic three-owner compositions.  FAIL as a
Target 2 closure.**  A target-range, pairwise-coprime, `g=2^80`
congruence-only fixture Hensel-lifts through the new `P^2` conditions at all
three owners and still fails the block equation.

## Dependency tree

```text
exact equation B(k,n+d)=4 B(k,n)
|
+- reflected omitted factors A=h*x, B=h*(m-x)
|  `- exact cofactor reflection Q_{k+1-i}(z)=(-1)^(k-1) Q_i(-z)
+- Taylor cofactor Q_i(z)=C_i+D_i*z+E_i*z^2 (mod z^3)
+- reflected square residual
|  +- even: m+3x=h*a
|  `- odd:  5x-m=h*a
|
+- second reflected lift
|  +- even: h | C_i*a-12D_i*x^2
|  `- odd:  h | C_i*a+20D_i*x^2
|
+- third reflected lift
|  +- even: h^2 | C_i*a-12D_i*x^2+h(8D_i*a*x-60E_i*x^3)
|  `- odd:  h^2 | C_i*a+20D_i*x^2-h(8D_i*a*x+60E_i*x^3)
|
`- S=gPQR and three reflected owners
   +- exact residual differences: step 3 (even) or step 5 (odd)
   +- cleaned second composition modulo P,Q,R
   `- cleaned third composition modulo P^2,Q^2,R^2
```

No node assumes that a necessary congruence is sufficient, cancels `3` or
`5`, sets the small-prime loss `g` to one, or invokes the target theorem.

## Exact formulas and verdicts

| Node | Verdict | Exact consequence |
|---|---|---|
| Cofactor reflection | PASS | `Q_{k+1-i}(z)=(-1)^(k-1)Q_i(-z)`; kernel proof and 4,410 independent evaluations. |
| Second lift | PASS | Even `h | Ca-12Dx^2`; odd `h | Ca+20Dx^2`. |
| No-inverse cleaning | PASS | Even `P | 3Ca-4DG^2`; odd `P | 5Ca+4DG^2`, where `G=gQR`.  The verifier explicitly uses moduli divisible by `3` and `5`; the proof multiplies rather than divides. |
| Third lift | PASS | Even `P^2 | Ca-12Dx^2+P(8Dax-60Ex^3)`; odd `P^2 | Ca+20Dx^2-P(8Dax+60Ex^3)`. |
| Cleaned third lift | PASS | Even `P^2 | 27Ca-36DG^2+60EPG^3`; odd `P^2 | 125Ca+100DG^2-60EPG^3`. |
| Cyclic second composition | PASS | Even `P | 3(Cabc-12Dg^2 delta_1 delta_2)`; odd `P | 5(Cabc+20Dg^2 delta_1 delta_2)`, cyclically. |
| Cyclic third composition | PASS | Even `P^2 | 27(Cabc-12Dg^2 delta_1 delta_2+20Eg^3PQR delta_1 delta_2)`; odd `P^2 | 125(Cabc+20Dg^2 delta_1 delta_2-12Eg^3PQR delta_1 delta_2)`, cyclically. |
| Cofactor growth | PASS | If `S=gPQR`, `2n<S`, and each squared residual is at most `7n`, then `8abc<343g^2S`.  This is linear in `S`, not a cutoff. |
| Target 2 | **OPEN** | The exact block equation must still eliminate the balanced three-or-more-owner branch. |

All public Lean surfaces report exactly
`[propext, Classical.choice, Quot.sound]`.

## Independent exact arithmetic

The verifier reconstructs products and all three Taylor coefficients without
importing a producer module.  It checks:

- `4,410` cofactor-reflection evaluations (`1<=k<=20`, every owner,
  `-10<=z<=10`);
- `66,910` cubic-congruence rows, with `25,027` failed square premises kept
  out of scope and `39` exact-equation rows checked at third order;
- explicit even `3 | P` and odd `5 | P` fixtures, ruling out a hidden inverse;
- the complete target-range Hensel fixture below.

## Target-range Hensel falsifier

Take

```text
k = 16
(P,Q,R) = (17,19,23)
(i,j,l) = (1,7,16)
g = 2^80 = 1208925819614629174706176
n = 4254209959225268127279392844
d = 472689995466543884333395799
S = 2n+d+k+1 = gPQR
```

Then `k<=d`, `9d<n`, the components are pairwise coprime primes larger than
`k`, and `g` has only the small prime base `2`.  At all three owners:

1. the lower and reflected upper terms are divisible by the assigned
   component;
2. the reflected square residual is divisible by its square;
3. the raw and cleaned second lifts hold;
4. the raw and cleaned third lifts hold modulo the component square;
5. the step-three differences and both cyclic compositions hold.

The one-digit Hensel data are exact:

| component | owner | derivative mod component | lifted digit |
|---:|---:|---:|---:|
| 17 | 1 | 16 | 12 |
| 19 | 7 | 6 | 18 |
| 23 | 16 | 22 | 4 |

Every derivative is a unit.  Their CRT lift is `t=6421`; the target-ratio
translation is `s=1396681840576`.  Nevertheless

```text
B(16,n+d) != 4 B(16,n)
```

and the exact difference has `443` decimal digits.  Therefore neither the
second-order nor the third-order reflected local conditions, even with
pairwise coprimality, small-prime-supported `g`, exact target inequalities,
and cyclic composition, imply Target 2.  This is a hard falsifier of further
congruence-only closure claims.

## Boundary audit

- `h=1` is retained in the exhaustive grid.
- Both parities and both signs are tested.
- Endpoint owners `1` and `k`, the interior owner `7`, and reflection are in
  the Hensel fixture.
- Failed square premises are counted, not silently promoted.
- `g` is never replaced by `1`; the strongest fixture uses `g=2^80`.
- Pairwise coprimality does not enter the local algebra, and is preserved
  explicitly at the cleaned-bucket interface.
- The pseudo-fixture is labeled as failing the block equation and is used
  only to falsify sufficiency.

## Exact remaining gap

The remaining balanced-center node is the following quantified statement:

> For every `k,n,d` with `16<=k<=d` and
> `B(k,n+d)=4B(k,n)`, no factorization of the reflection center into an
> explicit small-prime loss times at least three pairwise-coprime cleaned
> large components can realize the equation-derived reflected owner data.

The local-order lane through quadratic cofactor coefficient `E` does not
prove this statement.  Because the derivatives above are units and the
fixture lifts one further digit at every owner, this audit stops the bounded
local-order experiment here rather than claiming another unquantified lift.

## Frozen source hashes

Hashes below cover the producer theorem surface and the independent verifier
snapshot; regenerate them after any edit.

```text
884fb1861e3da3b9f1d9ed7ff131c65afeec82dc0606d1891bbd93f3f4ef0bc1  ErdosProblems/Erdos686ReflectedSecondLift.lean
e4b13a3cf97a4565408d93b0992e35fef9d2b45ef34390c3123f9f4ec5fefe3d  compute/campaign686/reflected_second_lift_hostile_verify.py
0c80b2c07956dfb4573185e0af51691a95e23876f3eec030d3cf28ba306d9eed  compute/campaign686/test_reflected_second_lift_hostile_verify.py
```
