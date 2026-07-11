# G-B joint frontier: complete corridor-bridge elimination

Status: **PROVED proper enlargement of the banked series slice.** This is
not a proof of all RL*. It proves RL for every residual instance having a
bridge on a selected root-stub geodesic and reduces the exact open core to a
fully bridge-free corridor with `s >= 5` and `d <= 2s`.

## 1. Statement

Let `R=(B,M,w,x0)` be a valid one-stub rooted instance in the strict RL*
residual

```text
n >= 14,  2 <= s,  2*s*p(d) < (d+1)^2,  |M| >= 2,
d = dist_B(w,x0),  s = n-1-d.
```

Fix a `w`-`x0` geodesic `P=(u_0,...,u_d)`. Under the strict Gamma induction
hypothesis, **if any edge of `P` is a bridge of `B`, then `R` satisfies RL**.
Consequently, a minimal residual counterexample may be assumed to satisfy

```text
forall i < d, not IsBridge_B(u_i u_{i+1}),
5 <= s,
d <= 2*s.
```

The only remaining quantified lemma is therefore:

> **BF-RL.** Every valid one-stub rooted instance satisfying the displayed
> residual assumptions and admitting a root-stub geodesic all of whose edges
> are nonbridges satisfies
> `Gamma_int <= s*(2*d+2+s)+2*s*p(d)`.

BF-RL is a strict graph class, not a renamed unrestricted RL statement.

## 2. Interior bridge

Let `u_k u_{k+1}` be a bridge with `1 <= k` and `k+1 < d`. Its deletion
gives root and stub components of orders `n1,n2` and positive local distances
`d1=k`, `d2=d-k-1`. The bridge cut lemma gives no M-edge between the two
components. RFC restricts to a valid one-stub block on each side, Gamma and
slack split, and the banked series budget is superadditive.

The exact induction-size gate is

```text
p(d1) < n2  and  p(d2) < n1.                         (G)
```

Indeed the two minimal composites have orders `n1+p(d1)` and `n2+p(d2)`;
both are strictly below `n1+n2` exactly under (G). The Lean theorems
`minimalComposite_sizes_lt_series_of_partner_lt` and
`minimalComposite_sizes_lt_series_iff` retain this exact gate.

Suppose (G) fails and neither component has order two. Since a positive
geodesic fits in each component, `n1,n2 >= 3`. Also `p <= 3`. A failure of
(G) therefore forces one component to have order three and the partner
distance on the other side to equal three. Since `p(t)=3` iff `t=1`, the
global distance is at most four. But `n>=14` then gives `s>=9`; direct
evaluation at `d=3,4` contradicts
`2*s*p(d)<(d+1)^2`. This is
`residual_series_gate_or_endpoint_pair` in Lean.

It remains that one bridge component has order two. Its positive local
distance is one. No legal M-edge lies inside a two-vertex component, and the
bridge lemma excludes an M-edge leaving it. Hence the outer endpoint `w` or
`x0` is an M-free B-leaf. Root move or stub retraction deletes that leaf,
preserves Gamma, produces a smaller valid rooted instance, and does not
increase the budget. The last arithmetic assertion is `rlBudget_pred_le`.

Thus every interior bridge is reduced, including every former side-of-order
two or three exception.

## 3. Endpoint bridge

Consider the first corridor edge `w u_1`; the last edge is symmetric. Let
`A` be its component containing `w`, of order `a`, and let `C` contain the
stub. Again no M-edge crosses the bridge.

If `a <= 3`, then `diam(B[A]) <= a-1 <= 2`, so `A` contains no legal M-edge.
Delete `A` and move the root to `u_1`. Restricting RFC to `C` proves the new
rooted instance valid. Its parameters are

```text
dC = d-1,  sC = s-(a-1),  GammaC = Gamma.
```

Here `a-1 <= s` because `C` contains the `d` vertices
`u_1,...,u_d`. Monotonicity in slack followed by root move gives

```text
F(s-(a-1),d-1) <= F(s,d),
```

where `F=rlBudget`; this is `rlBudget_endpointBlock_retraction_le`.

If `a >= 4`, restriction gives an ordinary valid instance on `A`, so strict
Gamma induction gives `Gamma_A <= a^2`. The rooted block `C` has minimal
composite order `|C|+p(d-1) < |C|+a=n`, because `p <= 3 < a`; hence the
already-proved minimal-composite equivalence gives RL on `C`. Exact expansion
then gives

```text
Gamma_A + F(sC,d-1) <= a^2 + F(sC,d-1)
                      <= F(sC+a-1,d).
```

The second inequality is
`gammaBlock_endpointBridge_le_rlBudget`. Thus endpoint bridges reduce for
every component order. The exhaustive order dispatch itself is kernel checked
as `endpointBlock_small_or_partner_lt`.

## 4. Full nonbridge consequence

Assume every edge of `P` is a nonbridge. For each corridor index `i`, the
banked canonical cut theorem supplies an off-corridor component whose
attachment interval covers `i`. A component `C` of order `q_C` has interval
span at most `q_C+1`. The canonical components partition the `s` vertices
outside `P`, and each has positive order. Therefore

```text
d <= sum_C (q_C+1)
  =  s + number_of_components
  <= 2*s.
```

This entire graph-level count is kernel checked as
`IsGeodesic.length_le_twice_slack_of_all_nonbridge`; it does not assume that
the whole graph is 2-connected. Finally `n=d+1+s>=14` and `d<=2s` imply
`s>=5`, kernel checked as
`IsGeodesic.slack_at_least_five_of_large_all_nonbridge_corridor`.

## 5. Exact frontier change

The previous bank closed only interior bridges with both sides of order at
least four. The present proof closes:

1. all interior side-of-order-three cases through the exact size gate;
2. all interior side-of-order-two cases by M-free endpoint retraction;
3. both endpoint corridor bridges, for every endpoint-component order; and
4. all residual rows `s=2,3,4` as an immediate structural consequence.

What remains is the genuine simultaneous-distance aggregation BF-RL above.
No volume packing, per-vertex load, summed SE1/SE2, or multicommodity
routability statement is used.

## 6. Exact weighted-cut dual interface

One further non-closing interface is banked for BF-RL. For every integer
potential `f:V->Nat`, summing RFC over the threshold cuts `{v:k<f(v)}` gives

```text
sum_{uv in M} |f(u)-f(v)| + |f(w)-f(x0)|
  <= sum_{ab in B} |f(a)-f(b)|.                         (C)
```

The layer-cake identity and (C) are kernel checked as
`sum_thresholdSeparation_eq_dist` and
`rootedCutCondition_natPotential_of_allCuts` (with the threshold-family core
`rootedCutCondition_natPotential`). The original root-excluding RFC form is
connected kernel-side by `rootedCutCondition_natPotential_of_rootCuts`.
This is a genuine cut-dual reformulation,
but it does not itself supply a potential whose left side majorizes the
quadratic Gamma objective at the required right-side cost. That construction
is part of BF-RL and is not claimed.

The complement step is exact: cut edge counts and terminal separation are
unchanged.

The landing condition is also kernel checked. If `|M|>=2`, a bounded
potential `f` and reserve `lambda` suffice when

```text
(D_uv+1)^2 + lambda <= |f(u)-f(v)|       for every uv in M,
sum_B |Delta f| <= |f(w)-f(x0)| + F(s,d) + 2*lambda.
```

Coarea then pays one `lambda` per M-edge and the two guaranteed edges absorb
the `2*lambda` allowance. This is
`rootedCutCondition_totalCost_le_of_potentialCertificate`. The missing BF-RL
work is the uniform construction of such a potential, not the certificate
algebra.
