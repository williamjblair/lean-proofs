# Hostile audit: G-B corridor-bridge elimination

Verdict: **PASS for the quantified bridge elimination and bridge-free
reduction. Full RL* remains unproved.**

## Dependency tree

1. **Partner-distance identities — PASS.**
   - Exact claims: `1 <= p(d) <= 3`; `p(d)=3` iff `d=1`; predecessor and
     successor changes are at most one in the directions used.
   - Kernel: `partnerDistance_pos`, `partnerDistance_le_three`,
     `partnerDistance_eq_three_iff`, `rlBudget_pred_le`.

2. **Exact interior induction gate — PASS.**
   - Claim: the two minimal composites are strict subinstances iff
     `p(d1)<n2` and `p(d2)<n1`.
   - Kernel: `minimalComposite_sizes_lt_series_of_partner_lt`,
     `minimalComposite_sizes_lt_series_iff`.
   - No non-strict or uniform `n_i>=4` substitution remains.

3. **Residual gate dispatch — PASS.**
   - Quantified claim: under `n>=14`, exact size/distance splitting, and
     `2*s*p(d)<(d+1)^2`, gate failure implies `n1=2` or `n2=2`.
   - Kernel: `residual_series_gate_or_endpoint_pair`.
   - Independent exact reproduction: all admissible tuples with
     `2<=n1,n2<40` in `test_gap_gb_joint_verify.py`.

4. **Two-vertex interior side — PASS.**
   - Positive local distance plus order two makes the outer endpoint a
     leaf. Distance at most one inside the component excludes every legal
     M-edge; the bridge lemma excludes crossing M-edges.
   - Existing paper nodes: M-free root move and stub retraction, Lemmas
     3.2 and 3.3 of `lemma_rl_proof.md`.
   - Budget kernel: `rlBudget_pred_le`.

5. **Small endpoint block — PASS.**
   - For `a<=3`, connectedness gives diameter at most two, so no M-edge can
     satisfy `d_B>=4`. RFC restriction is literal because no M-edge crosses
     the bridge. Exact parameter change is `d-1`, `s-(a-1)`.
   - Budget kernel: `rlBudget_endpointBlock_retraction_le`.

6. **Large endpoint block — PASS.**
   - For `a>=4`, `p(d-1)<=3<a` supplies the strict minimal-composite gate
     for the remaining rooted block. The endpoint block itself is an
     ordinary smaller valid instance and receives the stated `a^2` Gamma
     bound from the induction hypothesis.
   - Budget kernel: `gammaBlock_endpointBridge_le_rlBudget`.

7. **Canonical interval cover — PASS.**
   - Every specified nonbridge corridor edge is covered by a canonical
     off-corridor component interval; span is at most component order plus
     one; component orders sum exactly to `s`; component count is at most
     `s`.
   - Kernel: `IsGeodesic.corridorIndexSet_card_le_twice_slack` and its
     already-verified dependencies in `Erdos23GapGA*.lean`.

8. **Full bridge-free parameter reduction — PASS.**
   - Exact claims: all corridor edges nonbridge implies `d<=2s`; with
     `n=d+1+s>=14`, this implies `s>=5`.
   - Kernel: `IsGeodesic.length_le_twice_slack_of_all_nonbridge`,
     `IsGeodesic.slack_at_least_five_of_large_all_nonbridge_corridor`.

## Falsification record

- **Both equality-family ends:** no global joint-distance inequality is
  asserted. The long-tail C5 blow-up is explicitly reproduced and violates
  `sum D<=2s`; its tail bridge is handled by series reduction. The tight
  `d=1` equality family lies outside the residual.
- **n=8 forced hub:** reproduced exactly (`load=10>8`). No vertex-load
  statement occurs in the proof.
- **n=12 path packing:** reproduced exactly (`sum(D+1)=20>18` and
  `sum D=16>14`). No volume or unit-congestion statement occurs.
- **Mixed distances:** the rooted `[4,6]` fixture is reproduced exactly;
  no constant-distance hypothesis occurs.
- **Strict boundaries:** the residual predicate uses strict `<`; the gate
  uses strict `<`; two- and three-vertex sides are dispatched separately.
- **Endpoint edges:** treated explicitly in both orientations, not silently
  included in the positive-distance series theorem.
- **Natural subtraction:** `a-1<=s` is quantified from the retained
  geodesic vertices; the Lean budget theorem is valid even before using
  that side condition.

## Exact arithmetic reproduction

`python -m pytest -q compute23/gate3/test_gap_gb_joint_verify.py` checks:

- all mandatory killed fixtures;
- the strict residual boundary;
- exact interior size-gate extension;
- exhaustive bounded residual dispatch;
- a `100 x 98` endpoint-move grid; and
- a `98 x 100 x 99` endpoint-block absorption grid.

All arithmetic is integer arithmetic. No floating point or heuristic result
is a proof dependency; the discovery-only random harness was not banked.

## Kernel gate

`lake env lean ErdosProblems/Erdos23GapGBJoint.lean` reports only
`[propext, Classical.choice, Quot.sound]` or subsets for every new theorem.
There is no `sorry`, `axiom`, private theorem, or `native_decide`.

## Single remaining quantified lemma

For every valid one-stub rooted instance with

```text
n>=14, |M|>=2, 5<=s, d<=2s,
2*s*p(d)<(d+1)^2,
and some w-x0 geodesic P satisfying
  forall i<d, not IsBridge_B(P_i P_{i+1}),
```

prove

```text
sum_{uv in M} (d_B(u,v)+1)^2
  <= s*(2*d+2+s)+2*s*p(d).
```

This is BF-RL. No theorem-strength replacement for BF-RL is claimed.
