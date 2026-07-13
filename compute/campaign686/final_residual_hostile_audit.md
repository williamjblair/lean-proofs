# Hostile audit: the final Erdős 686 residual

Status: **PASS as exact equivalent packaging after new unconditional results;
FAIL as a proof of either original target.**

The checked-in declaration `FinalResidual686Hypothesis` is the one remaining
quantified lemma. It is not asserted, assumed as an axiom, or described as a
solution.  Despite its restricted-looking premises, it is theorem-strength
equivalent to `OddThueTail1000Hypothesis ∧ LargeKSmoothHypothesis`; the
checked-in theorem `finalResidual_iff_tail1000_and_smooth` records this audit.

## Dependency tree

```text
FinalResidual686Hypothesis
|
+-- odd arm
|   +-- exact target row membership
|   +-- d >= 10^1000
|   +-- complete AllOwnerAssemblyThirdNonzeroCertificate
|   +-- residual arm gives contradiction
|   `-- certified 10^120 <= d < 10^1000 band restores old tail
|
+-- large-row arm
|   +-- k >= 16 and d >= k
|   +-- k not in {16,18,20,24,28,32}
|   +-- 1218443*k*d < 1853952*n
|   +-- every even representation k=2r lies below explicit M_r
|   +-- every split-factorial prime-power lower term excluded
|   +-- every p>k owner a*p^A with 3707904*a <= 1218443*k excluded
|   +-- every p^e|d with p>=k lies below the component-square ceiling
|   +-- every exact p^e||d with p^e>=k violates its canonical
|       high-component dominance threshold (separate p=2, p=3, p>=5 bounds)
|   +-- one complete cleaned assignment has every bucket below that ceiling
|   +-- k=p^a-1, p>=5 excludes p^a from both endpoint parameters
|   +-- odd whole two-large-prime gaps carry the A=3k+2 Pell certificate
|   +-- their reflected harmonic simultaneous-zero value is nonintegral
|   `-- residual arm gives contradiction
|
`-- old terminal N=4 reduction gives not universal Erdős 686
```

## Per-node verdicts

| Node | Verdict | Evidence |
|---|---|---|
| Six-row band below `10^1000` | PASS | Six ordinary-kernel Farey certificates and independent exact verifier. |
| Complete odd owner certificate | PASS | Lean constructs all buckets with unchanged loss, exact residuals, all second/third divisibilities, and all second/third obstructions nonzero. |
| Rows 16,18,20,24,28,32 | PASS | Unconditional Lean theorems; the large covers use sharded ordinary `decide`. |
| Universal even tail | PASS | Lean constructs the polynomial certificate for every `r>=2`; no external theorem. |
| `1218443kd<1853952n` | PASS | Exact centered-pair product inequality, seven-term power bracket, and ratio-window composition in Lean. |
| Prime-power lower-term exclusions | PASS | Exact valuation/factorial-loss theorems in Lean. |
| Gap-component square ceiling | PASS | The local quadratic lift and exact `18/13` window prove the strict bound for every `p^e|d`, `p>=k`. |
| All-prime high-component thresholds | PASS | `no_four_solution_of_highPrimePower_component` and its exact `p=2`, `p=3`, and `p>=5` branches prove the three canonical exclusions with exactly `[propext, Classical.choice, Quot.sound]`. |
| Complete grouped-owner ceiling | PASS | Global concentration constructs one assignment; every grouped square divides its positive residual and inherits the same strict bound. |
| Prime-power boundary rows | PASS | Lucas arithmetic proves `p^a` divides neither endpoint when `k=p^a-1`, `p>=5`. |
| Reflected harmonic obstruction | PASS | Vendored Sylvester--Schur plus a p-adic interval wrapper proves uniform nonintegrality, and the formal coefficient bridge proves that distinct-owner second obstructions cannot both vanish. |
| Equivalence to the updated two targets | PASS | Both directions are proved by `finalResidual_iff_tail1000_and_smooth`. |
| Residual contradiction itself | OPEN | This is precisely `FinalResidual686Hypothesis`. |
| Full Erdős 686 refutation without the residual premise | NOT CLAIMED | The terminal theorem remains conditional on the displayed residual. |

## Quantified boundaries

- Odd cutoff: the finite certificate uses `d < 10^1000`; equality belongs to
  the residual arm.
- Even cutoff: the unconditional theorem uses
  `d >= max(2r, certificate.threshold)`; equality is excluded, and the
  residual uses strict `<`.
- Closed rows: the exact assumptions are `16<=d`, `18<=d`, `20<=d`,
  `24<=d`, `28<=d`, and `32<=d`, respectively.
- Prime-power interior: the exact all-prime criterion is

  ```text
  v_p((k-1)!) <= v_p(4) + v_p((i-1)! (k-i)!).
  ```

  It is not silently generalized to all `p<=k`.
- Large-base cofactor: the residual excludes exactly
  `3707904*a<=1218443*k`, obtained from
  `1218443*k*d<1853952*n` and `d>=k`; no `O(k)` phrase replaces this inequality.
- Gap components and grouped buckets: equality belongs to the excluded side;
  every solution gives the strict inequality
  `6h^2<(13k-6)d+18(k-1)`.
- All-prime high components: if `p^e || d` and `k<=p^e`, every surviving
  solution satisfies the strict reverse inequalities

  ```text
  p=2:  (13k-6)d+18(k-1) > 24*2^(2e-lambda_2(k));
  p=3:  (13k-6)d+18(k-1) >  6*3^(2e-mu_3(k,e)-1);
  p>=5: (13k-6)d+18(k-1) >  6*p^(2e-lambda_p(k)).
  ```

  Equality is excluded by the formal theorem; no asymptotic or unspecified
  constant is hidden here.

## Mandatory fixtures

| Fixture | Verdict |
|---|---|
| k=9 and k=15, d=1 telescopes | Outside `d>=10^1000`; preserved. |
| `(984,3177026,4480)` | Not an equation; no row-prefix conclusion is applied. |
| n=48502 cluster | Not an equation; no row-prefix conclusion is applied. |
| MalekZ k=5 all-moduli family | No pure congruence closure is claimed. |
| Interior p=2 fixture `(A,k,d,i,n)=(9,33,33,2,510)` | Reproduced; fails the split-factorial premise, so the unrestricted claim is rejected. |
| Interior p=3 fixture `(5,16,19,8,235)` | Reproduced; likewise outside the exact premise. |
| Reflection-compatible k=19 four-cycle | Reproduced; fails the lower ratio window and is not an equation. |

## Reproduction

```bash
lake env lean ErdosProblems/Erdos686FinalResidual.lean
lake env lean ErdosProblems/Erdos686HighPrimePowerComponent.lean
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_cf_tail_e1000 \
  compute/campaign686/agent_t2_even_tail \
  compute/campaign686/agent_t2_even_tail_coefficient \
  compute/campaign686/agent_t2_even_tail_supply \
  compute/campaign686/agent_t2_even_uniform_sqrt \
  compute/campaign686/agent_t2_even_k28 \
  compute/campaign686/agent_t2_even_k32 \
  compute/campaign686/agent_t2_small_prime_band \
  compute/campaign686/agent_t2_consecutive_property \
  compute/campaign686/agent_t2_binomial_kummer \
  compute/campaign686/agent_t2_large_prime_same_owner \
  compute/campaign686/agent_t2_large_odd_two_prime_pell \
  compute/campaign686/agent_t2_high_component
```

Every theorem named by the residual composition must print an axiom set
contained in `[propext, Classical.choice, Quot.sound]`. No `native_decide`,
`sorry`, `admit`, or custom theorem axiom is permitted.
