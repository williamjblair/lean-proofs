# Erdős 730 Kernel Closure Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove the unconditional Erdős #730 infinite-set theorem in Lean under only `[propext, Classical.choice, Quot.sound]`, replacing the target-strength density placeholder by a fully formal analytic derivation.

**Architecture:** Work on `main`, as explicitly requested, with separate modules for event counting, higher powers, fixed-depth Fourier analysis, prime-band summation, divisor switching, and final limsup/liminf assembly.  First prove `RequiredAnalyticInputs → CandidatePositiveDensityClaim`; then close the reciprocal-prime Mertens and fixed-modulus PNT-AP inputs from kernel-clean library or newly formalized analytic number theory.  Maintain a second audited route registry for any elementary replacement that removes PNT-AP or weakens Mertens, but do not change the explicit target family without a complete new density budget.

**Tech Stack:** Lean 4.29.1, pinned Mathlib 4.29.1, exact Python arithmetic for finite searches, `lake build`, repository axiom/manifest/attestation gates.

---

### Task 1: Replace the target-strength placeholder by event-count definitions

**Files:**
- Create: `ErdosProblems/Erdos730DensityEvents.lean`
- Create: `ErdosProblems/Erdos730DensityEventsAudit.lean`
- Modify: `ErdosProblems/Erdos730FullDensityReduction.lean`

**Step 1:** Define finite good, bad, branch-obstruction, and four-range event finsets over `1 ≤ x ≤ X`, with explicit prime, exponent, cofactor, and branch witnesses.

**Step 2:** Prove the pointwise transition theorem maps every bad parameter into the obstruction union.

**Step 3:** Prove the finite cardinality union bound `Bad(X) ≤ E(X)` and the disjoint range partition at `a ≥ 2`, `a=1,p≤sqrt X`, `sqrt X<p≤Y`, and `p>Y`.

**Step 4:** Run:

```sh
lake build ErdosProblems.Erdos730DensityEventsAudit
```

Expected: build succeeds; printed dependencies are a subset of the standard three axioms.

### Task 2: Specialize the higher-power dominated limit

**Files:**
- Create: `ErdosProblems/Erdos730HigherPowerDensity.lean`
- Create: `ErdosProblems/Erdos730HigherPowerDensityAudit.lean`

**Step 1:** Define the normalized `(p,a)` contribution appearing in the actual branch event count.

**Step 2:** Instantiate `padicBranchAllowedCount_le` with the exact depth `r=floor(log_p(X/p^a))`, including `r=0`.

**Step 3:** Prove pointwise convergence for fixed `(p,a)` and domination by `2/p^a`.

**Step 4:** Apply `tendsto_tsum_higherPower_of_dominated`; combine with `higherPrimePowerPairs.card/Z → 0` for the `+1` and terminal powers.

**Step 5:** Prove the exact theorem `E_higher(X)/X → 0` for all four branches and build its audit module.

### Task 3: Formalize the fixed-depth Fourier lemma

**Files:**
- Create: `ErdosProblems/Erdos730FourierPrelim.lean`
- Create: `ErdosProblems/Erdos730QuadraticGauss.lean`
- Create: `ErdosProblems/Erdos730FixedDepthFourier.lean`
- Create: `ErdosProblems/Erdos730FixedDepthFourierAudit.lean`

**Step 1:** Define additive characters on `ZMod (p^m)`, unnormalized finite Fourier transforms, digit boxes, and translated length-`p^r` intervals.

**Step 2:** Prove Fourier inversion and the zero-frequency main term for the digit-box indicator.

**Step 3:** Prove exact vanishing for effective modulus `p^m` when `m≤r` from the p-adic permutation property.

**Step 4:** Prove the unit quadratic Gauss-sum magnitude over odd prime powers and the one-nonzero-class completion formula for `m>r`.

**Step 5:** Prove the geometric interval sum and digit-box Fourier `l¹` bounds with the explicit constant `(2r+3)3^(2r)`.

**Step 6:** State and prove equation (29) exactly, uniformly in translation and polynomial coefficients, and audit every boundary (`r=1`, endpoint digit removed, effective modulus split).

### Task 4: Derive the small-prime and transition estimates from Mertens

**Files:**
- Create: `ErdosProblems/Erdos730PrimeBands.lean`
- Create: `ErdosProblems/Erdos730PrimeBandsAudit.lean`

**Step 1:** Under `MertensReciprocalPrimeInput`, prove reciprocal-prime interval estimates for real-power endpoints using natural floors.

**Step 2:** For each fixed depth `r`, combine the Fourier theorem with the exact digit density and prove equation (42).

**Step 3:** Prove the uniform depth tail (43)-(46), keeping fixed primes `5,7` outside the Fourier lemma.

**Step 4:** Sum four branches to obtain the small-prime limsup `≤4*densityBudgetSeries`.

**Step 5:** Prove the transition contribution tends to zero using the reciprocal-prime interval estimate and the ordinary prime-counting consequence of the modulus-1 input.

### Task 5: Formalize divisor switching under fixed-modulus PNT-AP

**Files:**
- Create: `ErdosProblems/Erdos730DivisorSwitching.lean`
- Create: `ErdosProblems/Erdos730DivisorSwitchingAudit.lean`

**Step 1:** Define the exact top-event pairs `(c,p)` and prove the injection from branch events using the kernel-banked top-digit classifications.

**Step 2:** Prove the periodic-class counting estimate and partial-summation lemma corresponding to equation (53).

**Step 3:** Convert qualitative fixed-modulus PNT-AP convergence into a finite uniform error over reduced classes.

**Step 4:** Sum errors over `c≤Z/Y`, prove the lower-cutoff loss is `o(Z)`, and derive `P,R≤(1/3)log 2`, `Q,S=0`.

**Step 5:** Audit the exact moduli `222138` and `148092`, class counts, endpoint inequalities, and all `sufficiently large` thresholds.

### Task 6: Close the conditional density theorem

**Files:**
- Create: `ErdosProblems/Erdos730ConditionalDensity.lean`
- Create: `ErdosProblems/Erdos730ConditionalDensityAudit.lean`
- Modify: `ErdosProblems/Erdos730FullDensityReduction.lean`

**Step 1:** Combine Tasks 1-5 and the exact budget theorem into:

```lean
theorem candidatePositiveDensity_of_requiredAnalyticInputs :
    FullDensity.RequiredAnalyticInputs →
      FullDensityReduction.CandidatePositiveDensityClaim
```

**Step 2:** Derive the exact upstream infinite-pair target from `RequiredAnalyticInputs`.

**Step 3:** Remove every statement suggesting the target-strength density claim is the analytic interface; the remaining interfaces must be Mertens and the three fixed PNT-AP instances only.

### Task 7: Kernel-prove reciprocal-prime Mertens

**Files:**
- Create: `ErdosProblems/Erdos730Mertens.lean`
- Create: `ErdosProblems/Erdos730MertensAudit.lean`
- Modify: `ErdosProblems/Erdos730AnalyticInputs.lean`

**Step 1:** Search pinned Mathlib and kernel-clean external sources for an existing theorem matching or implying `MertensReciprocalPrimeInput`.

**Step 2:** If absent, formalize a convergent Euler-product remainder and Abel summation sufficient for

```lean
∃ M, reciprocalPrimeSum N - log (log N) → M.
```

**Step 3:** Replace the unnecessarily explicit `4/log N` interface if the cleaned density chain uses only convergence and an eventual `O(1/log N)` or interval limit; prove the weakest sufficient input and update all uses.

**Step 4:** Prove the input unconditionally and audit it with no new axioms.

### Task 8: Kernel-prove fixed-modulus PNT-AP or replace it

**Files:**
- Create: `ErdosProblems/Erdos730PNTAP.lean`
- Create: `ErdosProblems/Erdos730PNTAPAudit.lean`
- Create: `compute730/full_density/approach_registry.md`

**Step 1:** Audit current Mathlib and `PrimeNumberTheoremAnd` theorem dependency graphs for a sorry-free Wiener/PNT/PNT-AP route compatible with Lean 4.29.1.

**Step 2:** Pursue the shortest kernel route: complete the missing Wiener/PNT dependency if bounded, or formalize fixed-modulus character orthogonality and the needed Tauberian theorem.

**Step 3:** In parallel, test an elementary replacement family and upper-bound-sieve route.  Any replacement must reproduce the full density budget exactly and must strictly improve the top-range class density enough to absorb the sieve constant.

**Step 4:** Prove `RequiredFixedModulusPNTAPInput` unconditionally or replace Task 5 by a strictly weaker kernel-proved input.

### Task 9: Register the unconditional headline and run all gates

**Files:**
- Modify: `ErdosProblems.lean`
- Modify: `Audit.lean`
- Modify: `proofs.yaml`
- Modify: `attestations.json`
- Modify: `FRONTIER.md`
- Modify: `README.md`
- Modify: `compute730/full_density/audit.md`

**Step 1:** Add an unconditional theorem with the exact upstream statement and no hypotheses.

**Step 2:** Run:

```sh
python3 -m pytest -q compute730/campaign_uniform compute730/full_density/test_verify.py
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
python3 scripts/emit_attestations.py
git diff --check
```

Expected: 119 exact tests pass; every new theorem has only the standard axiom footprint; the unconditional headline appears in the manifest and regenerated attestation.

**Step 3:** Hostile-audit the final dependency tree.  No target-strength lemma, unquantified uniformity, `sorry`, `native_decide`, or private analytic assumption may remain.
