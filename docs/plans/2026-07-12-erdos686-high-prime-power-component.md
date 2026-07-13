# Erdős 686 High Prime-Power Component Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Kernel-formalize the audited high prime-power component exclusion, compose it with the live Erdős 686 residual, and attest the resulting proper unbounded closure.

**Status:** Completed and integrated on 2026-07-12.  The implemented public
surface also includes the three cleaner square criteria and the uniform
`d=p^(k+t)` corollary.

**Architecture:** Add one theorem module between the existing block-product valuation layer and `Erdos686FinalResidual`.  The module first proves reusable exact factorization and normalized-unit translation lemmas, then treats `p≥5`, `p=2`, and `p=3` separately.  Each branch produces a large divisor of the positive residual `3(n+i)-d`; the existing `18/13` ratio ceiling turns the displayed component threshold into a contradiction.

**Tech Stack:** Lean 4.29.1, Mathlib 4.29.1, exact natural-number factorization and `Nat.ModEq`, repository Python exact verifier, YAML proof manifest, kernel axiom gate.

---

## Exact public surface

Create `ErdosProblems/Erdos686HighPrimePowerComponent.lean` with definitions

```lean
def highComponentLambda (p k : ℕ) : ℕ := Nat.log p (k - 1)

def highComponentMuThree (k e : ℕ) : ℕ :=
  min (highComponentLambda 3 k) (e - 2)
```

and the equation-facing theorem

```lean
theorem no_four_solution_of_highPrimePower_component
    {p e k n d : ℕ}
    (hp : p.Prime)
    (hk : 16 ≤ k) (hd : k ≤ d)
    (hexact : d.factorization p = e)
    (hcomponent : k ≤ p ^ e)
    (hthreshold :
      (p = 2 ∧
        (13 * k - 6) * d + 18 * (k - 1) ≤
          24 * 2 ^ (2 * e - highComponentLambda 2 k)) ∨
      (p = 3 ∧
        (13 * k - 6) * d + 18 * (k - 1) ≤
          6 * 3 ^ (2 * e - highComponentMuThree k e - 1)) ∨
      (5 ≤ p ∧
        (13 * k - 6) * d + 18 * (k - 1) ≤
          6 * p ^ (2 * e - highComponentLambda p k))) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n
```

If natural-subtraction normalization makes the combined theorem brittle, expose
the three prime-class theorems first and make this theorem a thin dispatcher.
The exact-valuation premise is canonical: `e = d.factorization p`, not merely
`p^e ∣ d`.

## Task 1: Freeze theorem signatures and imports

**Files:**
- Create: `ErdosProblems/Erdos686HighPrimePowerComponent.lean`
- Reference: `ErdosProblems/Erdos686PadicLift.lean`
- Reference: `ErdosProblems/Erdos686LargePrimeGapComponent.lean`
- Test: `/tmp/Erdos686HighPrimePowerComponentTest.lean`

**Step 1:** Add imports, namespace, the two exponent definitions, and theorem
signatures ending in `by` placeholders only in the temporary test file.

**Step 2:** Run:

```sh
lake env lean /tmp/Erdos686HighPrimePowerComponentTest.lean
```

Expected: all names and types elaborate; failure is confined to intentional
proof holes in the temporary file.

**Step 3:** Copy only elaborated definitions and proved helpers into the real
module.  Never commit `sorry`, `admit`, `native_decide`, a declared `axiom`, or
an `opaque` proof constant.

## Task 2: Exact factorization translation

**Files:**
- Modify: `ErdosProblems/Erdos686HighPrimePowerComponent.lean`
- Test: `/tmp/Erdos686HighPrimePowerComponentTest.lean`

**Step 1:** Prove a lower-valuation addition lemma:

```lean
lemma factorization_add_eq_left_of_lt
    {p x d e : ℕ} (hp : p.Prime) (hx : x ≠ 0) (hd : d ≠ 0)
    (hexact : d.factorization p = e)
    (hlt : x.factorization p < e) :
    (x + d).factorization p = x.factorization p
```

Use `hp.pow_dvd_iff_le_factorization` twice.  The nondivisibility of the next
power follows by subtracting `d` from `x+d`.

**Step 2:** Prove the symmetric higher-valuation lemma:

```lean
lemma factorization_add_eq_right_of_gt
    {p x d e : ℕ} (hp : p.Prime) (hx : x ≠ 0) (hd : d ≠ 0)
    (hexact : d.factorization p = e)
    (hgt : e < x.factorization p) :
    (x + d).factorization p = e
```

**Step 3:** Prove `d = p^e * ordCompl[p] d` and `¬p ∣ ordCompl[p] d` from
`hexact`, using `Nat.ordProj_mul_ordCompl_eq_self` and
`Nat.not_dvd_ordCompl`.

**Step 4:** Direct-compile the helper file.  Expected: PASS and no warnings in
the new module.

## Task 3: Normalized units and products

**Files:**
- Modify: `ErdosProblems/Erdos686HighPrimePowerComponent.lean`

**Step 1:** Define the `p`-free block product:

```lean
def pFreeBlockProduct (p k x : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, ordCompl[p] (x + i)
```

**Step 2:** Prove by Finset induction that `ordCompl` commutes with a finite
product, then derive

```lean
pFreeBlockProduct p k (n+d) = ordCompl[p] 4 * pFreeBlockProduct p k n
```

from the exact block equation.

**Step 3:** Prove that every such full or restricted product is nonzero and is
not divisible by `p`.

**Step 4:** For `s=(x.factorization p)<e` and `s≤L`, prove

```lean
ordCompl[p] (x+d) ≡ ordCompl[p] x [MOD p^(e-L)]
```

by writing `x=p^s*u` and `d=p^e*m`.  Prove `L<e` before every truncated
subtraction rewrite.

**Step 5:** Lift the pointwise congruence to any Finset of indices whose lower
valuations are at most `L`.

## Task 4: Maximum owner and total valuation accounting

**Files:**
- Modify: `ErdosProblems/Erdos686HighPrimePowerComponent.lean`

**Step 1:** Package `Finset.exists_max_image` for the lower block, retaining
both the owner membership and the pointwise maximum property.

**Step 2:** Prove that `p^e≥k` makes a `p^e`-divisible lower term unique.  The
existing `unique_dvd_add_of_mem_Icc_of_le` accepts the composite modulus
`p^e` and needs only `k≤p^e`.

**Step 3:** Expand both block-product factorizations as Finset sums and prove:

- if the maximum is below `e`, every translated valuation is unchanged;
- if the maximum is above `e`, the owner drops to `e` and all other
  valuations are unchanged;
- the equation requires upper total valuation to equal lower total valuation
  for odd `p`, and lower total plus two for `p=2`.

**Step 4:** Direct-compile and add temporary examples at the boundary `k=p^e`.

## Task 5: The `p≥5` branch

**Files:**
- Modify: `ErdosProblems/Erdos686HighPrimePowerComponent.lean`

**Step 1:** Exclude maximum valuation `<e` modulo `p`: the normalized product
is unchanged, but the equation multiplies it by four.  Therefore `p∣3U`,
contradicting `p≥5` and `p∤U`.

**Step 2:** Exclude maximum valuation `>e` using Task 4.

**Step 3:** At the unique owner `n+i=p^e*a`, prove all nonowners have valuation
at most `lambda=Nat.log p (k-1)`.  Use divisibility of their powers into the
nonzero index distance and `padicValNat_le_nat_log`, or the existing
factorization-concentration proof pattern.

**Step 4:** Cancel the nonowner unit product modulo `p^(e-lambda)` and prove

```lean
p^(e-lambda) ∣ 3*a - ordCompl[p] d.
```

**Step 5:** Multiply by the owner component to obtain

```lean
p^(2*e-lambda) ∣ 3*(n+i)-d.
```

## Task 6: The `p=2` branch

**Files:**
- Modify: `ErdosProblems/Erdos686HighPrimePowerComponent.lean`

**Step 1:** Exclude maximum `<e` because all term valuations are unchanged
while multiplication by four requires an increase of exactly two.

**Step 2:** Exclude maximum `>e` because the total valuation decreases.

**Step 3:** At the owner, derive upper valuation `e+2`.  Writing
`n+i=2^e*a`, `d=2^e*m`, set `b=(a+m)/4` and prove `b` is the upper odd unit.

**Step 4:** Use equality of odd block products and cancel the nonowner product
modulo `2^(e-lambda)` to prove `b≡a`, hence

```lean
2^(e-lambda+2) ∣ 3*a-m
```

and therefore `2^(2*e-lambda+2)` divides the positive residual.

## Task 7: The `p=3` owner set

**Files:**
- Modify: `ErdosProblems/Erdos686HighPrimePowerComponent.lean`

**Step 1:** Prove `e≥3` from `3^e≥k≥16` and set `h=3^(e-1)`.

**Step 2:** Exclude maximum `≤e-2` modulo nine, maximum `>e` by total
valuation, and maximum `=e` modulo three.

**Step 3:** Define the owner set of terms with valuation `e-1`.  Map an owner
`i` to `((n+i)/h)%3`.  It lies in `Icc 1 2`; equality of two images makes
`3h=3^e` divide the index distance, so the map is injective.  Apply
`Finset.card_le_card_of_injOn` to get cardinality at most two.

**Step 4:** If the owner set has two elements, split the `p`-free product into
owners and nonowners modulo nine.  The two owner units occupy residues one
and two modulo three.  Expanding

```text
(a1+3m)(a2+3m) = 4*a1*a2  (mod 9)
```

forces `m(a1+a2)=a1a2 (mod 3)`, i.e. `0=2`, contradiction.

**Step 5:** The owner set is therefore a singleton.  All nonowners have
valuation at most `mu=min(lambda,e-2)`.  Cancel them modulo `3^(e-mu)` and
divide the resulting congruence by three to obtain

```lean
3^(e-mu-1) ∣ a-m
```

and `3^(2*e-mu-1)` dividing the positive residual.

## Task 8: Archimedean contradiction and public theorems

**Files:**
- Modify: `ErdosProblems/Erdos686HighPrimePowerComponent.lean`
- Test: `compute/campaign686/agent_t2_high_component/test_high_component_verify.py`

**Step 1:** Factor the exact component as `d=p^e*m`.  From
`nine_mul_gap_lt_n_of_four_solution` prove positivity of `3a-m` (`p≠3`) or
`a-m` (`p=3`).

**Step 2:** Reuse
`eighteen_mul_n_add_one_lt_thirteen_mul_k_mul_gap_of_four_solution` to show the
residual is strictly below `R_k(d)/6` without division.

**Step 3:** Combine the divisibility lower bound with each non-strict threshold
to derive the contradiction.  Add the corollary excluding every
`d=p^(k+t)` for `k≥16` if its elementary exponent inequalities remain small
and kernel-transparent.

**Step 4:** Run:

```sh
lake env lean ErdosProblems/Erdos686HighPrimePowerComponent.lean
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_t2_high_component/test_high_component_verify.py
```

Expected: Lean PASS; `7 passed` for the frozen exact verifier.

## Task 9: Compose and attest

**Files:**
- Modify: `ErdosProblems/Erdos686FinalResidual.lean`
- Modify: `ErdosProblems.lean`
- Modify: `Audit.lean`
- Modify: `proofs.yaml`
- Modify: `FRONTIER.md`
- Modify: `PROGRESS_Erdos686.md`
- Modify: `compute/campaign686/approach_registry.md`
- Modify: `compute/campaign686/audit.md`
- Modify: `compute/campaign686/final_residual_hostile_audit.md`
- Modify: `attestations.json`

**Step 1:** Import the module and add every public theorem to `Audit.lean` and
`proofs.yaml`.  Add the high-component exclusion as an explicit banked
restriction in `FinalResidual686Hypothesis`; prove both equivalence directions
still hold.

**Step 2:** Replace `Lean OPEN` in the high-component audit only after the
kernel theorem, exact verifier, manifest, and attestation all pass.

**Step 3:** Run the final gates:

```sh
git diff --check
bash scripts/check_manifest.sh
lake build
bash scripts/check_axioms.sh
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider compute/campaign686
python3 scripts/emit_attestations.py
```

Expected: build success; every headline axiom footprint is a subset of
`[propext, Classical.choice, Quot.sound]`; manifest and attestation counts
match; no `native_decide`.

**Step 4:** Commit and push `main`, then verify `git rev-parse HEAD` equals
`git ls-remote origin refs/heads/main`.

## Non-goals and audit boundaries

- Do not import or assume the Nair--Shorey greatest-prime-factor theorem; its
  short strip remains external and paper-only.
- Do not replace `FinalResidual686Hypothesis` with the stale even-only residual
  from the GPT-Pro attachment.
- Do not call a finite parameter sweep a proof of the universal theorem.
- Do not route through the raw local quadratic lift: its factorial loss is too
  large to recover `Nat.log p (k-1)`.
- Preserve the fixed-prefix, MalekZ, smooth-block, and telescope fixtures in
  the hostile audit; this theorem uses exact equations and valuations, not a
  congruence-only obstruction.
