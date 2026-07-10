# Erdos699 T6 Prime Power Part Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Package the existing per-prime-power T6 row forcing into multiplicity-aware divisibility statements for the product of all prime-power factors at primes `p >= 5`.

**Architecture:** Add `primePowerPartGE`, the full-multiplicity analogue of `primeRadicalGE`, to `lean/Erdos699/Proved/Basic.lean`. Prove a generic finset product lemma for pairwise coprime prime powers, a factorization-based divisor theorem, row-3 instantiations for `n - 1` and `n - 2`, and a small equality bridge when all prime factors are in the large range. Keep all statements support-level only; full T6/T7 remain open.

**Tech Stack:** Lean 4, Mathlib `Nat.factorization`, existing `Erdos699.Proved.Basic`, exact Python criterion tests.

---

### Task 1: Red WIP API Check

**Files:**
- Create: `lean/Erdos699/WIP/T6PrimePowerPartTest.lean`

- [x] **Step 1: Write the failing API check**

```lean
import Erdos699.Proved.Basic

#check Erdos699.primePowerPartGE
#check Erdos699.prime_power_coprime_finset_prime_power_prod_of_not_mem
#check Erdos699.finset_prod_prime_powers_dvd_of_forall_dvd
#check Erdos699.primePowerPartGE_dvd_of_forall_prime_power_dvd
#check Erdos699.i_three_window_one_primePowerPartGE_dvd
#check Erdos699.i_three_window_two_primePowerPartGE_dvd
#check Erdos699.primePowerPartGE_eq_self_of_forall_prime_ge
#check Erdos699.i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd
```

- [x] **Step 2: Run Lean and confirm expected failure**

```bash
lake env lean lean/Erdos699/WIP/T6PrimePowerPartTest.lean
```

Expected: unknown constants for the eight new names.

### Task 2: Add Multiplicity-Aware Large Part

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add `primePowerPartGE` after `primeRadicalGE`**

```lean
/-- Product of the full prime-power divisors of `m` whose prime is at least `lo`. -/
def primePowerPartGE (lo m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => lo ≤ p), p ^ m.factorization p
```

- [x] **Step 2: Add the coprime prime-power product helper**

```lean
theorem prime_power_coprime_finset_prime_power_prod_of_not_mem {p : ℕ} {e : ℕ}
    {s : Finset ℕ} {f : ℕ → ℕ} (hp : p.Prime)
    (hs : ∀ q ∈ s, q.Prime) (hnot : p ∉ s) :
    (p ^ e).Coprime (∏ q ∈ s, q ^ f q) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hp_ne_a : p ≠ a := by
        intro hpa
        apply hnot
        rw [hpa]
        exact Finset.mem_insert_self a s
      have hpa_coprime : (p ^ e).Coprime (a ^ f a) :=
        Nat.coprime_pow_primes e (f a) hp
          (hs a (Finset.mem_insert_self a s)) hp_ne_a
      have hp_not_s : p ∉ s := by
        intro hps
        exact hnot (Finset.mem_insert_of_mem hps)
      have hprod : (p ^ e).Coprime (∏ q ∈ s, q ^ f q) :=
        ih (fun q hq => hs q (Finset.mem_insert_of_mem hq)) hp_not_s
      exact hpa_coprime.mul_right hprod
```

- [x] **Step 3: Add the generic product divisibility helper**

```lean
theorem finset_prod_prime_powers_dvd_of_forall_dvd {s : Finset ℕ} {e : ℕ → ℕ}
    {x : ℕ} (hprime : ∀ p ∈ s, p.Prime)
    (hdiv : ∀ p ∈ s, p ^ e p ∣ x) :
    (∏ p ∈ s, p ^ e p) ∣ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hacoprime : (a ^ e a).Coprime (∏ p ∈ s, p ^ e p) :=
        prime_power_coprime_finset_prime_power_prod_of_not_mem
          (p := a) (e := e a) (s := s) (f := e)
          (hprime a (Finset.mem_insert_self a s))
          (fun p hp => hprime p (Finset.mem_insert_of_mem hp)) ha
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hacoprime
        (hdiv a (Finset.mem_insert_self a s))
        (ih (fun p hp => hprime p (Finset.mem_insert_of_mem hp))
          (fun p hp => hdiv p (Finset.mem_insert_of_mem hp)))
```

### Task 3: Add Factorization and Row Instantiations

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add the factorization package theorem**

```lean
theorem primePowerPartGE_dvd_of_forall_prime_power_dvd {lo m x : ℕ}
    (h : ∀ p : ℕ, p.Prime → lo ≤ p → p ∣ m → p ^ m.factorization p ∣ x) :
    primePowerPartGE lo m ∣ x := by
  classical
  unfold primePowerPartGE
  apply finset_prod_prime_powers_dvd_of_forall_dvd
  · intro p hp_mem
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp_mem).1).1
  · intro p hp_mem
    rcases Finset.mem_filter.mp hp_mem with ⟨hpm, hlo⟩
    exact h p (Nat.mem_primeFactors.mp hpm).1 hlo (Nat.mem_primeFactors.mp hpm).2.1
```

- [x] **Step 2: Add row-3 full-multiplicity large-part theorems**

```lean
theorem i_three_window_one_primePowerPartGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 1 < n) :
    primePowerPartGE 5 (n - 1) ∣ j * (j - 1) := by
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp hp5 hpdvd
  have hm_ne : n - 1 ≠ 0 := by omega
  have hpowdvd : p ^ (n - 1).factorization p ∣ n - 1 :=
    (hp.pow_dvd_iff_le_factorization hm_ne).mpr le_rfl
  exact i_three_window_one_prime_pow_dvd_mul_sub_one hnone hp hp5 hn hpowdvd

theorem i_three_window_two_primePowerPartGE_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q) (hn : 2 < n) :
    primePowerPartGE 5 (n - 2) ∣ j * (j - 1) * (j - 2) := by
  apply primePowerPartGE_dvd_of_forall_prime_power_dvd
  intro p hp hp5 hpdvd
  have hm_ne : n - 2 ≠ 0 := by omega
  have hpowdvd : p ^ (n - 2).factorization p ∣ n - 2 :=
    (hp.pow_dvd_iff_le_factorization hm_ne).mpr le_rfl
  exact i_three_window_two_prime_pow_dvd_mul_sub_one_sub_two hnone hp hp5 hn hpowdvd
```

### Task 4: Add Large-Part Equality Bridge

**Files:**
- Modify: `lean/Erdos699/Proved/Basic.lean`

- [x] **Step 1: Add equality when every prime divisor is large**

```lean
theorem primePowerPartGE_eq_self_of_forall_prime_ge {lo m : ℕ}
    (hm : m ≠ 0) (hlo : ∀ p : ℕ, p.Prime → p ∣ m → lo ≤ p) :
    primePowerPartGE lo m = m := by
  classical
  unfold primePowerPartGE
  have hfilter : m.primeFactors.filter (fun p => lo ≤ p) = m.primeFactors := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).1
    · intro hp
      exact Finset.mem_filter.mpr
        ⟨hp, hlo p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1⟩
  rw [hfilter]
  simpa [Nat.prod_factorization_eq_prod_primeFactors] using
    Nat.prod_factorization_pow_eq_self hm
```

- [x] **Step 2: Add the case-I row-one `n - 1` bridge**

```lean
theorem i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd {n j : ℕ}
    (hnone : ∀ q : ℕ, ¬ commonPrimeDivisor n 3 j q)
    (hn : 1 < n) (h2n : 2 ∣ n) (h3n : 3 ∣ n) :
    n - 1 ∣ j * (j - 1) := by
  have hlarge : primePowerPartGE 5 (n - 1) = n - 1 := by
    apply primePowerPartGE_eq_self_of_forall_prime_ge
    · omega
    · intro p hp hpdvd
      by_cases hp2 : p = 2
      · subst p
        rcases h2n with ⟨a, ha⟩
        rcases hpdvd with ⟨b, hb⟩
        omega
      by_cases hp3 : p = 3
      · subst p
        rcases h3n with ⟨a, ha⟩
        rcases hpdvd with ⟨b, hb⟩
        omega
      have hp4 : p ≠ 4 := by
        intro hp_eq
        subst p
        exact (by decide : ¬ Nat.Prime 4) hp
      have hp2le : 2 ≤ p := hp.two_le
      omega
  rw [← hlarge]
  exact i_three_window_one_primePowerPartGE_dvd hnone hn
```

### Task 5: Verification, Cleanup, and Commit

**Files:**
- Modify: `notes/PROGRESS.md`
- Delete: `lean/Erdos699/WIP/T6PrimePowerPartTest.lean`

- [x] **Step 1: Run WIP API check green and remove WIP file**

```bash
lake env lean lean/Erdos699/WIP/T6PrimePowerPartTest.lean
```

Expected: Lean prints all eight theorem signatures. Then delete the WIP file.

- [x] **Step 2: Add the `[R]` progress entry**

```md
- [R] Proved T6 full-multiplicity large-prime-part packaging:
  `Erdos699.primePowerPartGE`,
  `Erdos699.i_three_window_one_primePowerPartGE_dvd`, and
  `Erdos699.i_three_window_two_primePowerPartGE_dvd` package the existing
  per-prime-power row forcing into full multiplicity for all primes `p ≥ 5`.
  Also proved the case-I row-one bridge
  `Erdos699.i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd`.
  Full T6/T7 remain open.
```

- [x] **Step 3: Run verification gates**

```bash
lake env lean lean/Erdos699/Proved/Basic.lean
python3 -m pytest compute/tests/test_criterion.py -q
rg -n "\bsorry\b|\badmit\b" lean/Erdos699/Proved || true
git diff --check
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
lake env lean --stdin <<'EOF'
import Erdos699.Proved.Basic
#print axioms Erdos699.i_three_window_one_sub_one_dvd_mul_sub_one_of_even_three_dvd
EOF
```

- [x] **Step 4: Commit the milestone**

```bash
git add docs/superpowers/plans/2026-07-05-erdos699-t6-prime-power-part.md lean/Erdos699/Proved/Basic.lean notes/PROGRESS.md
git commit -m "feat: prove erdos699 t6 prime power part"
```
