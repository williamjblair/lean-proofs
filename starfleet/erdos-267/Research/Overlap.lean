import Research.Lcm

/-!
# Concrete local consequences of the Fibonacci lcm overlap budget
-/

namespace Research

open scoped BigOperators

/-- A local bound on the cost of each new denominator implies the cumulative
index-overlap budget.  The first step follows just from strict monotonicity and
`e 0 = 1`. -/
theorem overlap_budget_of_local
    (n e : ℕ → ℕ) (hmono : StrictMono n) (he0 : e 0 = 1)
    (hlocal : ∀ k, 0 < k → 2 * n k + 2 ≤ n (k + 1) + e k) :
    ∀ N,
      (∑ k ∈ Finset.range N, n k) + 2 * N ≤
        n N + ∑ k ∈ Finset.range N, e k := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      by_cases hN : N = 0
      · subst N
        have hm := hmono (show 0 < 1 by omega)
        simp [he0] at ih ⊢
        omega
      · have hl := hlocal N (Nat.pos_of_ne_zero hN)
        omega

/-- Local reusable-divisor overlap is enough for irrationality. -/
theorem irrational_reciprocal_fib_of_local_overlap
    (n e : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hepos : ∀ k, 0 < e k) (he0 : e 0 = 1)
    (hediv : ∀ k, e k ∣ n k)
    (heprev : ∀ k, 0 < k → ∃ i < k, e k ∣ n i)
    (hlocal : ∀ k, 0 < k → 2 * n k + 2 ≤ n (k + 1) + e k) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  exact irrational_reciprocal_fib_of_overlap_budget n e hpos hmono
    hepos he0 hediv heprev (overlap_budget_of_local n e hmono he0 hlocal)

/-- The divisor shared with the immediately preceding selected index. -/
def consecutiveIndexGcd (n : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => Nat.gcd (n (k + 1)) (n k)

/-- A concrete consecutive-gcd condition implies irrationality. -/
theorem irrational_reciprocal_fib_of_consecutive_gcd_overlap
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (hlocal : ∀ k,
      2 * n (k + 1) + 2 ≤
        n (k + 2) + Nat.gcd (n (k + 1)) (n k)) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  let e := consecutiveIndexGcd n
  apply irrational_reciprocal_fib_of_local_overlap n e hpos hmono
  · intro k
    cases k with
    | zero => simp [e, consecutiveIndexGcd]
    | succ k =>
        exact Nat.gcd_pos_of_pos_left _ (hpos (k + 1))
  · simp [e, consecutiveIndexGcd]
  · intro k
    cases k with
    | zero => simp [e, consecutiveIndexGcd]
    | succ k =>
        exact Nat.gcd_dvd_left (n (k + 1)) (n k)
  · intro k hk
    cases k with
    | zero => simp at hk
    | succ k =>
        refine ⟨k, Nat.lt_succ_self k, ?_⟩
        exact Nat.gcd_dvd_right (n (k + 1)) (n k)
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simpa [e, consecutiveIndexGcd, Nat.add_assoc] using hlocal j

/-- Irrationality of a shifted reciprocal-Fibonacci tail implies irrationality
of the full series; the deleted prefix is rational. -/
theorem irrational_reciprocal_fib_of_shift
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n) (K : ℕ)
    (htail : Irrational
      (∑' k : ℕ, (Nat.fib (n (K + k)) : ℝ)⁻¹)) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  let q : ℚ := ∑ k ∈ Finset.range K, (Nat.fib (n k) : ℚ)⁻¹
  have hqcast :
      (q : ℝ) = ∑ k ∈ Finset.range K, (Nat.fib (n k) : ℝ)⁻¹ := by
    simp [q]
  have hsum := (summable_and_tsum_shift_le n hpos hmono 0).1
  have hsplit := hsum.sum_add_tsum_nat_add K
  have heq :
      (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) =
        (q : ℝ) + ∑' k : ℕ, (Nat.fib (n (K + k)) : ℝ)⁻¹ := by
    rw [hqcast]
    symm
    simpa [add_comm] using hsplit
  rw [heq]
  exact htail.ratCast_add q

/-- It is enough that the consecutive-gcd overlap condition hold eventually. -/
theorem irrational_reciprocal_fib_of_eventual_consecutive_gcd_overlap
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K : ℕ)
    (hlocal : ∀ k,
      2 * n (K + k + 1) + 2 ≤
        n (K + k + 2) + Nat.gcd (n (K + k + 1)) (n (K + k))) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  let m : ℕ → ℕ := fun k => n (K + k)
  have hmpos : ∀ k, 0 < m k := fun k => hpos (K + k)
  have hmmono : StrictMono m := hmono.comp add_right_strictMono
  have hmtail := irrational_reciprocal_fib_of_consecutive_gcd_overlap
    m hmpos hmmono (by
      intro k
      simpa [m, Nat.add_assoc] using hlocal k)
  exact irrational_reciprocal_fib_of_shift n hpos hmono K (by simpa [m] using hmtail)

end Research
