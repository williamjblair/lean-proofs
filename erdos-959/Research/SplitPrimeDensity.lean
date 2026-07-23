import PrimeNumberTheoremAnd.Consequences
import Research.FiniteExtremal

noncomputable section
open Filter Asymptotics
namespace Erdos959

/-- Split rational primes up to `n`. -/
def splitPrimesLE (n : ℕ) : Finset ℕ :=
  (Finset.Iic n).filter fun p => p.Prime ∧ p % 4 = 1

lemma mem_splitPrimesLE {n p : ℕ} :
    p ∈ splitPrimesLE n ↔ p ≤ n ∧ p.Prime ∧ p % 4 = 1 := by
  simp [splitPrimesLE, and_assoc]

lemma splitPrimeChebyshev_eq (n : ℕ) :
    (∑ p ∈ (Finset.Iic n).filter Nat.Prime,
      if p % 4 = 1 then Real.log p else 0) =
      ∑ p ∈ splitPrimesLE n, Real.log p := by
  classical
  simp only [splitPrimesLE, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_Iic] at hp
  by_cases hprime : p.Prime <;> by_cases hmod : p % 4 = 1 <;>
    simp [hprime, hmod]

/-- Quantitative consequence of the formally proved PNT in the progression
`1 mod 4`: eventually its Chebyshev sum is at least `x/4`. -/
theorem eventually_splitPrimeChebyshev_lower :
    ∀ᶠ x : ℝ in atTop,
      x / 4 ≤ ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        if p % 4 = 1 then Real.log p else 0 := by
  let f : ℝ → ℝ := fun x =>
    ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
      if p % 4 = 1 then Real.log p else 0
  let g : ℝ → ℝ := fun x => x / (4 : ℕ).totient
  have hequiv : f ~[atTop] g := by
    simpa [f, g] using
      (chebyshev_asymptotic_pnt (q := 4) (a := 1) (by norm_num) (by norm_num) (by norm_num))
  have hgz : ∀ᶠ x : ℝ in atTop, g x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    dsimp [g]
    positivity
  have htend : Tendsto (f / g) atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hgz).mp hequiv
  have hclose : ∀ᶠ x : ℝ in atTop, dist ((f / g) x) 1 < 1 / 2 :=
    htend.eventually (Metric.ball_mem_nhds 1 (by norm_num))
  filter_upwards [hclose, eventually_gt_atTop 0] with x hxclose hx
  have htot : Nat.totient 4 = 2 := by decide
  have hg : g x = x / 2 := by simp [g, htot]
  have hgpos : 0 < g x := by rw [hg]; positivity
  have habs : |f x / g x - 1| < 1 / 2 := by
    simpa [Pi.div_apply, Real.dist_eq] using hxclose
  rw [abs_lt] at habs
  have : x / 4 ≤ f x := by
    rw [hg] at hgpos habs
    have hxne : x / 2 ≠ 0 := ne_of_gt hgpos
    field_simp at habs
    nlinarith
  exact this

/-- In particular, eventually the number of split primes up to `n`, multiplied
by `log n`, is at least `n/4`. -/
theorem eventually_splitPrimes_card_mul_log_lower :
    ∃ N : ℕ, ∀ n ≥ N,
      (n : ℝ) / 4 ≤ (splitPrimesLE n).card * Real.log n := by
  obtain ⟨X, hX⟩ := (eventually_atTop.1 eventually_splitPrimeChebyshev_lower)
  let N := max 2 ⌈X⌉₊
  refine ⟨N, fun n hn => ?_⟩
  have hnX : X ≤ (n : ℝ) := by
    have hceil : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    exact hceil.trans (by exact_mod_cast (le_trans (le_max_right 2 ⌈X⌉₊) hn))
  have hlower := hX n hnX
  rw [Nat.floor_natCast, splitPrimeChebyshev_eq] at hlower
  have hn2 : 2 ≤ n := le_trans (le_max_left 2 ⌈X⌉₊) hn
  have hsumUpper : (∑ p ∈ splitPrimesLE n, Real.log p) ≤
      (splitPrimesLE n).card * Real.log n := by
    calc
      (∑ p ∈ splitPrimesLE n, Real.log p) ≤
          ∑ _p ∈ splitPrimesLE n, Real.log n := by
        apply Finset.sum_le_sum
        intro p hp
        have hm := mem_splitPrimesLE.mp hp
        exact Real.strictMonoOn_log.monotoneOn
          (show 0 < (p : ℝ) by exact_mod_cast hm.2.1.pos)
          (show 0 < (n : ℝ) by exact_mod_cast (by omega : 0 < n))
          (by exact_mod_cast hm.1)
      _ = (splitPrimesLE n).card * Real.log n := by
        rw [Finset.sum_const]
        simp
  exact hlower.trans hsumUpper

end Erdos959
