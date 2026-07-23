import Research.CanonicalIncidence

namespace Erdos796

/-- Greatest prime divisor, with the harmless default `1` at `d≤1`. -/
noncomputable def greatestPrimeFactor (d : ℕ) : ℕ := by
  classical
  exact if h : 1 < d then
    d.primeFactors.max' (by
      rcases Nat.exists_prime_and_dvd (show d ≠ 1 by omega) with ⟨p, hp, hpd⟩
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩⟩)
  else 1

/-- Cofactor left after removing the greatest prime divisor. -/
noncomputable def greatestPrimeCofactor (d : ℕ) : ℕ :=
  d / greatestPrimeFactor d

lemma greatestPrimeFactor_mem {d : ℕ} (hd : 1 < d) :
    greatestPrimeFactor d ∈ d.primeFactors := by
  classical
  unfold greatestPrimeFactor
  rw [dif_pos hd]
  exact Finset.max'_mem _ _

lemma greatestPrimeFactor_prime {d : ℕ} (hd : 1 < d) :
    (greatestPrimeFactor d).Prime :=
  Nat.prime_of_mem_primeFactors (greatestPrimeFactor_mem hd)

lemma greatestPrimeFactor_dvd {d : ℕ} (hd : 1 < d) :
    greatestPrimeFactor d ∣ d :=
  Nat.dvd_of_mem_primeFactors (greatestPrimeFactor_mem hd)

lemma prime_dvd_le_greatestPrimeFactor {d p : ℕ} (hd : 1 < d)
    (hp : p.Prime) (hpd : p ∣ d) :
    p ≤ greatestPrimeFactor d := by
  classical
  unfold greatestPrimeFactor
  rw [dif_pos hd]
  apply Finset.le_max'
  exact Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩

lemma greatestPrimeFactor_mul_cofactor {d : ℕ} (hd : 1 < d) :
    greatestPrimeFactor d * greatestPrimeCofactor d = d := by
  unfold greatestPrimeCofactor
  exact Nat.mul_div_cancel' (greatestPrimeFactor_dvd hd)

lemma greatestPrimeCofactor_mul_factor {d : ℕ} (hd : 1 < d) :
    greatestPrimeCofactor d * greatestPrimeFactor d = d := by
  rw [Nat.mul_comm]
  exact greatestPrimeFactor_mul_cofactor hd

lemma greatestPrimeCofactor_pos {d : ℕ} (hd : 1 < d) :
    0 < greatestPrimeCofactor d := by
  have hp := (greatestPrimeFactor_prime hd).pos
  have hmul := greatestPrimeFactor_mul_cofactor hd
  by_contra h
  have : greatestPrimeCofactor d = 0 := by omega
  rw [this] at hmul
  simp at hmul
  omega

/-- The greatest-prime/cofactor encoding is injective on integers above one. -/
theorem greatestPrimeEncoding_injective {Δ : Type*}
    (value : Δ → ℕ) (hvalue : Function.Injective value)
    (hgt : ∀ z, 1 < value z) :
    Function.Injective (fun z =>
      (greatestPrimeCofactor (value z), greatestPrimeFactor (value z))) := by
  intro z w hzw
  apply hvalue
  have hp := congrArg (fun e : ℕ × ℕ => e.1 * e.2) hzw
  simpa [greatestPrimeCofactor_mul_factor (hgt z),
    greatestPrimeCofactor_mul_factor (hgt w)] using hp

/-- If the greatest prime divisor is at most `S`, every prime divisor is. -/
theorem all_primeFactors_le_of_greatest_le {d S : ℕ} (hd : 1 < d)
    (hmax : greatestPrimeFactor d ≤ S) :
    ∀ p, p.Prime → p ∣ d → p ≤ S := by
  intro p hp hpd
  exact (prime_dvd_le_greatestPrimeFactor hd hp hpd).trans hmax

/-- A tail core whose chosen greatest prime is below the tail cutoff has a
large cofactor. -/
theorem cutoff_lt_cofactor_mul_factor {d R : ℕ} (hd : 1 < d)
    (hR : R < d) :
    R < greatestPrimeCofactor d * greatestPrimeFactor d := by
  simpa [greatestPrimeCofactor_mul_factor hd] using hR

end Erdos796
