import Research.RademacherBallotExact
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance sharpBallotDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma evenCentralMass_sq_upper (k : ℕ) :
    (2 * k + 1 : ℝ) * evenCentralMass k ^ 2 ≤ 1 := by
  induction k with
  | zero => norm_num [evenCentralMass, Nat.centralBinom]
  | succ k ih =>
      rw [evenCentralMass_succ]
      have hk : (0 : ℝ) < k + 1 := by positivity
      rw [show (2 * ((k + 1 : ℕ) : ℝ) + 1) = 2 * ((k : ℝ) + 1) + 1 by push_cast; ring]
      calc
        (2 * (↑k + 1) + 1) *
            (evenCentralMass k * ((2 * (k : ℝ) + 1) / (2 * (k + 1)))) ^ 2 ≤
          (2 * k + 1) * evenCentralMass k ^ 2 := by
            have hfac : (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 1) ≤
                (2 * (k + 1)) ^ 2 := by nlinarith
            have he : 0 ≤ evenCentralMass k ^ 2 := sq_nonneg _
            field_simp
            nlinarith
        _ ≤ 1 := ih

lemma ballotMass_sq_upper_sharp (n : ℕ) :
    ballotMass n ^ 2 ≤ 1 / (n + 1 : ℝ) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [ballotMass_even]
    rw [show (((2 * k : ℕ) : ℝ) + 1) = 2 * (k : ℝ) + 1 by push_cast; ring]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 * k + 1))).2
    have h := evenCentralMass_sq_upper k
    nlinarith
  · have hodd : ballotMass (2 * k + 1) = evenCentralMass (k + 1) := by
      rw [ballotMass_odd, evenCentralMass_succ]
    rw [hodd]
    rw [show (((2 * k + 1 : ℕ) : ℝ) + 1) = 2 * (k : ℝ) + 2 by push_cast; ring]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 * k + 2))).2
    have h := evenCentralMass_sq_upper (k + 1)
    push_cast at h
    nlinarith [sq_nonneg (evenCentralMass (k + 1))]

lemma ballotMass_sq_lower_sharp (n : ℕ) :
    1 / (2 * (n + 1 : ℝ)) ≤ ballotMass n ^ 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [ballotMass_even]
    by_cases hk : k = 0
    · subst k
      norm_num [evenCentralMass, Nat.centralBinom]
    · have h := evenCentralMass_sq_lower (Nat.one_le_iff_ne_zero.mpr hk)
      calc
        1 / (2 * ((2 * k : ℕ) + 1 : ℝ)) ≤ 1 / (4 * (k : ℝ)) := by
          have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
          apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((2 * k : ℕ) + 1))
            (by positivity : (0 : ℝ) < 4 * k)).2
          push_cast
          nlinarith
        _ ≤ evenCentralMass k ^ 2 := h
  · have hodd : ballotMass (2 * k + 1) = evenCentralMass (k + 1) := by
      rw [ballotMass_odd, evenCentralMass_succ]
    rw [hodd]
    have h := evenCentralMass_sq_lower (show 1 ≤ k + 1 by omega)
    convert h using 1 <;> push_cast <;> field_simp <;> ring

/-- Restrict a meander's down-step set to its first `s` steps. -/
def meanderPrefix {s r : ℕ} (D : MeanderPath (s + r)) : MeanderPath s :=
  ⟨Finset.univ.filter (fun i ↦ Fin.castAdd r i ∈ D.1), by
    intro t ht
    have hfull := D.property t (ht.trans (by omega : s ≤ s + r))
    unfold downPrefix at hfull ⊢
    have heq :
        ((Finset.univ.filter (fun i : Fin s ↦ Fin.castAdd r i ∈ D.1)) ∩ pathPrefix s t).card =
          (D.1 ∩ pathPrefix (s + r) t).card := by
      apply Finset.card_bij (fun i hi ↦ Fin.castAdd r i)
      · intro i hi
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
          mem_pathPrefix] at hi ⊢
        exact hi
      · intro i₁ hi₁ i₂ hi₂ h
        exact Fin.castAdd_injective s r h
      · intro j hj
        simp only [Finset.mem_inter, mem_pathPrefix] at hj
        have hjs : j.val < s := lt_of_lt_of_le hj.2 ht
        let i : Fin s := ⟨j.val, hjs⟩
        refine ⟨i, ?_, Fin.ext rfl⟩
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
          mem_pathPrefix]
        exact hj
    rw [heq]
    exact hfull⟩

/-- Boolean down-step word in the final `r` positions of a meander. -/
def meanderSuffix {s r : ℕ} (D : MeanderPath (s + r)) : Fin r → Bool :=
  fun i ↦ decide (Fin.natAdd s i ∈ D.1)

lemma meanderPrefix_suffix_injective (s r : ℕ) :
    Function.Injective (fun D : MeanderPath (s + r) ↦ (meanderPrefix D, meanderSuffix D)) := by
  intro D E h
  apply Subtype.ext
  ext j
  apply Fin.addCases (motive := fun j : Fin (s + r) ↦ (j ∈ D.1 ↔ j ∈ E.1))
  · intro i
    have hp := congrArg (fun z ↦ (i ∈ z.1.1)) h
    simpa [meanderPrefix] using hp
  · intro i
    have hs := congrArg (fun z ↦ z.2 i) h
    simpa [meanderSuffix] using hs

/-- At most one good prefix per prefix-meander/terminal-word pair. -/
theorem card_meanders_suffix_mem_le (s r : ℕ) (E : Finset (Fin r → Bool)) :
    Fintype.card {D : MeanderPath (s + r) // meanderSuffix D ∈ E} ≤
      Fintype.card (MeanderPath s) * E.card := by
  let f : {D : MeanderPath (s + r) // meanderSuffix D ∈ E} →
      MeanderPath s × E := fun D ↦ (meanderPrefix D.1, ⟨meanderSuffix D.1, D.property⟩)
  have h := Fintype.card_le_of_injective f (by
    intro D E hDE
    apply Subtype.ext
    apply meanderPrefix_suffix_injective s r
    have hpref : meanderPrefix D.1 = meanderPrefix E.1 := congrArg Prod.fst hDE
    have hsuf : meanderSuffix D.1 = meanderSuffix E.1 := congrArg (fun z ↦ z.2.1) hDE
    exact Prod.ext hpref hsuf)
  simpa [Fintype.card_prod, Fintype.card_coe] using h

/-- Squared terminal absolute-continuity bound for a one-dimensional meander.  Equivalently,
the unsquared density inflation is at most `sqrt (2(s+r+1)/(s+1))`. -/
theorem meander_suffix_density_sq_le (s r : ℕ) (E : Finset (Fin r → Bool)) :
    ((Fintype.card {D : MeanderPath (s + r) // meanderSuffix D ∈ E} : ℝ) /
        Fintype.card (MeanderPath (s + r))) ^ 2 ≤
      (2 * (s + r + 1 : ℝ) / (s + 1 : ℝ)) *
        (((E.card : ℝ) / (2 : ℝ) ^ r) ^ 2) := by
  have hcardNat := card_meanders_suffix_mem_le s r E
  have hcard : (Fintype.card {D : MeanderPath (s + r) // meanderSuffix D ∈ E} : ℝ) ≤
      Fintype.card (MeanderPath s) * E.card := by exact_mod_cast hcardNat
  have hMs : (Fintype.card (MeanderPath s) : ℝ) / (2 : ℝ) ^ s = ballotMass s := by
    rw [card_meanderPath, ballotMass]
  have hMn : (Fintype.card (MeanderPath (s + r)) : ℝ) / (2 : ℝ) ^ (s + r) =
      ballotMass (s + r) := by rw [card_meanderPath, ballotMass]
  have hpos : (0 : ℝ) < ballotMass (s + r) := by
    unfold ballotMass
    exact div_pos (by exact_mod_cast Nat.choose_pos (Nat.div_le_self (s + r) 2)) (by positivity)
  have hratio : (ballotMass s / ballotMass (s + r)) ^ 2 ≤
      2 * (s + r + 1 : ℝ) / (s + 1 : ℝ) := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hpos)).2
    have hlo := ballotMass_sq_lower_sharp (s + r)
    push_cast at hlo
    have hhi := ballotMass_sq_upper_sharp s
    have hspos : (0 : ℝ) < s + 1 := by positivity
    have hfactor : 0 ≤ 2 * (s + r + 1 : ℝ) / (s + 1 : ℝ) := by positivity
    calc
      ballotMass s ^ 2 ≤ 1 / (s + 1 : ℝ) := hhi
      _ = (2 * (s + r + 1 : ℝ) / (s + 1 : ℝ)) *
          (1 / (2 * (s + r + 1 : ℝ))) := by field_simp
      _ ≤ (2 * (s + r + 1 : ℝ) / (s + 1 : ℝ)) * ballotMass (s + r) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hlo hfactor
  have hden : (0 : ℝ) < Fintype.card (MeanderPath (s + r)) := by
    rw [card_meanderPath]
    exact_mod_cast Nat.choose_pos (Nat.div_le_self (s + r) 2)
  have hdensity :
      (Fintype.card {D : MeanderPath (s + r) // meanderSuffix D ∈ E} : ℝ) /
          Fintype.card (MeanderPath (s + r)) ≤
        (ballotMass s / ballotMass (s + r)) * ((E.card : ℝ) / (2 : ℝ) ^ r) := by
    apply (div_le_iff₀ hden).2
    calc
      (Fintype.card {D : MeanderPath (s + r) // meanderSuffix D ∈ E} : ℝ) ≤
          Fintype.card (MeanderPath s) * E.card := hcard
      _ = ((ballotMass s / ballotMass (s + r)) * ((E.card : ℝ) / (2 : ℝ) ^ r)) *
          Fintype.card (MeanderPath (s + r)) := by
        rw [← hMs, ← hMn, pow_add]
        field_simp
  have hleft0 : 0 ≤
      (Fintype.card {D : MeanderPath (s + r) // meanderSuffix D ∈ E} : ℝ) /
        Fintype.card (MeanderPath (s + r)) := by positivity
  have hright0 : 0 ≤
      (ballotMass s / ballotMass (s + r)) * ((E.card : ℝ) / (2 : ℝ) ^ r) := by
    exact mul_nonneg (div_nonneg (ballotMass_nonneg s) hpos.le) (by positivity)
  calc
    _ ≤ ((ballotMass s / ballotMass (s + r)) *
        ((E.card : ℝ) / (2 : ℝ) ^ r)) ^ 2 := (sq_le_sq₀ hleft0 hright0).2 hdensity
    _ = (ballotMass s / ballotMass (s + r)) ^ 2 *
        (((E.card : ℝ) / (2 : ℝ) ^ r) ^ 2) := by ring
    _ ≤ (2 * (s + r + 1 : ℝ) / (s + 1 : ℝ)) *
        (((E.card : ℝ) / (2 : ℝ) ^ r) ^ 2) := by gcongr

end Erdos521
