import Research.AxisCountExact
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance coneSuffixDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- An unconstrained schedule/sign word of paired-step length `r`. -/
abbrev AxisWord (r : ℕ) := (Fin r → Bool) × (Fin r → Bool)

/-- Restriction of an axis path to its first `s` steps. -/
def axisPrefix {s r : ℕ} (p : AxisGoodPath (s + r)) :
    Finset (Fin s) × (Fin s → Bool) :=
  (Finset.univ.filter (fun i ↦ Fin.castAdd r i ∈ p.1.1),
    fun i ↦ p.1.2 (Fin.castAdd r i))

/-- The unconstrained final `r` steps of an axis path. -/
def axisSuffix {s r : ℕ} (p : AxisGoodPath (s + r)) : AxisWord r :=
  (fun i ↦ decide (Fin.natAdd s i ∈ p.1.1),
    fun i ↦ p.1.2 (Fin.natAdd s i))

lemma finiteAxisWalk_axisPrefix {s r : ℕ} (p : AxisGoodPath (s + r)) (t : ℕ)
    (ht : t ≤ s) :
    finiteAxisWalk (axisPrefix p).1 (axisPrefix p).2 t =
      finiteAxisWalk p.1.1 p.1.2 t := by
  apply Prod.ext
  · rw [finiteAxisWalk_fst, finiteAxisWalk_fst]
    congr 1
    apply Finset.sum_bij (fun i hi ↦ Fin.castAdd r i)
    · intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨by simpa [axisPrefix] using hi.1, hi.2⟩
    · intro i₁ hi₁ i₂ hi₂ heq
      exact Fin.castAdd_injective s r heq
    · intro j hj
      have hjt : j.val < t := (Finset.mem_filter.mp hj).2
      have hjs : j.val < s := lt_of_lt_of_le hjt ht
      let i : Fin s := ⟨j.val, hjs⟩
      have hji : Fin.castAdd r i = j := Fin.ext rfl
      refine ⟨i, ?_, hji⟩
      simp only [Finset.mem_filter]
      constructor
      · simp only [axisPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hji]
        exact (Finset.mem_filter.mp hj).1
      · exact hjt
    · intro i hi
      rfl
  · rw [finiteAxisWalk_snd, finiteAxisWalk_snd]
    congr 1
    apply Finset.sum_bij (fun i hi ↦ Fin.castAdd r i)
    · intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨by simpa [axisPrefix] using hi.1, hi.2⟩
    · intro i₁ hi₁ i₂ hi₂ heq
      exact Fin.castAdd_injective s r heq
    · intro j hj
      have hjt : j.val < t := (Finset.mem_filter.mp hj).2
      have hjs : j.val < s := lt_of_lt_of_le hjt ht
      let i : Fin s := ⟨j.val, hjs⟩
      have hji : Fin.castAdd r i = j := Fin.ext rfl
      refine ⟨i, ?_, hji⟩
      simp only [Finset.mem_filter]
      constructor
      · simp only [Finset.mem_compl, axisPrefix, Finset.mem_filter, Finset.mem_univ,
          true_and, not_iff_not]
        rw [hji]
        exact Finset.mem_compl.mp (Finset.mem_filter.mp hj).1
      · exact hjt
    · intro i hi
      rfl

/-- Prefixes of good axis paths remain good. -/
def axisGoodPrefix {s r : ℕ} (p : AxisGoodPath (s + r)) : AxisGoodPath s :=
  ⟨axisPrefix p, by
    apply axisGood_of_finiteAxisWalk_nonneg
    intro t ht
    rw [finiteAxisWalk_axisPrefix p t ht]
    exact p.property.finiteAxisWalk_nonneg t⟩

lemma axisGoodPrefix_suffix_injective (s r : ℕ) :
    Function.Injective (fun p : AxisGoodPath (s + r) ↦ (axisGoodPrefix p, axisSuffix p)) := by
  intro p q heq
  apply Subtype.ext
  apply Prod.ext
  · ext j
    apply Fin.addCases (motive := fun j : Fin (s + r) ↦ (j ∈ p.1.1 ↔ j ∈ q.1.1))
    · intro i
      have hp := congrArg (fun z ↦ (i ∈ z.1.1.1)) heq
      simpa [axisGoodPrefix, axisPrefix] using hp
    · intro i
      have hs := congrArg (fun z ↦ z.2.1 i) heq
      simpa [axisSuffix] using hs
  · funext j
    apply Fin.addCases (motive := fun j : Fin (s + r) ↦ p.1.2 j = q.1.2 j)
    · intro i
      have hp := congrArg (fun z ↦ z.1.1.2 i) heq
      simpa [axisGoodPrefix, axisPrefix] using hp
    · intro i
      have hs := congrArg (fun z ↦ z.2.2 i) heq
      simpa [axisSuffix] using hs

lemma card_axisWord (r : ℕ) : Fintype.card (AxisWord r) = 4 ^ r := by
  simp [AxisWord, Fintype.card_fun]
  rw [← mul_pow]
  norm_num

lemma card_axisGoodPath_even_to_odd (m : ℕ) :
    (m + 1) * Fintype.card (AxisGoodPath (2 * m + 1)) =
      2 * (2 * m + 1) * Fintype.card (AxisGoodPath (2 * m)) := by
  rw [card_axisGoodPath_even, card_axisGoodPath_odd]
  have h := Nat.choose_mul_succ_eq (2 * m) m
  have h' : Nat.choose (2 * m) m * (2 * m + 1) =
      Nat.choose (2 * m + 1) m * (m + 1) := by
    simpa only [show 2 * m + 1 - m = m + 1 by omega] using h
  calc
    (m + 1) * (2 * Nat.choose (2 * m + 1) m ^ 2) =
        2 * Nat.choose (2 * m + 1) m *
          (Nat.choose (2 * m + 1) m * (m + 1)) := by ring
    _ = 2 * Nat.choose (2 * m + 1) m *
          (Nat.choose (2 * m) m * (2 * m + 1)) := by rw [← h']
    _ = 2 * (2 * m + 1) *
          (Nat.choose (2 * m) m * Nat.choose (2 * m + 1) m) := by ring

lemma card_axisGoodPath_odd_to_even (m : ℕ) :
    (2 * m + 4) * Fintype.card (AxisGoodPath (2 * m + 2)) =
      4 * (2 * m + 3) * Fintype.card (AxisGoodPath (2 * m + 1)) := by
  rw [show 2 * m + 2 = 2 * (m + 1) by omega, card_axisGoodPath_even,
    card_axisGoodPath_odd]
  let D := Nat.choose (2 * m + 1) m
  let C := Nat.choose (2 * m + 2) (m + 1)
  let E := Nat.choose (2 * m + 3) (m + 1)
  have hsym : Nat.choose (2 * m + 1) (m + 1) = D := by
    dsimp [D]
    calc
      Nat.choose (2 * m + 1) (m + 1) =
          Nat.choose (2 * m + 1) (2 * m + 1 - m) := by congr 1; omega
      _ = Nat.choose (2 * m + 1) m := Nat.choose_symm (by omega)
  have hC : C = 2 * D := by
    calc
      C = Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) (m + 1) := by
        dsimp [C]
        simpa only [show 2 * m + 2 = (2 * m + 1) + 1 by omega] using
          Nat.choose_succ_succ' (2 * m + 1) m
      _ = D + D := by rw [hsym]
      _ = 2 * D := by ring
  have hmul := Nat.choose_mul_succ_eq (2 * m + 2) (m + 1)
  have hE : C * (2 * m + 3) = E * (m + 2) := by
    dsimp [C, E]
    simpa only [show 2 * m + 2 + 1 = 2 * m + 3 by omega,
      show 2 * m + 3 - (m + 1) = m + 2 by omega] using hmul
  change (2 * m + 4) * (C * E) = 4 * (2 * m + 3) * (2 * D ^ 2)
  calc
    (2 * m + 4) * (C * E) = 2 * C * (E * (m + 2)) := by ring
    _ = 2 * C * (C * (2 * m + 3)) := by rw [← hE]
    _ = 4 * (2 * m + 3) * (2 * D ^ 2) := by rw [hC]; ring

/-- Quadrant-survival mass among all unconstrained paired-step words. -/
noncomputable def axisGoodMass (n : ℕ) : ℝ :=
  (Fintype.card (AxisGoodPath n) : ℝ) / (4 : ℝ) ^ n

lemma axisGoodMass_even_to_odd (m : ℕ) :
    (2 * m + 2 : ℝ) * axisGoodMass (2 * m + 1) =
      (2 * m + 1 : ℝ) * axisGoodMass (2 * m) := by
  have hnat := card_axisGoodPath_even_to_odd m
  have hreal : (m + 1 : ℝ) * Fintype.card (AxisGoodPath (2 * m + 1)) =
      2 * (2 * m + 1 : ℝ) * Fintype.card (AxisGoodPath (2 * m)) := by
    exact_mod_cast hnat
  unfold axisGoodMass
  rw [show (4 : ℝ) ^ (2 * m + 1) = (4 : ℝ) ^ (2 * m) * 4 by
    rw [show 2 * m + 1 = (2 * m).succ by omega, pow_succ]]
  have hp : (0 : ℝ) < 4 ^ (2 * m) := by positivity
  field_simp
  nlinarith

lemma axisGoodMass_odd_to_even (m : ℕ) :
    (2 * m + 4 : ℝ) * axisGoodMass (2 * m + 2) =
      (2 * m + 3 : ℝ) * axisGoodMass (2 * m + 1) := by
  have hnat := card_axisGoodPath_odd_to_even m
  have hreal : (2 * m + 4 : ℝ) * Fintype.card (AxisGoodPath (2 * m + 2)) =
      4 * (2 * m + 3 : ℝ) * Fintype.card (AxisGoodPath (2 * m + 1)) := by
    exact_mod_cast hnat
  unfold axisGoodMass
  rw [show (4 : ℝ) ^ (2 * m + 2) = (4 : ℝ) ^ (2 * m + 1) * 4 by
    rw [show 2 * m + 2 = (2 * m + 1).succ by omega, pow_succ]]
  have hp : (0 : ℝ) < 4 ^ (2 * m + 1) := by positivity
  field_simp
  nlinarith

lemma axisGoodMass_nonneg (n : ℕ) : 0 ≤ axisGoodMass n := by
  unfold axisGoodMass
  positivity

lemma scaled_axisGoodMass_mono :
    Monotone (fun n : ℕ ↦ (n + 1 : ℝ) * axisGoodMass n) := by
  apply monotone_nat_of_le_succ
  intro n
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hrec := axisGoodMass_even_to_odd m
    push_cast at *
    nlinarith
  · have hrec := axisGoodMass_odd_to_even m
    have hnonneg := axisGoodMass_nonneg (2 * m + 1)
    push_cast at *
    nlinarith

lemma axisGoodMass_scaled_le {s n : ℕ} (hsn : s ≤ n) :
    (s + 1 : ℝ) * axisGoodMass s ≤ (n + 1 : ℝ) * axisGoodMass n :=
  scaled_axisGoodMass_mono hsn

lemma card_axisGoodPath_pos (n : ℕ) : 0 < Fintype.card (AxisGoodPath n) := by
  rw [Fintype.card_pos_iff]
  let H : Finset (Fin n) := Finset.univ
  let S : Fin n → Bool := fun _ ↦ true
  refine ⟨⟨(H, S), ?_⟩⟩
  apply axisGood_of_finiteAxisWalk_nonneg
  intro t ht
  simp [finiteAxisWalk_fst, finiteAxisWalk_snd, H, S, sign]

lemma card_axisGoodPath_scaled_le (s r : ℕ) :
    (s + 1 : ℝ) * (4 : ℝ) ^ r * Fintype.card (AxisGoodPath s) ≤
      (s + r + 1 : ℝ) * Fintype.card (AxisGoodPath (s + r)) := by
  have h := axisGoodMass_scaled_le (show s ≤ s + r by omega)
  have hp : 0 ≤ (4 : ℝ) ^ (s + r) := by positivity
  have hm := mul_le_mul_of_nonneg_right h hp
  unfold axisGoodMass at hm
  rw [pow_add] at hm
  convert hm using 1 <;> push_cast
  · rfl
  · field_simp
  · field_simp

/-- Any prescribed family of terminal words has at most `A_s` good prefixes per word. -/
theorem card_goodPaths_suffix_mem_le (s r : ℕ) (E : Finset (AxisWord r)) :
    Fintype.card {p : AxisGoodPath (s + r) // axisSuffix p ∈ E} ≤
      Fintype.card (AxisGoodPath s) * E.card := by
  let f : {p : AxisGoodPath (s + r) // axisSuffix p ∈ E} →
      AxisGoodPath s × E := fun p ↦
    (axisGoodPrefix p.1, ⟨axisSuffix p.1, p.property⟩)
  have hcard := Fintype.card_le_of_injective f (by
    intro p q h
    apply Subtype.ext
    apply axisGoodPrefix_suffix_injective s r
    have hpref : axisGoodPrefix p.1 = axisGoodPrefix q.1 := congrArg Prod.fst h
    have hsuf : axisSuffix p.1 = axisSuffix q.1 := congrArg (fun z ↦ z.2.1) h
    exact Prod.ext hpref hsuf)
  simpa [Fintype.card_prod, Fintype.card_coe] using hcard

/-- A terminal event under quadrant survival has density at most `(s+r+1)/(s+1)`
relative to the uniform law on its `r` terminal paired steps. -/
theorem goodPaths_suffix_density_le (s r : ℕ) (E : Finset (AxisWord r)) :
    (Fintype.card {p : AxisGoodPath (s + r) // axisSuffix p ∈ E} : ℝ) /
        Fintype.card (AxisGoodPath (s + r)) ≤
      ((s + r + 1 : ℝ) / (s + 1 : ℝ)) * (E.card : ℝ) / (4 : ℝ) ^ r := by
  have hcardNat := card_goodPaths_suffix_mem_le s r E
  have hcard : (Fintype.card {p : AxisGoodPath (s + r) // axisSuffix p ∈ E} : ℝ) ≤
      Fintype.card (AxisGoodPath s) * E.card := by
    exact_mod_cast hcardNat
  have hfac : 0 ≤ (s + 1 : ℝ) * (4 : ℝ) ^ r := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcard hfac
  have hscale := card_axisGoodPath_scaled_le s r
  have hscaleE := mul_le_mul_of_nonneg_right hscale (show (0 : ℝ) ≤ E.card by positivity)
  have hcross :
      ((s + 1 : ℝ) * (4 : ℝ) ^ r) *
          Fintype.card {p : AxisGoodPath (s + r) // axisSuffix p ∈ E} ≤
        ((s + r + 1 : ℝ) * Fintype.card (AxisGoodPath (s + r))) * E.card := by
    calc
      _ ≤ ((s + 1 : ℝ) * (4 : ℝ) ^ r) *
          (Fintype.card (AxisGoodPath s) * E.card) := hmul
      _ = (((s + 1 : ℝ) * (4 : ℝ) ^ r) *
          Fintype.card (AxisGoodPath s)) * E.card := by ring
      _ ≤ ((s + r + 1 : ℝ) * Fintype.card (AxisGoodPath (s + r))) * E.card := hscaleE
  have hAn : (0 : ℝ) < Fintype.card (AxisGoodPath (s + r)) := by
    exact_mod_cast card_axisGoodPath_pos (s + r)
  apply (div_le_iff₀ hAn).2
  have hden : (0 : ℝ) < (s + 1 : ℝ) * (4 : ℝ) ^ r := by positivity
  calc
    (Fintype.card {p : AxisGoodPath (s + r) // axisSuffix p ∈ E} : ℝ) ≤
        (((s + r + 1 : ℝ) * Fintype.card (AxisGoodPath (s + r))) * E.card) /
          ((s + 1 : ℝ) * (4 : ℝ) ^ r) := (le_div_iff₀ hden).2 (by
            simpa [mul_comm] using hcross)
    _ = (((s + r + 1 : ℝ) / (s + 1 : ℝ)) * (E.card : ℝ) / (4 : ℝ) ^ r) *
        Fintype.card (AxisGoodPath (s + r)) := by field_simp

end Erdos521
