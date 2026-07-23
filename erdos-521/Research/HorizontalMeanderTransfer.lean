import Research.SharpBallotTerminal
import Research.ConeSuffixDensity
import Mathlib.Data.Finset.Slice
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance horizontalMeanderDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Axis schedule/sign paths for which only the horizontal compressed coordinate is a meander. -/
abbrev HorizontalGoodPath (n : ℕ) :=
  {p : Finset (Fin n) × (Fin n → Bool) //
    IsMeander (scheduleDownEquiv p.1 p.2).1}

/-- At fixed schedule, horizontal-good signs split into one meander and an unconstrained vertical
sign word. -/
noncomputable def horizontalGoodSignsEquiv {n : ℕ} (H : Finset (Fin n)) :
    {S : Fin n → Bool // IsMeander (scheduleDownEquiv H S).1} ≃
      MeanderPath H.card × Finset (Fin (Hᶜ).card) where
  toFun S := (⟨(scheduleDownEquiv H S.1).1, S.property⟩,
    (scheduleDownEquiv H S.1).2)
  invFun D := ⟨(scheduleDownEquiv H).symm (D.1.1, D.2), by
    rw [(scheduleDownEquiv H).apply_symm_apply]
    exact D.1.property⟩
  left_inv S := by
    apply Subtype.ext
    exact (scheduleDownEquiv H).symm_apply_apply S.1
  right_inv D := by
    have hz := (scheduleDownEquiv H).apply_symm_apply (D.1.1, D.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hz
    · change ((scheduleDownEquiv H) ((scheduleDownEquiv H).symm (D.1.1, D.2))).2 = D.2
      exact congrArg Prod.snd hz

lemma card_horizontalGoodSigns {n : ℕ} (H : Finset (Fin n)) :
    Fintype.card {S : Fin n → Bool // IsMeander (scheduleDownEquiv H S).1} =
      Nat.choose H.card (H.card / 2) * 2 ^ (Hᶜ).card := by
  rw [Fintype.card_congr (horizontalGoodSignsEquiv H), Fintype.card_prod,
    card_meanderPath]
  simp

/-- Separate a horizontal-good path into its schedule and constrained sign assignment. -/
def horizontalGoodEquivSigma (n : ℕ) :
    HorizontalGoodPath n ≃
      Σ H : Finset (Fin n),
        {S : Fin n → Bool // IsMeander (scheduleDownEquiv H S).1} where
  toFun p := ⟨p.1.1, p.1.2, p.property⟩
  invFun p := ⟨(p.1, p.2.1), p.2.property⟩
  left_inv p := by rfl
  right_inv p := by cases p; rfl

lemma card_horizontalGoodPath (n : ℕ) :
    Fintype.card (HorizontalGoodPath n) =
      ∑ H : Finset (Fin n),
        Nat.choose H.card (H.card / 2) * 2 ^ (Hᶜ).card := by
  rw [Fintype.card_congr (horizontalGoodEquivSigma n), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro H hH
  exact card_horizontalGoodSigns H

/-- Horizontal one-coordinate survival mass among all axis words. -/
noncomputable def horizontalGoodMass (n : ℕ) : ℝ :=
  (Fintype.card (HorizontalGoodPath n) : ℝ) / (4 : ℝ) ^ n

lemma horizontalGoodMass_eq_average_ballot (n : ℕ) :
    horizontalGoodMass n =
      (∑ H : Finset (Fin n), ballotMass H.card) / (2 : ℝ) ^ n := by
  rw [horizontalGoodMass, card_horizontalGoodPath]
  push_cast
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro H hH
  rw [ballotMass]
  have hcard := card_schedule_add_compl H
  have hp : (2 : ℝ) ^ H.card * (2 : ℝ) ^ (Hᶜ).card = (2 : ℝ) ^ n := by
    rw [← pow_add, hcard]
  rw [show (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n by
    rw [← mul_pow]; norm_num]
  rw [← hp]
  field_simp

/-- Group a sum over all finite subsets by their cardinality. -/
lemma sum_finsets_by_card_real (n : ℕ) (f : ℕ → ℝ) :
    (∑ H : Finset (Fin n), f H.card) =
      ∑ k : Fin (n + 1), (Nat.choose n k.val : ℝ) * f k.val := by
  let rank : Finset (Fin n) → Fin (n + 1) := fun H ↦
    ⟨H.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ H)⟩
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := rank) (f := fun H : Finset (Fin n) ↦ f H.card)]
  apply Finset.sum_congr rfl
  intro k hk
  have heq : (Finset.univ.filter fun H : Finset (Fin n) ↦ rank H = k) =
      Finset.powersetCard k.val Finset.univ := by
    ext H
    simp [rank, Fin.ext_iff]
  rw [heq]
  calc
    (∑ H ∈ Finset.powersetCard k.val Finset.univ, f H.card) =
        Nat.choose n k.val * f k.val := by
      simpa using Finset.sum_powersetCard k.val (Finset.univ : Finset (Fin n)) f
    _ = (Nat.choose n k.val : ℝ) * f k.val := by norm_cast

lemma choose_div_succ_eq (n k : ℕ) :
    (Nat.choose n k : ℝ) / (k + 1 : ℝ) =
      (Nat.choose (n + 1) (k + 1) : ℝ) / (n + 1 : ℝ) := by
  have hnat := Nat.add_one_mul_choose_eq n k
  have hreal : (n + 1 : ℝ) * Nat.choose n k =
      Nat.choose (n + 1) (k + 1) * (k + 1 : ℝ) := by exact_mod_cast hnat
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hk : (0 : ℝ) < k + 1 := by positivity
  apply (div_eq_div_iff (ne_of_gt hk) (ne_of_gt hn)).2
  nlinarith

/-- The reciprocal-cardinality average of a uniform random subset is `O(1/n)`. -/
lemma sum_finsets_card_recip_le (n : ℕ) :
    (∑ H : Finset (Fin n), (1 : ℝ) / (H.card + 1 : ℝ)) ≤
      (2 : ℝ) ^ (n + 1) / (n + 1 : ℝ) := by
  have hgroup := sum_finsets_by_card_real n
    (fun k : ℕ ↦ (1 : ℝ) / (k + 1 : ℝ))
  change (∑ H : Finset (Fin n),
    (fun k : ℕ ↦ (1 : ℝ) / (k + 1 : ℝ)) H.card) ≤ _
  rw [hgroup]
  change (∑ k : Fin (n + 1),
    (fun j : ℕ ↦ (Nat.choose n j : ℝ) * (1 / (j + 1 : ℝ))) k.val) ≤ _
  have hfin := Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ (Nat.choose n j : ℝ) * (1 / (j + 1 : ℝ))) (n + 1)
  rw [hfin]
  have hrewrite :
      (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * (1 / (k + 1 : ℝ))) =
      (1 / (n + 1 : ℝ)) *
        ∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 1) (k + 1) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (Nat.choose n k : ℝ) * (1 / (k + 1 : ℝ)) =
        (Nat.choose n k : ℝ) / (k + 1 : ℝ) by ring,
      choose_div_succ_eq]
    ring
  rw [hrewrite]
  have htail :
      (∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 1) (k + 1) : ℝ)) ≤
        (2 : ℝ) ^ (n + 1) := by
    have hsumNat := Nat.sum_range_choose (n + 1)
    have hsum :
        (∑ k ∈ Finset.range (n + 2), (Nat.choose (n + 1) k : ℝ)) =
          (2 : ℝ) ^ (n + 1) := by exact_mod_cast hsumNat
    rw [Finset.sum_range_succ'] at hsum
    rw [← hsum]
    norm_num
  calc
    (1 / (n + 1 : ℝ)) *
        ∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 1) (k + 1) : ℝ) ≤
      (1 / (n + 1 : ℝ)) * (2 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left htail (div_nonneg (by norm_num) (by positivity))
    _ = (2 : ℝ) ^ (n + 1) / (n + 1 : ℝ) := by ring

lemma horizontalGoodMass_sq_upper (n : ℕ) :
    horizontalGoodMass n ^ 2 ≤ 2 / (n + 1 : ℝ) := by
  rw [horizontalGoodMass_eq_average_ballot]
  let S : Finset (Finset (Fin n)) := Finset.univ
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := S) (f := fun H : Finset (Fin n) ↦ ballotMass H.card)
  have hsquares :
      (∑ H : Finset (Fin n), ballotMass H.card ^ 2) ≤
        (2 : ℝ) ^ (n + 1) / (n + 1 : ℝ) := by
    calc
      _ ≤ ∑ H : Finset (Fin n), (1 : ℝ) / (H.card + 1 : ℝ) := by
        apply Finset.sum_le_sum
        intro H hH
        exact ballotMass_sq_upper_sharp H.card
      _ ≤ _ := sum_finsets_card_recip_le n
  have hcard : (S.card : ℝ) = (2 : ℝ) ^ n := by
    dsimp [S]
    rw [Fintype.card_finset, Fintype.card_fin]
    norm_num
  have hsum :
      (∑ H : Finset (Fin n), ballotMass H.card) ^ 2 ≤
        (2 : ℝ) ^ n * ((2 : ℝ) ^ (n + 1) / (n + 1 : ℝ)) := by
    rw [hcard] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_left hsquares (by positivity))
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hp)).2
  calc
    (∑ H : Finset (Fin n), ballotMass H.card) ^ 2 ≤ _ := hsum
    _ = 2 / (n + 1 : ℝ) * ((2 : ℝ) ^ n) ^ 2 := by
      rw [show (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 by rw [pow_succ]]
      field_simp

lemma ballotMass_lower_common (n : ℕ) (H : Finset (Fin n)) :
    1 / Real.sqrt (2 * (n + 1 : ℝ)) ≤ ballotMass H.card := by
  have hH : H.card ≤ n := by simpa using Finset.card_le_univ H
  have hc : 0 ≤ 1 / (2 * (n + 1 : ℝ)) := by positivity
  have hsqrt : (1 / Real.sqrt (2 * (n + 1 : ℝ))) ^ 2 =
      1 / (2 * (n + 1 : ℝ)) := by
    have hpos : (0 : ℝ) < 2 * (n + 1 : ℝ) := by positivity
    rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
  apply (sq_le_sq₀ (by positivity) (ballotMass_nonneg H.card)).1
  rw [hsqrt]
  calc
    1 / (2 * (n + 1 : ℝ)) ≤ 1 / (2 * (H.card + 1 : ℝ)) := by
      gcongr
    _ ≤ ballotMass H.card ^ 2 := ballotMass_sq_lower_sharp H.card

lemma horizontalGoodMass_sq_lower (n : ℕ) :
    1 / (2 * (n + 1 : ℝ)) ≤ horizontalGoodMass n ^ 2 := by
  rw [horizontalGoodMass_eq_average_ballot]
  let c : ℝ := 1 / Real.sqrt (2 * (n + 1 : ℝ))
  have hpoint (H : Finset (Fin n)) : c ≤ ballotMass H.card :=
    ballotMass_lower_common n H
  have hsum :
      (∑ _H : Finset (Fin n), c) ≤
        ∑ H : Finset (Fin n), ballotMass H.card :=
    Finset.sum_le_sum fun H hH ↦ hpoint H
  have hcard : (Fintype.card (Finset (Fin n)) : ℝ) = (2 : ℝ) ^ n := by
    rw [Fintype.card_finset, Fintype.card_fin]
    norm_num
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hmean : c ≤
      (∑ H : Finset (Fin n), ballotMass H.card) / (2 : ℝ) ^ n := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    push_cast at hsum
    rw [hcard] at hsum
    apply (le_div_iff₀ hp).2
    simpa [mul_comm] using hsum
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hmean0 : 0 ≤
      (∑ H : Finset (Fin n), ballotMass H.card) / (2 : ℝ) ^ n := by
    exact div_nonneg (Finset.sum_nonneg fun H hH ↦ ballotMass_nonneg H.card) (by positivity)
  have hsquare := (sq_le_sq₀ hc0 hmean0).2 hmean
  have hcSq : c ^ 2 = 1 / (2 * (n + 1 : ℝ)) := by
    dsimp [c]
    have hpos : (0 : ℝ) < 2 * (n + 1 : ℝ) := by positivity
    rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
  rw [hcSq] at hsquare
  exact hsquare

/-- Restrict a horizontal-good axis path to its first `s` global paired steps. -/
def horizontalAxisPrefix {s r : ℕ} (p : HorizontalGoodPath (s + r)) :
    Finset (Fin s) × (Fin s → Bool) :=
  (Finset.univ.filter (fun i ↦ Fin.castAdd r i ∈ p.1.1),
    fun i ↦ p.1.2 (Fin.castAdd r i))

/-- Its final `r` unconstrained axis steps. -/
def horizontalAxisSuffix {s r : ℕ} (p : HorizontalGoodPath (s + r)) : AxisWord r :=
  (fun i ↦ decide (Fin.natAdd s i ∈ p.1.1),
    fun i ↦ p.1.2 (Fin.natAdd s i))

lemma finiteAxisWalk_fst_horizontalPrefix {s r : ℕ} (p : HorizontalGoodPath (s + r))
    (t : ℕ) (ht : t ≤ s) :
    (finiteAxisWalk (horizontalAxisPrefix p).1 (horizontalAxisPrefix p).2 t).1 =
      (finiteAxisWalk p.1.1 p.1.2 t).1 := by
  rw [finiteAxisWalk_fst, finiteAxisWalk_fst]
  congr 1
  apply Finset.sum_bij (fun i hi ↦ Fin.castAdd r i)
  · intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨by simpa [horizontalAxisPrefix] using hi.1, hi.2⟩
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
    · simp only [horizontalAxisPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hji]
      exact (Finset.mem_filter.mp hj).1
    · exact hjt
  · intro i hi
    rfl

lemma horizontalGood_fst_nonneg {n : ℕ} {H : Finset (Fin n)} {S : Fin n → Bool}
    (h : IsMeander (scheduleDownEquiv H S).1) (t : ℕ) (ht : t ≤ n) :
    0 ≤ (finiteAxisWalk H S t).1 := by
  let q := (H.filter (fun x ↦ x.val < t)).card
  have hq : q ≤ H.card := Finset.card_filter_le _ _
  have hm := h q hq
  rw [scheduleDownEquiv_fst_eq, downPrefix_compressedDown] at hm
  rw [finiteAxisWalk_fst]
  have hsign := (prefix_sign_nonneg_iff_false_card
    (H.filter (fun x ↦ x.val < t)) S).2 hm
  positivity

lemma horizontalGood_of_fst_nonneg {n : ℕ} {H : Finset (Fin n)} {S : Fin n → Bool}
    (h : ∀ t ≤ n, 0 ≤ (finiteAxisWalk H S t).1) :
    IsMeander (scheduleDownEquiv H S).1 := by
  rw [scheduleDownEquiv_fst_eq]
  intro q hq
  obtain ⟨t, htle, ht⟩ := filter_before_rank_card H q hq
  have hn := h t htle
  rw [finiteAxisWalk_fst] at hn
  have hs : 0 ≤ ∑ j ∈ H.filter (fun j ↦ j.val < t), sign (S j) := by linarith
  rw [prefix_sign_nonneg_iff_false_card] at hs
  rw [← ht, downPrefix_compressedDown]
  exact hs

/-- Prefixes of horizontal-good paths remain horizontal-good. -/
def horizontalGoodPrefix {s r : ℕ} (p : HorizontalGoodPath (s + r)) :
    HorizontalGoodPath s :=
  ⟨horizontalAxisPrefix p, by
    apply horizontalGood_of_fst_nonneg
    intro t ht
    rw [finiteAxisWalk_fst_horizontalPrefix p t ht]
    exact horizontalGood_fst_nonneg p.property t (ht.trans (by omega))⟩

lemma horizontalGoodPrefix_suffix_injective (s r : ℕ) :
    Function.Injective (fun p : HorizontalGoodPath (s + r) ↦
      (horizontalGoodPrefix p, horizontalAxisSuffix p)) := by
  intro p q heq
  apply Subtype.ext
  apply Prod.ext
  · ext j
    apply Fin.addCases (motive := fun j : Fin (s + r) ↦ (j ∈ p.1.1 ↔ j ∈ q.1.1))
    · intro i
      have hp := congrArg (fun z ↦ (i ∈ z.1.1.1)) heq
      simpa [horizontalGoodPrefix, horizontalAxisPrefix] using hp
    · intro i
      have hs := congrArg (fun z ↦ z.2.1 i) heq
      simpa [horizontalAxisSuffix] using hs
  · funext j
    apply Fin.addCases (motive := fun j : Fin (s + r) ↦ p.1.2 j = q.1.2 j)
    · intro i
      have hp := congrArg (fun z ↦ z.1.1.2 i) heq
      simpa [horizontalGoodPrefix, horizontalAxisPrefix] using hp
    · intro i
      have hs := congrArg (fun z ↦ z.2.2 i) heq
      simpa [horizontalAxisSuffix] using hs

lemma card_horizontalGood_suffix_mem_le (s r : ℕ) (E : Finset (AxisWord r)) :
    Fintype.card {p : HorizontalGoodPath (s + r) // horizontalAxisSuffix p ∈ E} ≤
      Fintype.card (HorizontalGoodPath s) * E.card := by
  let f : {p : HorizontalGoodPath (s + r) // horizontalAxisSuffix p ∈ E} →
      HorizontalGoodPath s × E := fun p ↦
    (horizontalGoodPrefix p.1, ⟨horizontalAxisSuffix p.1, p.property⟩)
  have hcard := Fintype.card_le_of_injective f (by
    intro p q h
    apply Subtype.ext
    apply horizontalGoodPrefix_suffix_injective s r
    have hpref : horizontalGoodPrefix p.1 = horizontalGoodPrefix q.1 := congrArg Prod.fst h
    have hsuf : horizontalAxisSuffix p.1 = horizontalAxisSuffix q.1 :=
      congrArg (fun z ↦ z.2.1) h
    exact Prod.ext hpref hsuf)
  simpa [Fintype.card_prod, Fintype.card_coe] using hcard

lemma horizontalGoodPath_card_pos (n : ℕ) : 0 < Fintype.card (HorizontalGoodPath n) := by
  rw [Fintype.card_pos_iff]
  let H : Finset (Fin n) := Finset.univ
  let S : Fin n → Bool := fun _ ↦ true
  refine ⟨⟨(H, S), ?_⟩⟩
  apply horizontalGood_of_fst_nonneg
  intro t ht
  simp [finiteAxisWalk_fst, H, S, sign]

/-- Any event on the final `r` axis words pays only a square-root density factor when conditioning
on one compressed coordinate, rather than the linear factor for quadrant conditioning. -/
theorem horizontalGood_suffix_density_sq_le (s r : ℕ) (E : Finset (AxisWord r)) :
    ((Fintype.card {p : HorizontalGoodPath (s + r) //
          horizontalAxisSuffix p ∈ E} : ℝ) /
        Fintype.card (HorizontalGoodPath (s + r))) ^ 2 ≤
      (4 * (s + r + 1 : ℝ) / (s + 1 : ℝ)) *
        (((E.card : ℝ) / (4 : ℝ) ^ r) ^ 2) := by
  have hcardNat := card_horizontalGood_suffix_mem_le s r E
  have hcard :
      (Fintype.card {p : HorizontalGoodPath (s + r) //
        horizontalAxisSuffix p ∈ E} : ℝ) ≤
      Fintype.card (HorizontalGoodPath s) * E.card := by exact_mod_cast hcardNat
  have hden : (0 : ℝ) < Fintype.card (HorizontalGoodPath (s + r)) := by
    exact_mod_cast horizontalGoodPath_card_pos (s + r)
  have hmassPos : 0 < horizontalGoodMass (s + r) := by
    unfold horizontalGoodMass
    exact div_pos hden (by positivity)
  have hdensity :
      (Fintype.card {p : HorizontalGoodPath (s + r) //
          horizontalAxisSuffix p ∈ E} : ℝ) /
          Fintype.card (HorizontalGoodPath (s + r)) ≤
        (horizontalGoodMass s / horizontalGoodMass (s + r)) *
          ((E.card : ℝ) / (4 : ℝ) ^ r) := by
    apply (div_le_iff₀ hden).2
    calc
      (Fintype.card {p : HorizontalGoodPath (s + r) //
          horizontalAxisSuffix p ∈ E} : ℝ) ≤
        Fintype.card (HorizontalGoodPath s) * E.card := hcard
      _ = ((horizontalGoodMass s / horizontalGoodMass (s + r)) *
          ((E.card : ℝ) / (4 : ℝ) ^ r)) *
            Fintype.card (HorizontalGoodPath (s + r)) := by
        unfold horizontalGoodMass
        rw [pow_add]
        field_simp
  have hratioSq :
      (horizontalGoodMass s / horizontalGoodMass (s + r)) ^ 2 ≤
        4 * (s + r + 1 : ℝ) / (s + 1 : ℝ) := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hmassPos)).2
    have hlo := horizontalGoodMass_sq_lower (s + r)
    push_cast at hlo
    have hhi := horizontalGoodMass_sq_upper s
    have hfac : 0 ≤ 4 * (s + r + 1 : ℝ) / (s + 1 : ℝ) := by positivity
    calc
      horizontalGoodMass s ^ 2 ≤ 2 / (s + 1 : ℝ) := hhi
      _ = (4 * (s + r + 1 : ℝ) / (s + 1 : ℝ)) *
          (1 / (2 * (s + r + 1 : ℝ))) := by field_simp; norm_num
      _ ≤ (4 * (s + r + 1 : ℝ) / (s + 1 : ℝ)) *
          horizontalGoodMass (s + r) ^ 2 :=
        mul_le_mul_of_nonneg_left hlo hfac
  have hleft0 : 0 ≤
      (Fintype.card {p : HorizontalGoodPath (s + r) //
          horizontalAxisSuffix p ∈ E} : ℝ) /
        Fintype.card (HorizontalGoodPath (s + r)) := by positivity
  have hmassS0 : 0 ≤ horizontalGoodMass s := by
    unfold horizontalGoodMass
    positivity
  have hright0 : 0 ≤
      (horizontalGoodMass s / horizontalGoodMass (s + r)) *
        ((E.card : ℝ) / (4 : ℝ) ^ r) := by
    exact mul_nonneg (div_nonneg hmassS0 hmassPos.le) (by positivity)
  calc
    _ ≤ ((horizontalGoodMass s / horizontalGoodMass (s + r)) *
        ((E.card : ℝ) / (4 : ℝ) ^ r)) ^ 2 :=
      (sq_le_sq₀ hleft0 hright0).2 hdensity
    _ = (horizontalGoodMass s / horizontalGoodMass (s + r)) ^ 2 *
        (((E.card : ℝ) / (4 : ℝ) ^ r) ^ 2) := by ring
    _ ≤ (4 * (s + r + 1 : ℝ) / (s + 1 : ℝ)) *
        (((E.card : ℝ) / (4 : ℝ) ^ r) ^ 2) := by gcongr

end Erdos521
