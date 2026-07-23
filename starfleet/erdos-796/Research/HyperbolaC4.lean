import Research.RayProjection
import Research.AnalyticLower
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

namespace Erdos796

open Filter Topology

/-- Rectangle-freeness is inherited by subgraphs. -/
theorem RectangleFree.mono {α β : Type*} {E F : Finset (α × β)}
    (hE : RectangleFree E) (hFE : F ⊆ E) : RectangleFree F := by
  intro a b x y hab hxy hax hay hbx hby
  exact hE hab hxy (hFE hax) (hFE hay) (hFE hbx) (hFE hby)

/-- KST bound when an edge set is contained in prescribed finite vertex
sets. -/
theorem rectangleFree_card_le_ambient
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (X : Finset α) (Y : Finset β)
    (hfree : RectangleFree E) (hsub : E ⊆ X.product Y) :
    (E.card : ℝ) ≤ X.card + Y.card * Real.sqrt X.card := by
  let E' : Finset (↥X × ↥Y) :=
    (Finset.univ : Finset (↥X × ↥Y)).filter fun z => (z.1.1, z.2.1) ∈ E
  have hcard : E'.card = E.card := by
    let f : E → E' := fun z =>
      ⟨(⟨z.1.1, (Finset.mem_product.mp (hsub z.2)).1⟩,
        ⟨z.1.2, (Finset.mem_product.mp (hsub z.2)).2⟩), by
          simp [E']⟩
    let g : E' → E := fun z =>
      ⟨(z.1.1.1, z.1.2.1), by
        have hz := Finset.mem_filter.mp z.2
        exact hz.2⟩
    have hfg : Function.LeftInverse g f := by
      intro z
      rfl
    have hgf : Function.RightInverse g f := by
      intro z
      apply Subtype.ext
      apply Prod.ext <;> rfl
    simpa only [Fintype.card_coe] using
      (Fintype.card_congr (Equiv.mk f g hfg hgf)).symm
  have hfree' : RectangleFree E' := by
    intro a b x y hab hxy hax hay hbx hby
    have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    apply hfree hab' hxy'
    · exact (Finset.mem_filter.mp hax).2
    · exact (Finset.mem_filter.mp hay).2
    · exact (Finset.mem_filter.mp hbx).2
    · exact (Finset.mem_filter.mp hby).2
  have hb := rectangleFree_card_le E' hfree'
  rw [hcard] at hb
  simpa using hb

/-- Fourth-root splitting point for a hyperbolic C4 graph. -/
def hyperbolaSplit (n : ℕ) : ℕ := Nat.nthRoot 4 n

/-- Explicit majorant for a rectangle-free graph in `u*q*p≤n`, with
`p>P₀`, `q` prime, and `q>sqrt n`. -/
noncomputable def hyperbolaC4Majorant (u P₀ n : ℕ) : ℝ :=
  let y := hyperbolaSplit n
  let X₀ := Nat.primeCounting (n / (u * (P₀ + 1)))
  let X₁ := Nat.primeCounting (n / (u * (y + 1)))
  (X₀ : ℝ) + (y : ℝ) * Real.sqrt X₀ +
    (X₁ : ℝ) + (n.sqrt : ℝ) * Real.sqrt X₁

/-- Two-range KST estimate under a hyperbolic product constraint. -/
theorem rectangleFree_hyperbola_card_le
    (E : Finset (ℕ × ℕ)) {u P₀ n : ℕ}
    (hu : 0 < u) (hfree : RectangleFree E)
    (hedge : ∀ z ∈ E,
      z.1.Prime ∧ n.sqrt < z.1 ∧ P₀ < z.2 ∧ z.2 ≤ n.sqrt ∧
        u * z.1 * z.2 ≤ n) :
    (E.card : ℝ) ≤ hyperbolaC4Majorant u P₀ n := by
  let y := hyperbolaSplit n
  let Elo := E.filter fun z => z.2 ≤ y
  let Ehi := E.filter fun z => y < z.2
  have hcard : E.card = Elo.card + Ehi.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := E) (fun z => z.2 ≤ y)
    simpa [Elo, Ehi, not_le] using h.symm
  let Xlo := Nat.primesLE (n / (u * (P₀ + 1)))
  let Ylo := Finset.Icc 1 y
  let Xhi := Nat.primesLE (n / (u * (y + 1)))
  let Yhi := Finset.Icc 1 n.sqrt
  have hloSub : Elo ⊆ Xlo.product Ylo := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have he := hedge z hz'.1
    apply Finset.mem_product.mpr
    constructor
    · apply Nat.mem_primesLE.mpr
      constructor
      · apply (Nat.le_div_iff_mul_le (mul_pos hu (by omega))).2
        calc
          z.1 * (u * (P₀ + 1)) = u * z.1 * (P₀ + 1) := by ring
          _ ≤ u * z.1 * z.2 := by gcongr; omega
          _ ≤ n := he.2.2.2.2
      · exact he.1
    · exact Finset.mem_Icc.mpr ⟨by omega, hz'.2⟩
  have hhiSub : Ehi ⊆ Xhi.product Yhi := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have he := hedge z hz'.1
    apply Finset.mem_product.mpr
    constructor
    · apply Nat.mem_primesLE.mpr
      constructor
      · apply (Nat.le_div_iff_mul_le (mul_pos hu (by omega))).2
        calc
          z.1 * (u * (y + 1)) = u * z.1 * (y + 1) := by ring
          _ ≤ u * z.1 * z.2 := by gcongr; omega
          _ ≤ n := he.2.2.2.2
      · exact he.1
    · exact Finset.mem_Icc.mpr ⟨by omega, he.2.2.2.1⟩
  have hloFree : RectangleFree Elo := hfree.mono (Finset.filter_subset _ _)
  have hhiFree : RectangleFree Ehi := hfree.mono (Finset.filter_subset _ _)
  have hlo := rectangleFree_card_le_ambient Elo Xlo Ylo hloFree hloSub
  have hhi := rectangleFree_card_le_ambient Ehi Xhi Yhi hhiFree hhiSub
  have hXlo : Xlo.card = Nat.primeCounting (n / (u * (P₀ + 1))) := by
    simp [Xlo, Nat.primesLE_card_eq_primeCounting]
  have hXhi : Xhi.card = Nat.primeCounting (n / (u * (y + 1))) := by
    simp [Xhi, Nat.primesLE_card_eq_primeCounting]
  have hYlo : Ylo.card = y := by simp [Ylo]
  have hYhi : Yhi.card = n.sqrt := by simp [Yhi]
  unfold hyperbolaC4Majorant
  dsimp only
  rw [hXlo, hYlo] at hlo
  rw [hXhi, hYhi] at hhi
  rw [hcard]
  push_cast
  linarith

/-- The fourth-root splitting point is eventually large. -/
theorem tendsto_hyperbolaSplit_atTop : Tendsto hyperbolaSplit atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b ^ 4)] with n hn
  unfold hyperbolaSplit
  rw [Nat.le_nthRoot_iff (by norm_num : (4 : ℕ) ≠ 0)]
  exact hn

lemma primeCounting_le_self_hyperbola (m : ℕ) : Nat.primeCounting m ≤ m := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have hsub : Nat.primesLE m ⊆ Finset.Icc 1 m := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    exact Finset.mem_Icc.mpr ⟨hp'.2.one_le, hp'.1⟩
  simpa using Finset.card_le_card hsub

lemma hyperbolaSplit_pow_le (n : ℕ) : (hyperbolaSplit n) ^ 4 ≤ n := by
  unfold hyperbolaSplit
  exact Nat.pow_nthRoot_le_iff.mpr (Or.inl (by norm_num))

lemma lt_hyperbolaSplit_succ_pow (n : ℕ) : n < (hyperbolaSplit n + 1) ^ 4 := by
  unfold hyperbolaSplit
  exact Nat.lt_pow_nthRoot_add_one (by norm_num) n

lemma cast_hyperbolaSplit_le_rpow (n : ℕ) :
    (hyperbolaSplit n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num]
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (by norm_num : (0 : ℝ) < 4)).2
  have hpow : (((hyperbolaSplit n : ℕ) : ℝ) ^ 4) ≤ (n : ℝ) := by
    exact_mod_cast hyperbolaSplit_pow_le n
  convert hpow using 1 <;> norm_num [Real.rpow_natCast]

lemma rpow_quarter_le_cast_split_succ (n : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / 4) ≤ (hyperbolaSplit n + 1 : ℕ) := by
  have hcast : (n : ℝ) ≤ (((hyperbolaSplit n + 1 : ℕ) : ℝ) ^ 4) := by
    exact_mod_cast (lt_hyperbolaSplit_succ_pow n).le
  have hr := Real.rpow_le_rpow (by positivity) hcast (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
  calc
    (n : ℝ) ^ ((1 : ℝ) / 4) ≤
        ((((hyperbolaSplit n + 1 : ℕ) : ℝ) ^ 4) ^ ((1 : ℝ) / 4)) := hr
    _ = (hyperbolaSplit n + 1 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num

lemma rpow_mul_log_div_self {x a : ℝ} (hx : 0 < x) :
    x ^ a * Real.log x / x = Real.log x / x ^ (1 - a) := by
  field_simp
  rw [show x ^ a * Real.log x * x ^ (1 - a) =
    Real.log x * (x ^ a * x ^ (1 - a)) by ring,
    ← Real.rpow_add hx, show a + (1 - a) = (1 : ℝ) by ring,
    Real.rpow_one]

/-- All non-star terms in the two-range C4 bound vanish after normalization. -/
theorem tendsto_hyperbolaC4Majorant_sub_star
    (u P₀ : ℕ) (hu : 0 < u) :
    Tendsto (fun n : ℕ =>
      hyperbolaC4Majorant u P₀ n / ((n : ℝ) / Real.log (n : ℝ)) -
        (Nat.primeCounting (n / (u * (P₀ + 1))) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop (nhds 0) := by
  let y : ℕ → ℕ := hyperbolaSplit
  let X₀ : ℕ → ℕ := fun n => Nat.primeCounting (n / (u * (P₀ + 1)))
  let X₁ : ℕ → ℕ := fun n => Nat.primeCounting (n / (u * (y n + 1)))
  have hX0 : ∀ n, X₀ n ≤ n := fun n =>
    (primeCounting_le_self_hyperbola _).trans (Nat.div_le_self _ _)
  have hX1div : ∀ n, X₁ n ≤ n / (y n + 1) := by
    intro n
    calc
      X₁ n ≤ n / (u * (y n + 1)) := primeCounting_le_self_hyperbola _
      _ ≤ n / (y n + 1) := by
        exact Nat.div_le_div_left (Nat.le_mul_of_pos_left _ hu) (by omega)
  have hsmall0 : Tendsto (fun n : ℕ =>
      (y n : ℝ) * Real.sqrt (X₀ n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n : ℕ =>
      Real.log (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 4))
    · filter_upwards [eventually_gt_atTop 1] with n hn
      positivity
    · filter_upwards [eventually_gt_atTop 1] with n hn
      have hy := cast_hyperbolaSplit_le_rpow n
      have hs : Real.sqrt (X₀ n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hX0 n)
      have hp : (y n : ℝ) * Real.sqrt (X₀ n : ℝ) ≤
          (n : ℝ) ^ ((3 : ℝ) / 4) := by
        calc
          _ ≤ (n : ℝ) ^ ((1 : ℝ) / 4) *
              (n : ℝ) ^ ((1 : ℝ) / 2) := by gcongr
          _ = _ := by
            rw [← Real.rpow_add (by positivity)]
            congr 2
            norm_num
      calc
        (y n : ℝ) * Real.sqrt (X₀ n : ℝ) * Real.log (n : ℝ) / (n : ℝ)
          ≤ (n : ℝ) ^ ((3 : ℝ) / 4) * Real.log (n : ℝ) / (n : ℝ) := by
            gcongr
        _ = Real.log (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 4) := by
          convert rpow_mul_log_div_self (a := (3 : ℝ) / 4)
            (by positivity : (0 : ℝ) < n) using 1 <;> norm_num
    · convert (Real.tendsto_pow_log_div_pow_atTop
        ((1 : ℝ) / 4) 1 (by norm_num)).comp
          tendsto_natCast_atTop_atTop using 1
      funext n
      simp
  have hsmall1a : Tendsto (fun n : ℕ =>
      (X₁ n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n : ℕ =>
      Real.log (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 4))
    · filter_upwards [eventually_gt_atTop 1] with n hn
      positivity
    · filter_upwards [eventually_gt_atTop 1] with n hn
      have hcast : (X₁ n : ℝ) ≤ (n : ℝ) / (y n + 1 : ℕ) := by
        calc
          (X₁ n : ℝ) ≤ (n / (y n + 1) : ℕ) := by exact_mod_cast hX1div n
          _ ≤ (n : ℝ) / (y n + 1 : ℕ) := Nat.cast_div_le
      have hy := rpow_quarter_le_cast_split_succ n
      calc
        (X₁ n : ℝ) * Real.log (n : ℝ) / (n : ℝ)
          ≤ ((n : ℝ) / (y n + 1 : ℕ)) * Real.log (n : ℝ) / (n : ℝ) := by
            gcongr
        _ = Real.log (n : ℝ) / (y n + 1 : ℕ) := by field_simp
        _ ≤ Real.log (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 4) := by
          exact div_le_div_of_nonneg_left
            (Real.log_nonneg (by exact_mod_cast hn.le)) (by positivity) hy
    · convert (Real.tendsto_pow_log_div_pow_atTop
        ((1 : ℝ) / 4) 1 (by norm_num)).comp
          tendsto_natCast_atTop_atTop using 1
      funext n
      simp
  have hsmall1b : Tendsto (fun n : ℕ =>
      (n.sqrt : ℝ) * Real.sqrt (X₁ n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n : ℕ =>
      Real.log (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 8))
    · filter_upwards [eventually_gt_atTop 1] with n hn
      positivity
    · filter_upwards [eventually_gt_atTop 1] with n hn
      have hcast : (X₁ n : ℝ) ≤ (n : ℝ) / (y n + 1 : ℕ) := by
        calc
          (X₁ n : ℝ) ≤ (n / (y n + 1) : ℕ) := by exact_mod_cast hX1div n
          _ ≤ (n : ℝ) / (y n + 1 : ℕ) := Nat.cast_div_le
      have hy := rpow_quarter_le_cast_split_succ n
      have hX : (X₁ n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 4) := by
        calc
          (X₁ n : ℝ) ≤ (n : ℝ) / (y n + 1 : ℕ) := hcast
          _ ≤ (n : ℝ) / ((n : ℝ) ^ ((1 : ℝ) / 4)) := by gcongr
          _ = (n : ℝ) ^ ((3 : ℝ) / 4) := by
            calc
              (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 4) =
                  (n : ℝ) ^ (1 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 4) := by
                    rw [Real.rpow_one]
              _ = (n : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 4) :=
                (Real.rpow_sub (by positivity) _ _).symm
              _ = _ := by congr 2; norm_num
      have hsX : Real.sqrt (X₁ n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 8) := by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
          exact hX
      have hsn : (n.sqrt : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.nat_sqrt_le_real_sqrt
      have hp : (n.sqrt : ℝ) * Real.sqrt (X₁ n : ℝ) ≤
          (n : ℝ) ^ ((7 : ℝ) / 8) := by
        calc
          _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) *
              (n : ℝ) ^ ((3 : ℝ) / 8) := by gcongr
          _ = _ := by
            rw [← Real.rpow_add (by positivity)]
            congr 2
            norm_num
      calc
        (n.sqrt : ℝ) * Real.sqrt (X₁ n : ℝ) * Real.log (n : ℝ) / (n : ℝ)
          ≤ (n : ℝ) ^ ((7 : ℝ) / 8) * Real.log (n : ℝ) / (n : ℝ) := by
            gcongr
        _ = Real.log (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 8) := by
          convert rpow_mul_log_div_self (a := (7 : ℝ) / 8)
            (by positivity : (0 : ℝ) < n) using 1 <;> norm_num
    · convert (Real.tendsto_pow_log_div_pow_atTop
        ((1 : ℝ) / 8) 1 (by norm_num)).comp
          tendsto_natCast_atTop_atTop using 1
      funext n
      simp
  have hsum : Tendsto (fun n : ℕ =>
      (y n : ℝ) * Real.sqrt (X₀ n : ℝ) * Real.log (n : ℝ) / (n : ℝ) +
      (X₁ n : ℝ) * Real.log (n : ℝ) / (n : ℝ) +
      (n.sqrt : ℝ) * Real.sqrt (X₁ n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by simpa using (hsmall0.add hsmall1a).add hsmall1b
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  unfold hyperbolaC4Majorant
  dsimp [y, X₀, X₁]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  field_simp
  ring

/-- Exact normalized limit of the hyperbolic C4 majorant. -/
theorem tendsto_hyperbolaC4Majorant_normalized
    (u P₀ : ℕ) (hu : 0 < u) :
    Tendsto (fun n : ℕ =>
      hyperbolaC4Majorant u P₀ n / ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds ((1 : ℝ) / (u * (P₀ + 1)))) := by
  have hstar := tendsto_primeCounting_div_normalization
    (u * (P₀ + 1)) (mul_pos hu (by omega))
  have herror := tendsto_hyperbolaC4Majorant_sub_star u P₀ hu
  have hsum := herror.add hstar
  convert hsum using 1
  · funext n
    ring
  · push_cast
    simp

end Erdos796
