/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686NormalizedMatching
import ErdosProblems.Erdos686CenteredRatioWindowSharp

/-!
# Erdős 686: two-owner secants and controlled pairing

This module begins the direct large-`k` matching audit.  It first isolates the
exact arithmetic common to any two coprime row-diagonal owners.  Later
sections will add the zero-secant geometry and an explicit controlled pairing
algorithm.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The signed secant determinant of two row-diagonal owner points, evaluated
against the translated point `(-n,-d)`. -/
def twoOwnerSecantForm
    (n d j₁ j₂ ρ₁ ρ₂ : ℤ) : ℤ :=
  (ρ₂ - ρ₁) * (n + j₁) - (j₂ - j₁) * (d + ρ₁)

/-- Signed row-diagonal offset of an owner cell `(j,i)`. -/
def ownerDiagonalOffset (i j : ℕ) : ℤ :=
  (i : ℤ) - (j : ℤ)

/-- Row coordinate of a canonical owner cell encoded as `(row,column)`. -/
def ownerCellRow (e : ℕ × ℕ) : ℕ :=
  e.1

/-- Column coordinate of a canonical owner cell encoded as `(row,column)`. -/
def ownerCellColumn (e : ℕ × ℕ) : ℕ :=
  e.2

/-- Signed diagonal offset of a canonical owner cell. -/
def ownerCellOffset (e : ℕ × ℕ) : ℤ :=
  ownerDiagonalOffset (ownerCellColumn e) (ownerCellRow e)

/-- Secant determinant between two canonical owner cells. -/
def ownerCellSecant (n d : ℕ) (e f : ℕ × ℕ) : ℤ :=
  twoOwnerSecantForm (n : ℤ) (d : ℤ)
    (ownerCellRow e : ℤ) (ownerCellRow f : ℤ)
    (ownerCellOffset e) (ownerCellOffset f)

/-- Re-expanding the same secant determinant at the second owner leaves it
unchanged. -/
theorem twoOwnerSecantForm_recenter
    (n d j₁ j₂ ρ₁ ρ₂ : ℤ) :
    twoOwnerSecantForm n d j₁ j₂ ρ₁ ρ₂ =
      (ρ₂ - ρ₁) * (n + j₂) - (j₂ - j₁) * (d + ρ₂) := by
  simp only [twoOwnerSecantForm]
  ring

/-- Two coprime owner moduli divide their common secant determinant as a
product.  This is the exact two-owner secant divisor, stated over `ℤ` so that
signed offsets need no truncated subtraction. -/
theorem two_owner_secant_dvd
    {P₁ P₂ : ℕ} {n d j₁ j₂ ρ₁ ρ₂ : ℤ}
    (hcop : P₁.Coprime P₂)
    (h₁row : (P₁ : ℤ) ∣ n + j₁)
    (h₁diag : (P₁ : ℤ) ∣ d + ρ₁)
    (h₂row : (P₂ : ℤ) ∣ n + j₂)
    (h₂diag : (P₂ : ℤ) ∣ d + ρ₂) :
    ((P₁ * P₂ : ℕ) : ℤ) ∣
      twoOwnerSecantForm n d j₁ j₂ ρ₁ ρ₂ := by
  have h₁ :
      (P₁ : ℤ) ∣ twoOwnerSecantForm n d j₁ j₂ ρ₁ ρ₂ := by
    exact dvd_sub
      (dvd_mul_of_dvd_right h₁row (ρ₂ - ρ₁))
      (dvd_mul_of_dvd_right h₁diag (j₂ - j₁))
  have h₂ :
      (P₂ : ℤ) ∣ twoOwnerSecantForm n d j₁ j₂ ρ₁ ρ₂ := by
    rw [twoOwnerSecantForm_recenter]
    exact dvd_sub
      (dvd_mul_of_dvd_right h₂row (ρ₂ - ρ₁))
      (dvd_mul_of_dvd_right h₂diag (j₂ - j₁))
  have hcopZ : IsCoprime (P₁ : ℤ) (P₂ : ℤ) := hcop.isCoprime
  simpa using hcopZ.mul_dvd h₁ h₂

/-- Pure ordered-ring core of the zero-secant classification.  If two
nonzero integer direction coordinates have equal positive slope and the
vertical scale is less than `2/K`, then the vertical direction is a unit and
the horizontal direction crosses more than half the row span. -/
theorem zero_secant_direction_classification
    {K x y Δj Δρ : ℤ}
    (hx : 0 < x)
    (hy : 0 < y)
    (hΔρ : Δρ ≠ 0)
    (hrow : |Δj| ≤ K)
    (hscale : K * y < 2 * x)
    (hzero : Δρ * x = Δj * y) :
    |Δρ| = 1 ∧ K < 2 * |Δj| ∧
      ((0 < Δρ ∧ 0 < Δj) ∨ (Δρ < 0 ∧ Δj < 0)) := by
  have hsign :
      (0 < Δρ ∧ 0 < Δj) ∨ (Δρ < 0 ∧ Δj < 0) := by
    rcases lt_or_gt_of_ne hΔρ with hΔρneg | hΔρpos
    · right
      refine ⟨hΔρneg, ?_⟩
      have hlhs : Δρ * x < 0 := mul_neg_of_neg_of_pos hΔρneg hx
      have hrhs : Δj * y < 0 := by simpa [hzero] using hlhs
      rcases mul_neg_iff.mp hrhs with h | h
      · omega
      · exact h.1
    · left
      refine ⟨hΔρpos, ?_⟩
      have hlhs : 0 < Δρ * x := mul_pos hΔρpos hx
      have hrhs : 0 < Δj * y := by simpa [hzero] using hlhs
      rcases mul_pos_iff.mp hrhs with h | h
      · exact h.1
      · omega
  rcases hsign with hpos | hneg
  · have hΔjLe : Δj ≤ K := by simpa [abs_of_pos hpos.2] using hrow
    have hΔρone : Δρ = 1 := by
      by_contra hne
      have htwo : 2 ≤ Δρ := by omega
      have htwoX : 2 * x ≤ Δρ * x :=
        Int.mul_le_mul_of_nonneg_right htwo (le_of_lt hx)
      have hrowY : Δj * y ≤ K * y :=
        Int.mul_le_mul_of_nonneg_right hΔjLe (le_of_lt hy)
      omega
    have hhalf : K < 2 * Δj := by
      rw [hΔρone, one_mul] at hzero
      have hscaled : K * y < (2 * Δj) * y := by
        calc
          K * y < 2 * x := hscale
          _ = (2 * Δj) * y := by rw [hzero]; ring
      exact (Int.mul_lt_mul_right hy).mp hscaled
    exact ⟨by simp [hΔρone], by simpa [abs_of_pos hpos.2] using hhalf,
      Or.inl hpos⟩
  · have hΔjLe : -Δj ≤ K := by simpa [abs_of_neg hneg.2] using hrow
    have hpositiveρ : 0 < -Δρ := by omega
    have hpositivej : 0 < -Δj := by omega
    have hzeroNeg : (-Δρ) * x = (-Δj) * y := by
      calc
        (-Δρ) * x = -(Δρ * x) := by ring
        _ = -(Δj * y) := by rw [hzero]
        _ = (-Δj) * y := by ring
    have hΔρnegOne : -Δρ = 1 := by
      by_contra hne
      have htwo : 2 ≤ -Δρ := by omega
      have htwoX : 2 * x ≤ (-Δρ) * x :=
        Int.mul_le_mul_of_nonneg_right htwo (le_of_lt hx)
      have hrowY : (-Δj) * y ≤ K * y :=
        Int.mul_le_mul_of_nonneg_right hΔjLe (le_of_lt hy)
      omega
    have hhalf : K < 2 * (-Δj) := by
      rw [hΔρnegOne, one_mul] at hzeroNeg
      have hscaled : K * y < (2 * (-Δj)) * y := by
        calc
          K * y < 2 * x := hscale
          _ = (2 * (-Δj)) * y := by rw [hzeroNeg]; ring
      exact (Int.mul_lt_mul_right hy).mp hscaled
    exact ⟨by simp [abs_of_neg hneg.1, hΔρnegOne],
      by simpa [abs_of_neg hneg.2] using hhalf, Or.inr hneg⟩

/-- Exact zero-secant classification for two translated owner points.  The
scale inequality is kept explicit so the later large-`k` bridge can be
audited independently. -/
theorem zero_secant_classification
    {K n d j₁ j₂ ρ₁ ρ₂ : ℤ}
    (hx : 0 < n + j₁)
    (hy : 0 < d + ρ₁)
    (hoffsets : ρ₂ - ρ₁ ≠ 0)
    (hrowBound : |j₂ - j₁| ≤ K)
    (hscale : K * (d + ρ₁) < 2 * (n + j₁))
    (hzero : twoOwnerSecantForm n d j₁ j₂ ρ₁ ρ₂ = 0) :
    |ρ₂ - ρ₁| = 1 ∧ K < 2 * |j₂ - j₁| ∧
      ((0 < ρ₂ - ρ₁ ∧ 0 < j₂ - j₁) ∨
        (ρ₂ - ρ₁ < 0 ∧ j₂ - j₁ < 0)) := by
  apply zero_secant_direction_classification hx hy hoffsets
    hrowBound hscale
  simpa [twoOwnerSecantForm, sub_eq_zero] using hzero

/-- The exact large-`k` scale bridge used by the zero-secant theorem.  The
gap threshold is the integer form of
`d > (708827 / 5000000) * k^2`; the quotient-four equation supplies the
banked sharp ratio `23*k*d < 35*n`. -/
theorem large_k_zero_secant_scale
    {k n d : ℕ}
    (hk : 16 ≤ k)
    (hd : k ≤ d)
    (hgap : 708827 * k ^ 2 < 5000000 * d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (k - 1) * (d + k - 1) < 2 * (n + 1) := by
  have hratio :
      23 * k * d < 35 * n :=
    twenty_three_k_mul_gap_lt_thirty_five_mul_n_of_four_solution hk hd heq
  by_cases hk23 : 23 ≤ k
  · have h51 : 51 * k ≤ 16 * d := by
      by_contra hnot
      have hlt : 16 * d < 51 * k := by omega
      have hnonneg :
          0 ≤ (k : ℤ) * ((k : ℤ) - 23) := mul_nonneg (by omega) (by omega)
      nlinarith
    have hmul :
        (51 * k) * (11 * k + 35) ≤
          (16 * d) * (11 * k + 35) :=
      Nat.mul_le_mul_right (11 * k + 35) h51
    have hpoly :
        560 * (k - 1) ^ 2 ≤ (51 * k) * (11 * k + 35) := by
      let r := k - 1
      have hkEq : k = r + 1 := by
        dsimp [r]
        omega
      change 560 * r ^ 2 ≤ (51 * k) * (11 * k + 35)
      rw [hkEq]
      ring_nf
      nlinarith [sq_nonneg (r : ℤ)]
    have hshape :
        35 * (k - 1) ^ 2 ≤ (11 * k + 35) * d := by
      nlinarith
    have hkEq : k = (k - 1) + 1 := by omega
    have hkMul : k * d = (k - 1) * d + d := by
      calc
        k * d = ((k - 1) + 1) * d := by rw [← hkEq]
        _ = (k - 1) * d + d := by ring
    have hlinear :
        35 * ((k - 1) * (d + k - 1)) ≤ 46 * k * d := by
      have hsum : d + k - 1 = d + (k - 1) := by omega
      calc
        35 * ((k - 1) * (d + k - 1)) =
            35 * (k - 1) * d + 35 * (k - 1) ^ 2 := by
              rw [hsum]
              ring
        _ ≤ 35 * (k - 1) * d + (11 * k + 35) * d :=
          Nat.add_le_add_left hshape _
        _ = 35 * (k - 1) * d + 11 * (k * d) + 35 * d := by ring
        _ = 35 * (k - 1) * d +
            11 * ((k - 1) * d + d) + 35 * d := by rw [hkMul]
        _ = 46 * ((k - 1) * d + d) := by ring
        _ = 46 * (k * d) := by rw [hkMul]
        _ = 46 * k * d := by ring
    have hscaled :
        35 * ((k - 1) * (d + k - 1)) <
          35 * (2 * (n + 1)) := by
      calc
        35 * ((k - 1) * (d + k - 1)) ≤ 46 * k * d := hlinear
        _ = 2 * (23 * k * d) := by ring
        _ < 2 * (35 * n) :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mpr hratio
        _ < 35 * (2 * (n + 1)) := by omega
    exact (Nat.mul_lt_mul_left (by norm_num : 0 < 35)).mp hscaled
  · have hkle : k ≤ 22 := by omega
    interval_cases k <;> norm_num at hgap hratio ⊢ <;> omega

/-- Equation-facing zero-secant classification for two cells in the
`k × k` owner square.  This packages the exact gap threshold and the sharp
ratio theorem into the local scale hypothesis of
`zero_secant_classification`. -/
theorem large_k_zero_secant_classification
    {k n d i₁ i₂ j₁ j₂ : ℕ}
    (hk : 16 ≤ k)
    (hd : k ≤ d)
    (hi₁ : i₁ ∈ Finset.Icc 1 k)
    (hj₁ : j₁ ∈ Finset.Icc 1 k)
    (hj₂ : j₂ ∈ Finset.Icc 1 k)
    (hgap : 708827 * k ^ 2 < 5000000 * d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hoffsets :
      ownerDiagonalOffset i₂ j₂ - ownerDiagonalOffset i₁ j₁ ≠ 0)
    (hzero :
      twoOwnerSecantForm (n : ℤ) (d : ℤ) (j₁ : ℤ) (j₂ : ℤ)
        (ownerDiagonalOffset i₁ j₁) (ownerDiagonalOffset i₂ j₂) = 0) :
    |ownerDiagonalOffset i₂ j₂ - ownerDiagonalOffset i₁ j₁| = 1 ∧
      ((k - 1 : ℕ) : ℤ) < 2 * |(j₂ : ℤ) - (j₁ : ℤ)| ∧
      ((0 < ownerDiagonalOffset i₂ j₂ - ownerDiagonalOffset i₁ j₁ ∧
          0 < (j₂ : ℤ) - (j₁ : ℤ)) ∨
        (ownerDiagonalOffset i₂ j₂ - ownerDiagonalOffset i₁ j₁ < 0 ∧
          (j₂ : ℤ) - (j₁ : ℤ) < 0)) := by
  have hglobal := large_k_zero_secant_scale hk hd hgap heq
  have hi₁1 : 1 ≤ i₁ := (Finset.mem_Icc.mp hi₁).1
  have hi₁k : i₁ ≤ k := (Finset.mem_Icc.mp hi₁).2
  have hj₁1 : 1 ≤ j₁ := (Finset.mem_Icc.mp hj₁).1
  have hj₁k : j₁ ≤ k := (Finset.mem_Icc.mp hj₁).2
  have hj₂1 : 1 ≤ j₂ := (Finset.mem_Icc.mp hj₂).1
  have hj₂k : j₂ ≤ k := (Finset.mem_Icc.mp hj₂).2
  have hdiagPos : 0 < d + i₁ - j₁ := by omega
  have hdiagLe : d + i₁ - j₁ ≤ d + k - 1 := by omega
  have hlocal :
      (k - 1) * (d + i₁ - j₁) < 2 * (n + j₁) := by
    calc
      (k - 1) * (d + i₁ - j₁) ≤
          (k - 1) * (d + k - 1) :=
        Nat.mul_le_mul_left (k - 1) hdiagLe
      _ < 2 * (n + 1) := hglobal
      _ ≤ 2 * (n + j₁) := by omega
  have hyEq :
      (d : ℤ) + ownerDiagonalOffset i₁ j₁ =
        ((d + i₁ - j₁ : ℕ) : ℤ) := by
    rw [show d + i₁ - j₁ = d + i₁ - j₁ by rfl,
      Nat.cast_sub (by omega : j₁ ≤ d + i₁)]
    simp only [Nat.cast_add, ownerDiagonalOffset]
    ring
  have hrowBound :
      |(j₂ : ℤ) - (j₁ : ℤ)| ≤ ((k - 1 : ℕ) : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  have hscale :
      ((k - 1 : ℕ) : ℤ) *
          ((d : ℤ) + ownerDiagonalOffset i₁ j₁) <
        2 * ((n : ℤ) + (j₁ : ℤ)) := by
    rw [hyEq]
    exact_mod_cast hlocal
  exact zero_secant_classification
    (by positivity)
    (by rw [hyEq]; exact_mod_cast hdiagPos)
    hoffsets hrowBound hscale hzero

/-- Under injective diagonal support, a fixed owner has at most one
zero-secant neighbor.  Same-side neighbors have the same unit offset and
therefore coincide; opposite-side neighbors would cross more than the entire
row interval. -/
theorem zero_secant_neighbor_unique
    {k n d : ℕ} {S : Finset (ℕ × ℕ)} {e f g : ℕ × ℕ}
    (hk : 16 ≤ k)
    (hd : k ≤ d)
    (hgap : 708827 * k ^ 2 < 5000000 * d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hcells : ∀ z ∈ S,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hoffsetInj : ∀ a ∈ S, ∀ b ∈ S,
      ownerCellOffset a = ownerCellOffset b → a = b)
    (heS : e ∈ S)
    (hfS : f ∈ S)
    (hgS : g ∈ S)
    (hfe : f ≠ e)
    (hge : g ≠ e)
    (hef : ownerCellSecant n d e f = 0)
    (heg : ownerCellSecant n d e g = 0) :
    f = g := by
  have heCell := hcells e heS
  have hfCell := hcells f hfS
  have hgCell := hcells g hgS
  have hoffEF : ownerCellOffset f - ownerCellOffset e ≠ 0 := by
    intro hzero
    have hoffEq : ownerCellOffset f = ownerCellOffset e := by omega
    exact hfe (hoffsetInj f hfS e heS hoffEq)
  have hoffEG : ownerCellOffset g - ownerCellOffset e ≠ 0 := by
    intro hzero
    have hoffEq : ownerCellOffset g = ownerCellOffset e := by omega
    exact hge (hoffsetInj g hgS e heS hoffEq)
  have hclassEF := large_k_zero_secant_classification
    hk hd heCell.2 heCell.1 hfCell.1 hgap heq hoffEF
    (by simpa [ownerCellSecant, ownerCellOffset, ownerCellRow,
      ownerCellColumn] using hef)
  have hclassEG := large_k_zero_secant_classification
    hk hd heCell.2 heCell.1 hgCell.1 hgap heq hoffEG
    (by simpa [ownerCellSecant, ownerCellOffset, ownerCellRow,
      ownerCellColumn] using heg)
  rcases hclassEF.2.2 with hEFpos | hEFneg
  · rcases hclassEG.2.2 with hEGpos | hEGneg
    · have hunitEF :
          ownerCellOffset f - ownerCellOffset e = 1 := by
        simpa [abs_of_pos hEFpos.1] using hclassEF.1
      have hunitEG :
          ownerCellOffset g - ownerCellOffset e = 1 := by
        simpa [abs_of_pos hEGpos.1] using hclassEG.1
      apply hoffsetInj f hfS g hgS
      omega
    · have hrowEF :
          |(ownerCellRow f : ℤ) - (ownerCellRow e : ℤ)| =
            (ownerCellRow f : ℤ) - (ownerCellRow e : ℤ) :=
        abs_of_pos hEFpos.2
      have hrowEG :
          |(ownerCellRow g : ℤ) - (ownerCellRow e : ℤ)| =
            (ownerCellRow e : ℤ) - (ownerCellRow g : ℤ) := by
        rw [abs_of_neg hEGneg.2]
        ring
      rw [hrowEF] at hclassEF
      rw [hrowEG] at hclassEG
      have hfRowLe := (Finset.mem_Icc.mp hfCell.1).2
      have hgRowOne := (Finset.mem_Icc.mp hgCell.1).1
      omega
  · rcases hclassEG.2.2 with hEGpos | hEGneg
    · have hrowEF :
          |(ownerCellRow f : ℤ) - (ownerCellRow e : ℤ)| =
            (ownerCellRow e : ℤ) - (ownerCellRow f : ℤ) := by
        rw [abs_of_neg hEFneg.2]
        ring
      have hrowEG :
          |(ownerCellRow g : ℤ) - (ownerCellRow e : ℤ)| =
            (ownerCellRow g : ℤ) - (ownerCellRow e : ℤ) :=
        abs_of_pos hEGpos.2
      rw [hrowEF] at hclassEF
      rw [hrowEG] at hclassEG
      have hgRowLe := (Finset.mem_Icc.mp hgCell.1).2
      have hfRowOne := (Finset.mem_Icc.mp hfCell.1).1
      omega
    · have hunitEF :
          ownerCellOffset f - ownerCellOffset e = -1 := by
        have hunit :
            |ownerCellOffset f - ownerCellOffset e| = 1 := by
          simpa [ownerCellOffset] using hclassEF.1
        have hneg :
            ownerCellOffset f - ownerCellOffset e < 0 := by
          simpa [ownerCellOffset] using hEFneg.1
        rw [abs_of_neg hneg] at hunit
        omega
      have hunitEG :
          ownerCellOffset g - ownerCellOffset e = -1 := by
        have hunit :
            |ownerCellOffset g - ownerCellOffset e| = 1 := by
          simpa [ownerCellOffset] using hclassEG.1
        have hneg :
            ownerCellOffset g - ownerCellOffset e < 0 := by
          simpa [ownerCellOffset] using hEGneg.1
        rw [abs_of_neg hneg] at hunit
        omega
      apply hoffsetInj f hfS g hgS
      omega

/-- The zero-secant graph on a row-diagonal support has maximum degree one. -/
theorem zero_secant_graph_max_degree_one
    {k n d : ℕ} {S : Finset (ℕ × ℕ)} {e : ℕ × ℕ}
    (hk : 16 ≤ k)
    (hd : k ≤ d)
    (hgap : 708827 * k ^ 2 < 5000000 * d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hcells : ∀ z ∈ S,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hoffsetInj : ∀ a ∈ S, ∀ b ∈ S,
      ownerCellOffset a = ownerCellOffset b → a = b)
    (heS : e ∈ S) :
    ((S.erase e).filter (fun f => ownerCellSecant n d e f = 0)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro f hf g hg
  simp only [Finset.mem_filter, Finset.mem_erase] at hf hg
  exact zero_secant_neighbor_unique hk hd hgap heq hcells hoffsetInj
    heS hf.1.2 hg.1.2 hf.1.1 hg.1.1 hf.2 hg.2

#print axioms twoOwnerSecantForm_recenter
#print axioms two_owner_secant_dvd
#print axioms zero_secant_direction_classification
#print axioms zero_secant_classification
#print axioms large_k_zero_secant_scale
#print axioms large_k_zero_secant_classification
#print axioms zero_secant_neighbor_unique
#print axioms zero_secant_graph_max_degree_one

end Erdos686Variant
end Erdos686
