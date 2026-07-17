/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686MatchingResultant

/-!
# Erdős 686: exclusion of collinear matching support

This file isolates the exact affine-line argument in the large-`k` matching
lane.  If every translated owner point lies on one affine line, the product
of the pairwise-coprime owner moduli divides the value of that line at
`(-n,-d)`.  The zero value is excluded by the banked zero-secant degree-one
theorem as soon as the support has at least three cells.  A strict product
dominance hypothesis then excludes the remaining nonzero value.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The affine-line resultant obtained by evaluating
`u*j + v*rho = w` at the translated point `(-n,-d)`. -/
def affineLineResultant (u v w n d : ℤ) : ℤ :=
  u * n + v * d + w

/-- Normal-vector coefficients of the line through two owner cells. -/
def secantLineU (e f : ℕ × ℕ) : ℤ :=
  ownerCellOffset f - ownerCellOffset e

def secantLineV (e f : ℕ × ℕ) : ℤ :=
  -((ownerCellRow f : ℤ) - (ownerCellRow e : ℤ))

def secantLineW (e f : ℕ × ℕ) : ℤ :=
  secantLineU e f * (ownerCellRow e : ℤ) +
    secantLineV e f * ownerCellOffset e

/-- A cell in the owner square has signed diagonal offset at most `k-1`. -/
theorem ownerCellOffset_natAbs_le_k_sub_one
    {k : ℕ} {e : ℕ × ℕ}
    (hk : 1 ≤ k)
    (he : ownerCellRow e ∈ Finset.Icc 1 k ∧
      ownerCellColumn e ∈ Finset.Icc 1 k) :
    Int.natAbs (ownerCellOffset e) ≤ k - 1 := by
  rcases e with ⟨j, i⟩
  simp only [ownerCellRow, ownerCellColumn] at he
  have hbound :
      |ownerCellOffset (j, i)| ≤ ((k - 1 : ℕ) : ℤ) := by
    rw [abs_le, Nat.cast_sub hk]
    simp only [ownerCellOffset, ownerDiagonalOffset, ownerCellColumn,
      ownerCellRow]
    have hr := Finset.mem_Icc.mp he.1
    have hc := Finset.mem_Icc.mp he.2
    constructor <;> omega
  have hcast :
      ((Int.natAbs (ownerCellOffset (j, i)) : ℕ) : ℤ) ≤
        ((k - 1 : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    exact hbound
  exact_mod_cast hcast

/-- The explicit secant normal through two owner cells has exactly the
coefficient bounds used in the affine-line mass comparison. -/
theorem secantLine_coefficients_bounded
    {k : ℕ} {e f : ℕ × ℕ}
    (hk : 16 ≤ k)
    (he : ownerCellRow e ∈ Finset.Icc 1 k ∧
      ownerCellColumn e ∈ Finset.Icc 1 k)
    (hf : ownerCellRow f ∈ Finset.Icc 1 k ∧
      ownerCellColumn f ∈ Finset.Icc 1 k) :
    Int.natAbs (secantLineU e f) ≤ 2 * (k - 1) ∧
    Int.natAbs (secantLineV e f) ≤ k - 1 ∧
    Int.natAbs (secantLineW e f) < 3 * k ^ 2 := by
  have heOffset := ownerCellOffset_natAbs_le_k_sub_one (by omega) he
  have hfOffset := ownerCellOffset_natAbs_le_k_sub_one (by omega) hf
  have hu : Int.natAbs (secantLineU e f) ≤ 2 * (k - 1) := by
    rw [secantLineU]
    exact (Int.natAbs_sub_le _ _).trans (by omega)
  have hv : Int.natAbs (secantLineV e f) ≤ k - 1 := by
    rw [secantLineV, Int.natAbs_neg]
    have hr := Finset.mem_Icc.mp he.1
    have hs := Finset.mem_Icc.mp hf.1
    have hbound :
        |(ownerCellRow f : ℤ) - (ownerCellRow e : ℤ)| ≤
          ((k - 1 : ℕ) : ℤ) := by
      rw [abs_le, Nat.cast_sub (by omega : 1 ≤ k)]
      constructor <;> omega
    have hcast :
        ((Int.natAbs ((ownerCellRow f : ℤ) -
            (ownerCellRow e : ℤ)) : ℕ) : ℤ) ≤
          ((k - 1 : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hbound
    exact_mod_cast hcast
  have hwTri :
      Int.natAbs (secantLineW e f) ≤
        Int.natAbs (secantLineU e f) * ownerCellRow e +
          Int.natAbs (secantLineV e f) *
            Int.natAbs (ownerCellOffset e) := by
    rw [secantLineW]
    calc
      Int.natAbs
          (secantLineU e f * (ownerCellRow e : ℤ) +
            secantLineV e f * ownerCellOffset e) ≤
          Int.natAbs (secantLineU e f * (ownerCellRow e : ℤ)) +
            Int.natAbs (secantLineV e f * ownerCellOffset e) :=
        Int.natAbs_add_le _ _
      _ = Int.natAbs (secantLineU e f) * ownerCellRow e +
          Int.natAbs (secantLineV e f) *
            Int.natAbs (ownerCellOffset e) := by
        rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
  have hrowLe : ownerCellRow e ≤ k := (Finset.mem_Icc.mp he.1).2
  have hwCoarse :
      Int.natAbs (secantLineW e f) ≤
        2 * (k - 1) * k + (k - 1) ^ 2 := by
    have hfirst := Nat.mul_le_mul hu hrowLe
    have hsecond := Nat.mul_le_mul hv heOffset
    exact hwTri.trans (by simpa [pow_two] using Nat.add_le_add hfirst hsecond)
  have hwBound : 2 * (k - 1) * k + (k - 1) ^ 2 < 3 * k ^ 2 := by
    have hfirst : 2 * (k - 1) * k ≤ 2 * k ^ 2 := by
      have h := Nat.mul_le_mul_right k
        (Nat.mul_le_mul_left 2 (Nat.sub_le k 1))
      simpa [pow_two, mul_assoc] using h
    have hsecond : (k - 1) ^ 2 < k ^ 2 :=
      Nat.pow_lt_pow_left (by omega : k - 1 < k) (by norm_num)
    omega
  exact ⟨hu, hv, lt_of_le_of_lt hwCoarse hwBound⟩

theorem secantLineU_ne_zero_of_offset_ne
    {e f : ℕ × ℕ} (h : ownerCellOffset e ≠ ownerCellOffset f) :
    secantLineU e f ≠ 0 := by
  simp only [secantLineU, sub_ne_zero]
  exact Ne.symm h

theorem secantLine_through_left (e f : ℕ × ℕ) :
    secantLineU e f * (ownerCellRow e : ℤ) +
      secantLineV e f * ownerCellOffset e = secantLineW e f := rfl

theorem secantLine_through_right (e f : ℕ × ℕ) :
    secantLineU e f * (ownerCellRow f : ℤ) +
      secantLineV e f * ownerCellOffset f = secantLineW e f := by
  simp only [secantLineU, secantLineV, secantLineW]
  ring

/-- One owner modulus divides the affine-line resultant. -/
theorem owner_dvd_affineLineResultant
    {P u v w n d j rho : ℤ}
    (hrow : P ∣ n + j)
    (hdiag : P ∣ d + rho)
    (hline : u * j + v * rho = w) :
    P ∣ affineLineResultant u v w n d := by
  have hu := dvd_mul_of_dvd_right hrow u
  have hv := dvd_mul_of_dvd_right hdiag v
  have hadd := dvd_add hu hv
  convert hadd using 1
  simp only [affineLineResultant]
  rw [← hline]
  ring

/-- Pairwise-coprime owner moduli multiply in the affine-line divisor. -/
theorem support_product_dvd_affineLineResultant
    {α : Type*} {S : Finset α}
    (P : α → ℤ) (row offset : α → ℤ)
    (u v w n d : ℤ)
    (hpair : (S : Set α).Pairwise (Function.onFun IsCoprime P))
    (hrow : ∀ e ∈ S, P e ∣ n + row e)
    (hdiag : ∀ e ∈ S, P e ∣ d + offset e)
    (hline : ∀ e ∈ S, u * row e + v * offset e = w) :
    (∏ e ∈ S, P e) ∣ affineLineResultant u v w n d := by
  classical
  apply Finset.prod_dvd_of_coprime hpair
  intro e he
  exact owner_dvd_affineLineResultant
    (hrow e he) (hdiag e he) (hline e he)

/-- If the affine-line resultant vanishes and the normal vector is nonzero,
every secant between two points of the support vanishes. -/
theorem ownerCellSecant_eq_zero_of_affineLineResultant_eq_zero
    {n d : ℕ} {e f : ℕ × ℕ} {u v w : ℤ}
    (hnormal : u ≠ 0 ∨ v ≠ 0)
    (heline :
      u * (ownerCellRow e : ℤ) + v * ownerCellOffset e = w)
    (hfline :
      u * (ownerCellRow f : ℤ) + v * ownerCellOffset f = w)
    (hzero : affineLineResultant u v w (n : ℤ) (d : ℤ) = 0) :
    ownerCellSecant n d e f = 0 := by
  have hetranslated :
      u * ((n : ℤ) + (ownerCellRow e : ℤ)) +
          v * ((d : ℤ) + ownerCellOffset e) = 0 := by
    simp only [affineLineResultant] at hzero
    linear_combination hzero + heline
  have hftranslated :
      u * ((n : ℤ) + (ownerCellRow f : ℤ)) +
          v * ((d : ℤ) + ownerCellOffset f) = 0 := by
    simp only [affineLineResultant] at hzero
    linear_combination hzero + hfline
  rcases hnormal with hu | hv
  · apply mul_left_cancel₀ hu
    simp only [ownerCellSecant, twoOwnerSecantForm]
    linear_combination
      ((d : ℤ) + ownerCellOffset f) * hetranslated -
        ((d : ℤ) + ownerCellOffset e) * hftranslated
  · apply mul_left_cancel₀ hv
    simp only [ownerCellSecant, twoOwnerSecantForm]
    linear_combination
      ((n : ℤ) + (ownerCellRow e : ℤ)) *
          hftranslated -
        ((n : ℤ) + (ownerCellRow f : ℤ)) * hetranslated

/-- The zero affine-line branch contains at most two matching cells.  This
is the precise use of the zero-secant graph theorem: relative to any chosen
cell, every other cell is a zero-secant neighbor, while that neighbor set has
cardinality at most one. -/
theorem collinear_support_card_le_two_of_resultant_eq_zero
    {k n d : ℕ} {S : Finset (ℕ × ℕ)} {u v w : ℤ}
    (hk : 16 ≤ k)
    (hd : k ≤ d)
    (hgap : 708827 * k ^ 2 < 5000000 * d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hcells : ∀ z ∈ S,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hoffsetInj : ∀ a ∈ S, ∀ b ∈ S,
      ownerCellOffset a = ownerCellOffset b → a = b)
    (hnormal : u ≠ 0 ∨ v ≠ 0)
    (hline : ∀ e ∈ S,
      u * (ownerCellRow e : ℤ) + v * ownerCellOffset e = w)
    (hzero : affineLineResultant u v w (n : ℤ) (d : ℤ) = 0) :
    S.card ≤ 2 := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨e, he⟩ := hS
    have hdegree := zero_secant_graph_max_degree_one
      hk hd hgap heq hcells hoffsetInj he
    have hfilter :
        (S.erase e).filter (fun f => ownerCellSecant n d e f = 0) =
          S.erase e := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h,
          ownerCellSecant_eq_zero_of_affineLineResultant_eq_zero
            hnormal (hline e he) (hline f h.2) hzero⟩
    rw [hfilter] at hdegree
    rw [Finset.card_erase_of_mem he] at hdegree
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

/-- Exact coefficient-height estimate for a primitive affine line.  The
coefficient bounds are the ones obtained from two cells in the `k × k`
owner square. -/
theorem affineLineResultant_natAbs_lt_three_k_sq_mul_d
    {k n d : ℕ} {u v w : ℤ}
    (hk : 16 ≤ k)
    (hd : k ≤ d)
    (hn : n < k * d)
    (hu : Int.natAbs u ≤ 2 * (k - 1))
    (hv : Int.natAbs v ≤ k - 1)
    (hw : Int.natAbs w < 3 * k ^ 2) :
    Int.natAbs (affineLineResultant u v w (n : ℤ) (d : ℤ)) <
      3 * k ^ 2 * d := by
  have htri :
      Int.natAbs (affineLineResultant u v w (n : ℤ) (d : ℤ)) ≤
        Int.natAbs u * n + Int.natAbs v * d + Int.natAbs w := by
    rw [affineLineResultant]
    calc
      Int.natAbs (u * (n : ℤ) + v * (d : ℤ) + w) ≤
          Int.natAbs (u * (n : ℤ) + v * (d : ℤ)) +
            Int.natAbs w := Int.natAbs_add_le _ _
      _ ≤ (Int.natAbs (u * (n : ℤ)) +
            Int.natAbs (v * (d : ℤ))) + Int.natAbs w :=
          Nat.add_le_add_right (Int.natAbs_add_le _ _) _
      _ = Int.natAbs u * n + Int.natAbs v * d + Int.natAbs w := by
          rw [Int.natAbs_mul, Int.natAbs_mul,
            Int.natAbs_natCast, Int.natAbs_natCast]
  have huTerm : Int.natAbs u * n < 2 * (k - 1) * (k * d) := by
    have hnMul := Nat.mul_lt_mul_of_pos_left hn (by omega : 0 < 2 * (k - 1))
    exact lt_of_le_of_lt (Nat.mul_le_mul_right n hu) (by
      simpa [mul_assoc] using hnMul)
  have hvTerm : Int.natAbs v * d ≤ (k - 1) * d :=
    Nat.mul_le_mul_right d hv
  have hcoarse :
      Int.natAbs u * n + Int.natAbs v * d + Int.natAbs w <
        2 * (k - 1) * (k * d) + (k - 1) * d + 3 * k ^ 2 := by
    omega
  have hpoly :
      2 * (k - 1) * (k * d) + (k - 1) * d + 3 * k ^ 2 ≤
        3 * k ^ 2 * d := by
    have hfirst :
        2 * (k - 1) * (k * d) ≤ 2 * k ^ 2 * d := by
      have h := Nat.mul_le_mul_right (k * d)
        (Nat.mul_le_mul_left 2 (Nat.sub_le k 1))
      simpa [pow_two, mul_assoc] using h
    have hsecond :
        (k - 1) * d + 3 * k ^ 2 ≤ k ^ 2 * d := by
      have hleft : (k - 1) * d ≤ k * d :=
        Nat.mul_le_mul_right d (Nat.sub_le k 1)
      have hright : 3 * k ^ 2 ≤ 3 * k * d := by
        have h := Nat.mul_le_mul_left (3 * k) hd
        simpa [pow_two, mul_assoc] using h
      have hfour : 4 * k * d ≤ k ^ 2 * d := by
        have h := Nat.mul_le_mul_right (k * d) (by omega : 4 ≤ k)
        simpa [pow_two, mul_assoc] using h
      calc
        (k - 1) * d + 3 * k ^ 2 ≤ k * d + 3 * k * d :=
          Nat.add_le_add hleft hright
        _ = 4 * k * d := by ring
        _ ≤ k ^ 2 * d := hfour
    calc
      2 * (k - 1) * (k * d) + (k - 1) * d + 3 * k ^ 2 =
          2 * (k - 1) * (k * d) + ((k - 1) * d + 3 * k ^ 2) := by
            ring
      _ ≤ 2 * k ^ 2 * d + k ^ 2 * d := Nat.add_le_add hfirst hsecond
      _ = 3 * k ^ 2 * d := by ring
  exact lt_of_le_of_lt htri (lt_of_lt_of_le hcoarse hpoly)

/-- Exact collinear-support exclusion.  The only numerical input left to a
mass theorem is the strict comparison between the support product and the
absolute affine-line resultant; the zero-resultant branch is discharged
internally and is not a residual hypothesis. -/
theorem collinear_matching_support_excluded
    {k n d : ℕ} {S : Finset (ℕ × ℕ)}
    (P : (ℕ × ℕ) → ℤ) {u v w : ℤ}
    (hk : 16 ≤ k)
    (hd : k ≤ d)
    (hgap : 708827 * k ^ 2 < 5000000 * d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hcells : ∀ z ∈ S,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hoffsetInj : ∀ a ∈ S, ∀ b ∈ S,
      ownerCellOffset a = ownerCellOffset b → a = b)
    (hcard : 3 ≤ S.card)
    (hnormal : u ≠ 0 ∨ v ≠ 0)
    (hpair : (S : Set (ℕ × ℕ)).Pairwise
      (Function.onFun IsCoprime P))
    (hrow : ∀ e ∈ S, P e ∣ (n : ℤ) + (ownerCellRow e : ℤ))
    (hdiag : ∀ e ∈ S, P e ∣ (d : ℤ) + ownerCellOffset e)
    (hline : ∀ e ∈ S,
      u * (ownerCellRow e : ℤ) + v * ownerCellOffset e = w)
    (hdominates :
      Int.natAbs (affineLineResultant u v w (n : ℤ) (d : ℤ)) <
        Int.natAbs (∏ e ∈ S, P e)) :
    False := by
  by_cases hzero :
      affineLineResultant u v w (n : ℤ) (d : ℤ) = 0
  · have hle := collinear_support_card_le_two_of_resultant_eq_zero
      hk hd hgap heq hcells hoffsetInj hnormal hline hzero
    omega
  · have hdvd := support_product_dvd_affineLineResultant
      P (fun e => (ownerCellRow e : ℤ)) ownerCellOffset
      u v w (n : ℤ) (d : ℤ) hpair hrow hdiag hline
    have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hzero
    omega

/-- Equation-facing collinear exclusion with the line-height estimate and
the support-mass comparison separated as exact natural inequalities. -/
theorem collinear_matching_support_excluded_of_mass
    {k n d : ℕ} {S : Finset (ℕ × ℕ)}
    (P : (ℕ × ℕ) → ℤ) {u v w : ℤ}
    (hk : 16 ≤ k)
    (hd : k ≤ d)
    (hgap : 708827 * k ^ 2 < 5000000 * d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hn : n < k * d)
    (hcells : ∀ z ∈ S,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hoffsetInj : ∀ a ∈ S, ∀ b ∈ S,
      ownerCellOffset a = ownerCellOffset b → a = b)
    (hcard : 3 ≤ S.card)
    (hnormal : u ≠ 0 ∨ v ≠ 0)
    (hu : Int.natAbs u ≤ 2 * (k - 1))
    (hv : Int.natAbs v ≤ k - 1)
    (hw : Int.natAbs w < 3 * k ^ 2)
    (hpair : (S : Set (ℕ × ℕ)).Pairwise
      (Function.onFun IsCoprime P))
    (hrow : ∀ e ∈ S, P e ∣ (n : ℤ) + (ownerCellRow e : ℤ))
    (hdiag : ∀ e ∈ S, P e ∣ (d : ℤ) + ownerCellOffset e)
    (hline : ∀ e ∈ S,
      u * (ownerCellRow e : ℤ) + v * ownerCellOffset e = w)
    (hmass : 3 * k ^ 2 * d < Int.natAbs (∏ e ∈ S, P e)) :
    False := by
  apply collinear_matching_support_excluded P hk hd hgap heq hcells
    hoffsetInj hcard hnormal hpair hrow hdiag hline
  exact lt_trans
    (affineLineResultant_natAbs_lt_three_k_sq_mul_d hk hd hn hu hv hw)
    hmass

/-- Natural-owner specialization of the collinear exclusion.  This is the
interface used by the canonical owner matrix: coprimality and row divisors
remain in `ℕ`, while only the signed diagonal divisor is cast to `ℤ`. -/
theorem collinear_matching_support_excluded_of_nat_mass
    {k n d : ℕ} {S : Finset (ℕ × ℕ)}
    (P : (ℕ × ℕ) → ℕ) {u v w : ℤ}
    (hk : 16 ≤ k)
    (hd : k ≤ d)
    (hgap : 708827 * k ^ 2 < 5000000 * d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hn : n < k * d)
    (hcells : ∀ z ∈ S,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hoffsetInj : ∀ a ∈ S, ∀ b ∈ S,
      ownerCellOffset a = ownerCellOffset b → a = b)
    (hcard : 3 ≤ S.card)
    (hnormal : u ≠ 0 ∨ v ≠ 0)
    (hu : Int.natAbs u ≤ 2 * (k - 1))
    (hv : Int.natAbs v ≤ k - 1)
    (hw : Int.natAbs w < 3 * k ^ 2)
    (hpair : (S : Set (ℕ × ℕ)).Pairwise
      (Function.onFun Nat.Coprime P))
    (hrow : ∀ e ∈ S, P e ∣ n + ownerCellRow e)
    (hdiag : ∀ e ∈ S, (P e : ℤ) ∣ (d : ℤ) + ownerCellOffset e)
    (hline : ∀ e ∈ S,
      u * (ownerCellRow e : ℤ) + v * ownerCellOffset e = w)
    (hmass : 3 * k ^ 2 * d < ∏ e ∈ S, P e) :
    False := by
  classical
  let Pz : (ℕ × ℕ) → ℤ := fun e => (P e : ℤ)
  have hpairZ : (S : Set (ℕ × ℕ)).Pairwise
      (Function.onFun IsCoprime Pz) := by
    intro e he f hf hef
    exact (hpair he hf hef).isCoprime
  have hrowZ : ∀ e ∈ S,
      Pz e ∣ (n : ℤ) + (ownerCellRow e : ℤ) := by
    intro e he
    change (P e : ℤ) ∣ (n : ℤ) + (ownerCellRow e : ℤ)
    exact_mod_cast hrow e he
  have hmassZ :
      3 * k ^ 2 * d < Int.natAbs (∏ e ∈ S, Pz e) := by
    have hprod :
        (∏ e ∈ S, Pz e) = ((∏ e ∈ S, P e : ℕ) : ℤ) := by
      simp [Pz]
    rw [hprod, Int.natAbs_natCast]
    exact hmass
  exact collinear_matching_support_excluded_of_mass Pz hk hd hgap heq hn
    hcells hoffsetInj hcard hnormal hu hv hw hpairZ hrowZ hdiag hline hmassZ

/-- Fully constructive line-normal form of the natural-owner exclusion.
Choosing any two support cells with different offsets supplies the normal,
its nonvanishing, and all three coefficient bounds automatically. -/
theorem collinear_matching_support_excluded_of_secantLine_nat_mass
    {k n d : ℕ} {S : Finset (ℕ × ℕ)}
    (P : (ℕ × ℕ) → ℕ) {e f : ℕ × ℕ}
    (hk : 16 ≤ k)
    (hd : k ≤ d)
    (hgap : 708827 * k ^ 2 < 5000000 * d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hn : n < k * d)
    (hcells : ∀ z ∈ S,
      ownerCellRow z ∈ Finset.Icc 1 k ∧
        ownerCellColumn z ∈ Finset.Icc 1 k)
    (hoffsetInj : ∀ a ∈ S, ∀ b ∈ S,
      ownerCellOffset a = ownerCellOffset b → a = b)
    (hcard : 3 ≤ S.card)
    (heS : e ∈ S)
    (hfS : f ∈ S)
    (hoffsetNe : ownerCellOffset e ≠ ownerCellOffset f)
    (hpair : (S : Set (ℕ × ℕ)).Pairwise
      (Function.onFun Nat.Coprime P))
    (hrow : ∀ z ∈ S, P z ∣ n + ownerCellRow z)
    (hdiag : ∀ z ∈ S,
      (P z : ℤ) ∣ (d : ℤ) + ownerCellOffset z)
    (hline : ∀ z ∈ S,
      secantLineU e f * (ownerCellRow z : ℤ) +
        secantLineV e f * ownerCellOffset z = secantLineW e f)
    (hmass : 3 * k ^ 2 * d < ∏ z ∈ S, P z) :
    False := by
  have hbounds := secantLine_coefficients_bounded hk
    (hcells e heS) (hcells f hfS)
  apply collinear_matching_support_excluded_of_nat_mass P hk hd hgap heq hn
    hcells hoffsetInj hcard
    (Or.inl (secantLineU_ne_zero_of_offset_ne hoffsetNe))
    hbounds.1 hbounds.2.1 hbounds.2.2 hpair hrow hdiag hline hmass

#print axioms owner_dvd_affineLineResultant
#print axioms ownerCellOffset_natAbs_le_k_sub_one
#print axioms secantLine_coefficients_bounded
#print axioms secantLineU_ne_zero_of_offset_ne
#print axioms secantLine_through_left
#print axioms secantLine_through_right
#print axioms support_product_dvd_affineLineResultant
#print axioms ownerCellSecant_eq_zero_of_affineLineResultant_eq_zero
#print axioms collinear_support_card_le_two_of_resultant_eq_zero
#print axioms affineLineResultant_natAbs_lt_three_k_sq_mul_d
#print axioms collinear_matching_support_excluded
#print axioms collinear_matching_support_excluded_of_mass
#print axioms collinear_matching_support_excluded_of_nat_mass
#print axioms collinear_matching_support_excluded_of_secantLine_nat_mass

end Erdos686Variant
end Erdos686
