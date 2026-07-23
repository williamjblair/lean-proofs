import Research.GenericBooster
import Research.RationalInversion

/-!
# Finite general-position integer-distance witnesses

This file combines the rational generic circle booster with a generic rational
circle inversion and one common integer scale.
-/

namespace Erdos130
namespace FiniteWitness

open Circle
open Circle.GenericBooster
open Circle.RationalInversion
open TangencyBooster

noncomputable section

/-- Uniform scaling about the origin. -/
def scalePoint (s : ℝ) (p : Point) : Point := (s * p.1, s * p.2)

@[simp] theorem sqDist_scalePoint (s : ℝ) (p q : Point) :
    sqDist (scalePoint s p) (scalePoint s q) = s ^ 2 * sqDist p q := by
  simp only [scalePoint, sqDist]
  ring

@[simp] theorem orient_scalePoint (s : ℝ) (p q r : Point) :
    orient (scalePoint s p) (scalePoint s q) (scalePoint s r) =
      s ^ 2 * orient p q r := by
  simp only [orient, scalePoint]
  ring

set_option maxHeartbeats 500000 in
@[simp] theorem cyclicDet_scalePoint (s : ℝ) (p q r t : Point) :
    cyclicDet (scalePoint s p) (scalePoint s q) (scalePoint s r)
      (scalePoint s t) = s ^ 4 * cyclicDet p q r t := by
  simp only [cyclicDet, scalePoint]
  ring

/-- A nonzero uniform scale reflects collinearity. -/
theorem collinear_of_scalePoint {s : ℝ} (hs : s ≠ 0) {p q r : Point}
    (h : Collinear (scalePoint s p) (scalePoint s q) (scalePoint s r)) :
    Collinear p q r := by
  simp only [Collinear, scalePoint] at h ⊢
  have hz : s ^ 2 *
      ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) = 0 := by
    linear_combination h
  have ht := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hs)
  linarith

/-- Distance from a scaled point to an arbitrary center, expressed after
unscaling that center. -/
theorem sqDist_scalePoint_center {s : ℝ} (hs : s ≠ 0) (o p : Point) :
    sqDist o (scalePoint s p) =
      s ^ 2 * sqDist (o.1 / s, o.2 / s) p := by
  simp only [sqDist, scalePoint]
  field_simp [hs]

/-- A nonzero uniform scale reflects four-point concyclicity. -/
theorem concyclic4_of_scalePoint {s : ℝ} (hs : s ≠ 0) {p q r t : Point}
    (h : Concyclic4 (scalePoint s p) (scalePoint s q)
      (scalePoint s r) (scalePoint s t)) : Concyclic4 p q r t := by
  rcases h with ⟨o, hpq, hpr, hpt⟩
  refine ⟨(o.1 / s, o.2 / s), ?_, ?_, ?_⟩
  · rw [sqDist_scalePoint_center hs o p, sqDist_scalePoint_center hs o q] at hpq
    exact (mul_left_cancel₀ (pow_ne_zero 2 hs)) hpq
  · rw [sqDist_scalePoint_center hs o p, sqDist_scalePoint_center hs o r] at hpr
    exact (mul_left_cancel₀ (pow_ne_zero 2 hs)) hpr
  · rw [sqDist_scalePoint_center hs o p, sqDist_scalePoint_center hs o t] at hpt
    exact (mul_left_cancel₀ (pow_ne_zero 2 hs)) hpt

/-- Rational reals are closed under division. -/
theorem rationalReal_div {x y : ℝ} (hx : IsRationalReal x)
    (hy : IsRationalReal y) : IsRationalReal (x / y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a / b, by norm_num⟩

/-- Powers and circle powers of rational data remain rational. -/
theorem rationalReal_sq {x : ℝ} (hx : IsRationalReal x) : IsRationalReal (x ^ 2) := by
  simpa [pow_two] using rationalReal_mul hx hx

theorem rational_inversionDenom (O : Point) (A : Circle)
    (hO : IsRationalReal O.1 ∧ IsRationalReal O.2)
    (hA : RationalCircle A) : IsRationalReal (inversionDenom O A) := by
  simp only [inversionDenom, sqDist]
  exact rationalReal_sub
    (rationalReal_add (rationalReal_sq (rationalReal_sub hA.1 hO.1))
      (rationalReal_sq (rationalReal_sub hA.2.1 hO.2)))
    (rationalReal_sq hA.2.2)

/-- Inverse-circle centers are rational for rational source data and inversion
center. -/
theorem rational_inverseRelativeCenter (O : Point) (A : Circle)
    (hO : IsRationalReal O.1 ∧ IsRationalReal O.2)
    (hA : RationalCircle A) :
    IsRationalReal (inverseRelativeCenter O A).1 ∧
      IsRationalReal (inverseRelativeCenter O A).2 := by
  exact ⟨rationalReal_div (rationalReal_sub hA.1 hO.1)
      (rational_inversionDenom O A hO hA),
    rationalReal_div (rationalReal_sub hA.2.1 hO.2)
      (rational_inversionDenom O A hO hA)⟩

/-- A single rational real has a positive natural denominator multiplier. -/
theorem exists_nat_multiplier {x : ℝ} (hx : IsRationalReal x) :
    ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℝ) * x = (z : ℝ) := by
  obtain ⟨q, rfl⟩ := hx
  refine ⟨q.den, q.den_pos, q.num, ?_⟩
  exact_mod_cast Rat.den_mul_eq_num q

/-- Finitely many rational reals have one common positive natural multiplier
which makes every one integral. -/
theorem exists_common_nat_multiplier {α : Type*} [Fintype α]
    (x : α → ℝ) (hx : ∀ i, IsRationalReal (x i)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ z : ℤ, (N : ℝ) * x i = (z : ℝ) := by
  classical
  have aux : ∀ s : Finset α, ∃ N : ℕ, 0 < N ∧
      ∀ i ∈ s, ∃ z : ℤ, (N : ℝ) * x i = (z : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
        obtain ⟨N, hN, hNs⟩ := ih
        obtain ⟨D, hD, z, hz⟩ := exists_nat_multiplier (hx a)
        refine ⟨N * D, Nat.mul_pos hN hD, ?_⟩
        intro i hi
        simp only [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · refine ⟨(N : ℤ) * z, ?_⟩
          calc
            ((N * D : ℕ) : ℝ) * x i = (N : ℝ) * ((D : ℝ) * x i) := by
              norm_num
              ring
            _ = (N : ℝ) * (z : ℝ) := by rw [hz]
            _ = (((N : ℤ) * z : ℤ) : ℝ) := by norm_num
        · obtain ⟨y, hy⟩ := hNs i hi
          refine ⟨(D : ℤ) * y, ?_⟩
          calc
            ((N * D : ℕ) : ℝ) * x i = (D : ℝ) * ((N : ℝ) * x i) := by
              norm_num
              ring
            _ = (D : ℝ) * (y : ℝ) := by rw [hy]
            _ = (((D : ℤ) * y : ℤ) : ℝ) := by norm_num
  obtain ⟨N, hN, h⟩ := aux Finset.univ
  exact ⟨N, hN, fun i => h i (Finset.mem_univ i)⟩

/-- If a tangency graph cannot be colored with at least two colors, then any
two distinct indices have a third index different from both. -/
theorem exists_third_of_noKColoring {α : Type*} {F : α → Circle} {m : ℕ}
    (hm : 2 ≤ m) (hno : NoKColoring F m) {a b : α} (hab : a ≠ b) :
    ∃ c : α, c ≠ a ∧ c ≠ b := by
  classical
  by_contra hn
  have hall (c : α) : c = a ∨ c = b := by
    by_cases hca : c = a
    · exact Or.inl hca
    · right
      by_contra hcb
      exact hn ⟨c, hca, hcb⟩
  let color : α → Fin m := fun c =>
    if c = a then ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hm⟩ else ⟨1, hm⟩
  obtain ⟨x, y, hxy, ht, hc⟩ := hno color
  by_cases hxa : x = a
  · have hya : y ≠ a := by intro h; exact hxy (hxa.trans h.symm)
    simp [color, hxa, hya] at hc
  · by_cases hya : y = a
    · simp [color, hxa, hya] at hc
    · have hxb : x = b := (hall x).resolve_left hxa
      have hyb : y = b := (hall y).resolve_left hya
      exact hxy (hxb.trans hyb.symm)

/-- A nonzero squared distance characterizes distinct points. -/
theorem sqDist_ne_zero_of_ne {p q : Point} (h : p ≠ q) : sqDist p q ≠ 0 := by
  intro hz
  apply h
  apply Prod.ext <;> simp only [sqDist] at hz ⊢ <;> nlinarith

/-- Indexed finite point families with no `Fin k` coloring via positive integer
edges. -/
def NoKPointColoring {α : Type*} (P : α → Point) (k : ℕ) : Prop :=
  ∀ color : α → Fin k,
    ∃ a b : α, a ≠ b ∧ Adjacent (P a) (P b) ∧ color a = color b

/-- Strong determinant form of indexed incidence general position. -/
def StrongIndexedGeneralPosition {α : Type*} (P : α → Point) : Prop :=
  Function.Injective P ∧
  (∀ v : Fin 3 → α, Function.Injective v →
    orient (P (v 0)) (P (v 1)) (P (v 2)) ≠ 0) ∧
  (∀ v : Fin 4 → α, Function.Injective v →
    cyclicDet (P (v 0)) (P (v 1)) (P (v 2)) (P (v 3)) ≠ 0)

/-- Indexed form of incidence general position. -/
def IndexedGeneralPosition {α : Type*} (P : α → Point) : Prop :=
  Function.Injective P ∧
  (∀ v : Fin 3 → α, Function.Injective v →
    ¬ Collinear (P (v 0)) (P (v 1)) (P (v 2))) ∧
  (∀ v : Fin 4 → α, Function.Injective v →
    ¬ Concyclic4 (P (v 0)) (P (v 1)) (P (v 2)) (P (v 3)))

/-- The determinant package implies the geometric package used by the problem. -/
theorem StrongIndexedGeneralPosition.indexed {α : Type*} {P : α → Point}
    (h : StrongIndexedGeneralPosition P) : IndexedGeneralPosition P := by
  refine ⟨h.1, ?_, ?_⟩
  · intro v hvi hc
    exact h.2.1 v hvi ((collinear_iff_orient_eq_zero _ _ _).mp hc)
  · intro v hvi hc
    exact h.2.2 v hvi (cyclicDet_eq_zero_of_concyclic4 hc)

/-- The finite synthesis theorem: for every number of colors there is a finite
rational point family in incidence general position whose positive-integer-
distance graph has no such coloring. -/
theorem exists_finite_rational_generalPosition_noKPointColoring (k : ℕ) :
    ∃ (α : Type) (_ : Fintype α) (_ : Nonempty α), ∃ P : α → Point,
      StrongIndexedGeneralPosition P ∧ IndexedGeneralPosition P ∧
      (∀ i, IsRationalReal (P i).1 ∧ IsRationalReal (P i).2) ∧
      NoKPointColoring P k := by
  classical
  obtain ⟨α, αfin, αne, F, hgood, hFrat, hno⟩ :=
    exists_finite_good_rational_noKColoring (k + 3)
  letI : Fintype α := αfin
  letI : Nonempty α := αne
  have hFinj : Function.Injective F := by
    intro a b h
    exact hgood.2.1 (congrArg Circle.center h)
  obtain ⟨o, hden, htriClear, hquadClear⟩ :=
    exists_rational_good_inversion_center F hgood.1 hFinj hgood.2.2.2
  let O : Point := ((o.1 : ℝ), (o.2 : ℝ))
  let P : α → Point := fun i => inverseRelativeCenter O (F i)
  have hOrat : IsRationalReal O.1 ∧ IsRationalReal O.2 := by
    exact ⟨⟨o.1, rfl⟩, ⟨o.2, rfl⟩⟩
  have hPrat (i : α) : IsRationalReal (P i).1 ∧ IsRationalReal (P i).2 :=
    rational_inverseRelativeCenter O (F i) hOrat (hFrat i)
  have hPorient : ∀ v : Fin 3 → α, Function.Injective v →
      orient (P (v 0)) (P (v 1)) (P (v 2)) ≠ 0 := by
    intro v hvi hz
    apply htriClear v hvi
    rw [clearedInverseCenterTriple_eq_denom_mul_orient _ _ _ _
      (hden (v 0)) (hden (v 1)) (hden (v 2))]
    change _ * orient (P (v 0)) (P (v 1)) (P (v 2)) = 0
    rw [hz, mul_zero]
  have hPcyclic : ∀ v : Fin 4 → α, Function.Injective v →
      cyclicDet (P (v 0)) (P (v 1)) (P (v 2)) (P (v 3)) ≠ 0 := by
    intro v hvi hz
    apply hquadClear v hvi
    rw [clearedInverseCenterQuad_eq_denom_mul_cyclicDet _ _ _ _ _
      (hden (v 0)) (hden (v 1)) (hden (v 2)) (hden (v 3))]
    change _ * cyclicDet (P (v 0)) (P (v 1)) (P (v 2)) (P (v 3)) = 0
    rw [hz, mul_zero]
  have htri : ∀ v : Fin 3 → α, Function.Injective v →
      ¬ Collinear (P (v 0)) (P (v 1)) (P (v 2)) := by
    intro v hvi hc
    exact hPorient v hvi ((collinear_iff_orient_eq_zero _ _ _).mp hc)
  have hquad : ∀ v : Fin 4 → α, Function.Injective v →
      ¬ Concyclic4 (P (v 0)) (P (v 1)) (P (v 2)) (P (v 3)) := by
    intro v hvi hc
    exact hPcyclic v hvi (cyclicDet_eq_zero_of_concyclic4 hc)
  have hm : 2 ≤ k + 3 := by omega
  have hPinj : Function.Injective P := by
    intro a b hp
    by_contra hab
    obtain ⟨c, hca, hcb⟩ := exists_third_of_noKColoring hm hno hab
    let v : Fin 3 → α := ![a, b, c]
    have hvi : Function.Injective v := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [v]
    apply htri v hvi
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Collinear]
    rw [hp]
    ring
  let signedRadius : α → ℝ := fun i => (F i).radius / inversionDenom O (F i)
  have hsrat (i : α) : IsRationalReal (signedRadius i) :=
    rationalReal_div (hFrat i).2.2
      (rational_inversionDenom O (F i) hOrat (hFrat i))
  obtain ⟨N, hN, hInt⟩ := exists_common_nat_multiplier signedRadius hsrat
  have hNreal : (N : ℝ) ≠ 0 := by positivity
  let Q : α → Point := fun i => scalePoint (N : ℝ) (P i)
  have hQinj : Function.Injective Q := by
    intro a b h
    apply hPinj
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp only [Q, scalePoint] at hx hy
    apply Prod.ext
    · exact (mul_left_cancel₀ hNreal) hx
    · exact (mul_left_cancel₀ hNreal) hy
  have hQtri : ∀ v : Fin 3 → α, Function.Injective v →
      ¬ Collinear (Q (v 0)) (Q (v 1)) (Q (v 2)) := by
    intro v hvi hc
    apply htri v hvi
    apply collinear_of_scalePoint hNreal
    simpa only [Q] using hc
  have hQquad : ∀ v : Fin 4 → α, Function.Injective v →
      ¬ Concyclic4 (Q (v 0)) (Q (v 1)) (Q (v 2)) (Q (v 3)) := by
    intro v hvi hc
    apply hquad v hvi
    apply concyclic4_of_scalePoint hNreal
    simpa only [Q] using hc
  have hQorient : ∀ v : Fin 3 → α, Function.Injective v →
      orient (Q (v 0)) (Q (v 1)) (Q (v 2)) ≠ 0 := by
    intro v hvi
    change orient (scalePoint (N : ℝ) (P (v 0)))
      (scalePoint (N : ℝ) (P (v 1))) (scalePoint (N : ℝ) (P (v 2))) ≠ 0
    rw [orient_scalePoint]
    exact mul_ne_zero (pow_ne_zero 2 hNreal) (hPorient v hvi)
  have hQcyclic : ∀ v : Fin 4 → α, Function.Injective v →
      cyclicDet (Q (v 0)) (Q (v 1)) (Q (v 2)) (Q (v 3)) ≠ 0 := by
    intro v hvi
    change cyclicDet (scalePoint (N : ℝ) (P (v 0)))
      (scalePoint (N : ℝ) (P (v 1))) (scalePoint (N : ℝ) (P (v 2)))
      (scalePoint (N : ℝ) (P (v 3))) ≠ 0
    rw [cyclicDet_scalePoint]
    exact mul_ne_zero (pow_ne_zero 4 hNreal) (hPcyclic v hvi)
  have hQstrong : StrongIndexedGeneralPosition Q := ⟨hQinj, hQorient, hQcyclic⟩
  have hQrat (i : α) : IsRationalReal (Q i).1 ∧ IsRationalReal (Q i).2 := by
    have hNr : IsRationalReal (N : ℝ) := ⟨N, by norm_num⟩
    exact ⟨rationalReal_mul hNr (hPrat i).1,
      rationalReal_mul hNr (hPrat i).2⟩
  refine ⟨α, inferInstance, inferInstance, Q,
    hQstrong, hQstrong.indexed, hQrat, ?_⟩
  intro color
  let largeColor : α → Fin (k + 3) := fun i => (Fin.castAddEmb 3) (color i)
  obtain ⟨a, b, hab, ht, hc⟩ := hno largeColor
  have hc' : color a = color b := (Fin.castAddEmb 3).injective hc
  obtain ⟨za, hza⟩ := hInt a
  obtain ⟨zb, hzb⟩ := hInt b
  let z : ℤ := za + zb
  have hsum : (N : ℝ) * (signedRadius a + signedRadius b) = (z : ℝ) := by
    simp only [mul_add, z, Int.cast_add]
    rw [hza, hzb]
  have hdistP : sqDist (P a) (P b) =
      (signedRadius a + signedRadius b) ^ 2 := by
    simpa only [P, signedRadius] using
      sqDist_inverseRelativeCenter_of_externallyTangent O (F a) (F b)
        (hden a) (hden b) ht
  have hdistQ : sqDist (Q a) (Q b) = (z : ℝ) ^ 2 := by
    change sqDist (scalePoint (N : ℝ) (P a)) (scalePoint (N : ℝ) (P b)) = _
    rw [sqDist_scalePoint, hdistP]
    calc
      (N : ℝ) ^ 2 * (signedRadius a + signedRadius b) ^ 2 =
          ((N : ℝ) * (signedRadius a + signedRadius b)) ^ 2 := by ring
      _ = (z : ℝ) ^ 2 := by rw [hsum]
  have hz : z ≠ 0 := by
    intro hz
    apply sqDist_ne_zero_of_ne (fun h => hab (hQinj h))
    rw [hdistQ, hz]
    norm_num
  have hnatSq : (((z.natAbs : ℕ) : ℝ) ^ 2) = (z : ℝ) ^ 2 := by
    have h := congrArg (fun n : ℤ => (n : ℝ)) (Int.natAbs_sq z)
    simpa using h
  refine ⟨a, b, hab, ?_, hc'⟩
  exact ⟨(fun h => hab (hQinj h)), z.natAbs, Int.natAbs_pos.mpr hz,
    hdistQ.trans hnatSq.symm⟩

end
end FiniteWitness
end Erdos130
