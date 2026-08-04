import Mathlib

namespace Erdos123

open Combinatorics

noncomputable section

private def encodeWord {ι : Type*} [Fintype ι] (L : ℕ)
    (x : ι → Fin L) : ℕ :=
  Nat.ofDigits L (List.ofFn (fun j : Fin (Fintype.card ι) =>
    (x ((Fintype.equivFin ι).symm j) : ℕ)))

private theorem encodeWord_lt {ι : Type*} [Fintype ι] {L : ℕ} (hL : 1 < L)
    (x : ι → Fin L) : encodeWord L x < L ^ Fintype.card ι := by
  have h := Nat.ofDigits_lt_base_pow_length (b := L)
    (l := List.ofFn (fun j : Fin (Fintype.card ι) =>
      (x ((Fintype.equivFin ι).symm j) : ℕ))) hL
  have hh := h (by
    intro d hd
    simp only [List.mem_ofFn] at hd
    rcases hd with ⟨j, rfl⟩
    exact (x ((Fintype.equivFin ι).symm j)).isLt)
  simpa [encodeWord] using hh

private def lineOptions {α ι : Type*} [Fintype ι] (l : Line α ι) :
    List (Option α) :=
  List.ofFn (fun j : Fin (Fintype.card ι) =>
    l.idxFun ((Fintype.equivFin ι).symm j))

private def optionMask {α : Type*} : Option α → ℕ
  | none => 1
  | some _ => 0

private def optionBase {L : ℕ} : Option (Fin L) → ℕ
  | none => 0
  | some x => (x : ℕ)

private theorem ofDigits_option_line {L : ℕ} (r : Fin L)
    (opts : List (Option (Fin L))) :
    Nat.ofDigits L (opts.map (fun o : Option (Fin L) => (o.getD r : ℕ))) =
      Nat.ofDigits L (opts.map optionBase) +
        (r : ℕ) * Nat.ofDigits L (opts.map optionMask) := by
  induction opts with
  | nil => simp
  | cons o opts ih =>
      cases o <;> simp [Nat.ofDigits_cons, optionMask, optionBase, ih] <;> ring

private theorem line_step_pos {ι : Type*} [Fintype ι] {L : ℕ} (hL : 1 < L)
    (l : Line (Fin L) ι) :
    0 < Nat.ofDigits L ((lineOptions l).map optionMask) := by
  by_contra h
  have hz : Nat.ofDigits L ((lineOptions l).map optionMask) = 0 := by omega
  rcases l.proper with ⟨i, hi⟩
  have hmemOpt : (none : Option (Fin L)) ∈ lineOptions l := by
    unfold lineOptions
    simp only [List.mem_ofFn]
    refine ⟨(Fintype.equivFin ι) i, ?_⟩
    simp [hi]
  have hmemOne : 1 ∈ (lineOptions l).map optionMask := by
    exact List.mem_map.mpr ⟨none, hmemOpt, rfl⟩
  have hallzero := Nat.digits_zero_of_eq_zero (by omega : L ≠ 0) hz 1 hmemOne
  omega

private theorem encode_line_affine {ι : Type*} [Fintype ι] {L : ℕ}
    (hL : 1 < L) (l : Line (Fin L) ι) (r : Fin L) :
    let zero : Fin L := ⟨0, by omega⟩
    encodeWord L (l r) =
      encodeWord L (l zero) + (r : ℕ) *
        Nat.ofDigits L ((lineOptions l).map optionMask) := by
  let zero : Fin L := ⟨0, by omega⟩
  change encodeWord L (l r) = encodeWord L (l zero) + _
  let opts : List (Option (Fin L)) :=
    List.ofFn (fun j : Fin (Fintype.card ι) =>
      l.idxFun ((Fintype.equivFin ι).symm j))
  have hrList :
      List.ofFn (fun j : Fin (Fintype.card ι) =>
        ((l r) ((Fintype.equivFin ι).symm j) : ℕ)) =
        opts.map (fun o : Option (Fin L) => (o.getD r : ℕ)) := by
    rw [List.map_ofFn, List.ofFn_inj]
    funext j
    simp only [opts, Function.comp_apply, Line.coe_apply]
  have hzList :
      List.ofFn (fun j : Fin (Fintype.card ι) =>
        ((l zero) ((Fintype.equivFin ι).symm j) : ℕ)) =
        opts.map optionBase := by
    rw [List.map_ofFn, List.ofFn_inj]
    funext j
    simp only [opts, Function.comp_apply, Line.coe_apply]
    cases l.idxFun ((Fintype.equivFin ι).symm j) <;>
      simp [optionBase, zero]
  unfold encodeWord lineOptions
  rw [hrList, hzList]
  exact ofDigits_option_line r opts

/-- A finite van der Waerden theorem obtained from Hales--Jewett: for every
number of colors and every requested length at least two, one finite initial
interval already forces a monochromatic arithmetic progression of that
length. -/
theorem finite_van_der_waerden (K L : ℕ) (hL : 1 < L) :
    ∃ N : ℕ, 0 < N ∧ ∀ color : ℕ → Fin K,
      ∃ b d : ℕ, 0 < d ∧ b + (L - 1) * d < N ∧
        ∀ r : Fin L, color (b + (r : ℕ) * d) = color b := by
  rcases Line.exists_mono_in_high_dimension (Fin L) (Fin K) with
    ⟨ι, inst, hmono⟩
  letI : Fintype ι := inst
  let N := L ^ Fintype.card ι
  have hN : 0 < N := by
    unfold N
    positivity
  refine ⟨N, hN, ?_⟩
  intro color
  let C : (ι → Fin L) → Fin K := fun x => color (encodeWord L x)
  rcases hmono C with ⟨l, k, hk⟩
  let zero : Fin L := ⟨0, by omega⟩
  let last : Fin L := ⟨L - 1, by omega⟩
  let b := encodeWord L (l zero)
  let d := Nat.ofDigits L ((lineOptions l).map optionMask)
  have hd : 0 < d := line_step_pos hL l
  have hlast : b + (L - 1) * d < N := by
    have hcode := encodeWord_lt hL (l last)
    have hval : (last : ℕ) = L - 1 := rfl
    rw [encode_line_affine hL l last, hval] at hcode
    exact hcode
  refine ⟨b, d, hd, hlast, ?_⟩
  intro r
  dsimp [b, d]
  rw [← encode_line_affine hL l r]
  change C (l r) = C (l zero)
  exact (hk r).trans (hk zero).symm

end

end Erdos123
