import Research.Profiles

namespace Erdos796

/-- An exact capacity profile through 40 found by finite CP-SAT search and
independently certified below by Lean evaluation. -/
def fiberType40 : Fin 40 → Finset ℕ
  | ⟨0, _⟩ => {1}
  | ⟨1, _⟩ => {1, 2}
  | ⟨2, _⟩ => {1, 2, 3}
  | ⟨3, _⟩ => {1, 2, 3}
  | ⟨4, _⟩ => {1, 3, 4, 5}
  | ⟨5, _⟩ => {1, 3, 4, 5, 6}
  | ⟨6, _⟩ => {1, 3, 4, 5, 6, 7}
  | ⟨7, _⟩ => {1, 3, 4, 5, 6, 7}
  | ⟨8, _⟩ => {2, 3, 5, 7, 8, 9}
  | ⟨9, _⟩ => {2, 3, 5, 7, 8, 9, 10}
  | ⟨10, _⟩ => {2, 3, 5, 7, 8, 9, 10, 11}
  | ⟨11, _⟩ => {2, 3, 5, 7, 8, 9, 10, 11}
  | ⟨12, _⟩ => {2, 3, 5, 7, 8, 9, 10, 11, 13}
  | ⟨13, _⟩ => {2, 3, 5, 7, 8, 9, 10, 11, 13}
  | ⟨14, _⟩ => {2, 3, 5, 7, 8, 9, 10, 11, 13}
  | ⟨15, _⟩ => {2, 3, 5, 7, 8, 9, 10, 11, 13}
  | ⟨16, _⟩ => {2, 3, 5, 7, 8, 9, 10, 11, 13, 17}
  | ⟨17, _⟩ => {2, 3, 5, 7, 9, 10, 11, 13, 16, 17}
  | ⟨18, _⟩ => {1, 3, 8, 11, 13, 14, 15, 16, 17, 18, 19}
  | ⟨19, _⟩ => {1, 3, 8, 11, 13, 14, 15, 16, 17, 18, 19, 20}
  | ⟨20, _⟩ => {1, 3, 8, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21}
  | ⟨21, _⟩ => {1, 3, 8, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21}
  | ⟨22, _⟩ => {1, 3, 8, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23}
  | ⟨23, _⟩ => {1, 3, 8, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23}
  | ⟨24, _⟩ => {1, 3, 8, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 25}
  | ⟨25, _⟩ => {1, 3, 8, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 25}
  | ⟨26, _⟩ => {1, 3, 11, 13, 14, 15, 17, 19, 20, 21, 22, 23, 24, 25, 27}
  | ⟨27, _⟩ => {1, 3, 8, 11, 13, 15, 17, 18, 19, 20, 22, 23, 25, 27, 28}
  | ⟨28, _⟩ => {1, 3, 8, 11, 13, 15, 17, 18, 19, 20, 22, 23, 25, 27, 28, 29}
  | ⟨29, _⟩ => {1, 3, 8, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 25, 29}
  | ⟨30, _⟩ => {1, 3, 11, 13, 14, 15, 17, 19, 20, 21, 22, 23, 24, 25, 27, 29, 31}
  | ⟨31, _⟩ => {1, 4, 11, 13, 14, 15, 17, 19, 20, 21, 22, 23, 24, 25, 27, 29, 31}
  | ⟨32, _⟩ => {1, 3, 8, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 25, 29, 31}
  | ⟨33, _⟩ => {1, 4, 11, 14, 15, 17, 19, 20, 21, 23, 24, 25, 26, 27, 29, 31, 33, 34}
  | ⟨34, _⟩ => {1, 4, 6, 7, 11, 15, 17, 19, 23, 25, 26, 27, 29, 31, 32, 33, 34, 35}
  | ⟨35, _⟩ => {1, 4, 11, 13, 14, 15, 19, 23, 25, 26, 27, 29, 31, 32, 33, 34, 35, 36}
  | ⟨36, _⟩ => {1, 2, 7, 8, 11, 13, 15, 17, 18, 19, 20, 23, 25, 27, 29, 31, 33, 35, 37}
  | ⟨37, _⟩ => {1, 4, 11, 13, 14, 15, 20, 21, 23, 24, 25, 26, 27, 29, 31, 33, 34, 37, 38}
  | ⟨38, _⟩ => {1, 4, 11, 14, 15, 17, 19, 23, 25, 26, 27, 29, 31, 32, 33, 34, 35, 36, 37, 39}
  | ⟨39, _⟩ => {1, 4, 7, 11, 15, 17, 23, 25, 26, 27, 29, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40}
  | ⟨n + 40, h⟩ => by omega

/-- All forty types are pairwise cross-compatible, including self-pairs. -/
theorem fiberType40_pairwise_compatible :
    ∀ i j : Fin 40, CrossCompatible (fiberType40 i) (fiberType40 j) := by
  native_decide

/-- The forty-type family as a reusable certified profile. -/
def certifiedProfile40 : FiberProfile 40 where
  posR := by norm_num
  fiber := fiberType40
  positive := by
    intro j d hd
    fin_cases j <;> simp [fiberType40] at hd ⊢ <;> omega
  bounded := by
    intro j d hd
    fin_cases j <;> simp [fiberType40] at hd ⊢ <;> omega
  compatible := fiberType40_pairwise_compatible

/-- Layer weights for the cutoff-40 profile. -/
def fiberWeight40 (j : Fin 40) : ℚ :=
  if j.val = 39 then 1 / 40 else 1 / ((j.val + 1) * (j.val + 2) : ℕ)

/-- Exact normalized gain of the certified profile after subtracting the
reciprocals of all primes through 40. -/
theorem fiberType40_gamma_value :
    (∑ j : Fin 40, fiberWeight40 j * (fiberType40 j).card) -
      ((1 : ℚ) / 2 + 1 / 3 + 1 / 5 + 1 / 7 + 1 / 11 + 1 / 13 +
       1 / 17 + 1 / 19 + 1 / 23 + 1 / 29 + 1 / 31 + 1 / 37) =
      (1377763 : ℚ) / 928200 := by
  native_decide

/-- The exact all-`n` construction from the certified cutoff-40 profile. -/
def fiberType40Construction (n : ℕ) : Finset ℕ :=
  certifiedProfile40.construction n

theorem fiberType40Construction_hasRepBound (n : ℕ) :
    HasRepBound 3 (fiberType40Construction n) :=
  certifiedProfile40.construction_hasRepBound n

theorem fiberType40Construction_subset_Icc (n : ℕ) :
    fiberType40Construction n ⊆ Finset.Icc 1 n :=
  certifiedProfile40.construction_subset_Icc n

theorem fiberType40Construction_card_le_g (n : ℕ) :
    (fiberType40Construction n).card ≤ g 3 n :=
  certifiedProfile40.construction_card_le_g n

end Erdos796
