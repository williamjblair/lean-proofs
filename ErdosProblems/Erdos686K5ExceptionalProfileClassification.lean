import ErdosProblems.Erdos686K5ExceptionalFullSquareSystem
import ErdosProblems.Erdos686K5ExceptionalCrossingSquare

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The exceptional residual vector whose unique unit is in position two. -/
def K5ExceptionalUnitTwoProfile (f : ℕ → ℕ) : Prop :=
  f 1 = 2 ∧ f 2 = 1 ∧ f 3 = 2 ∧ f 4 = 3 ∧ f 5 = 2

/-- The exceptional residual vector whose unique unit is in position four. -/
def K5ExceptionalUnitFourProfile (f : ℕ → ℕ) : Prop :=
  f 1 = 2 ∧ f 2 = 3 ∧ f 3 = 2 ∧ f 4 = 1 ∧ f 5 = 2

private lemma odd_values_of_twos_filter
    {f : ℕ → ℕ}
    (h : (Finset.Icc 1 5).filter (fun r => f r = 2) =
      ({1, 3, 5} : Finset ℕ)) :
    f 1 = 2 ∧ f 3 = 2 ∧ f 5 = 2 := by
  have h1 : 1 ∈ (Finset.Icc 1 5).filter (fun r => f r = 2) := by
    rw [h]
    simp
  have h3 : 3 ∈ (Finset.Icc 1 5).filter (fun r => f r = 2) := by
    rw [h]
    simp
  have h5 : 5 ∈ (Finset.Icc 1 5).filter (fun r => f r = 2) := by
    rw [h]
    simp
  constructor
  · exact (Finset.mem_filter.mp h1).2
  constructor
  · exact (Finset.mem_filter.mp h3).2
  · exact (Finset.mem_filter.mp h5).2

private theorem fully_owned_row_cell_coprime_quotient
    {k n d t j i : ℕ}
    (data : CanonicalOwnerData k n d t)
    (hi : i ∈ Finset.Icc 1 k)
    (hlower : canonicalLowerResidual data j = 1) :
    Nat.Coprime (canonicalOwnerCell data j i)
      ((n + j) / canonicalOwnerCell data j i) := by
  classical
  let S := Finset.Icc 1 k
  let P := canonicalOwnerCell data j i
  let T := ∏ i' ∈ S.erase i, canonicalOwnerCell data j i'
  have hcop : Nat.Coprime P T := by
    dsimp [P, T]
    apply Nat.Coprime.prod_right
    intro i' hi'
    apply canonicalOwnerCells_pairwise_coprime data
    intro heq
    have hii' : i = i' := congrArg Prod.snd heq
    subst i'
    exact (Finset.mem_erase.mp hi').1 rfl
  have hrow : n + j = P * T := by
    calc
      n + j = canonicalOwnerRow data j := by
        rw [canonical_lower_term_factorization data, hlower, one_mul]
      _ = ∏ i' ∈ S, canonicalOwnerCell data j i' := by
        rw [canonicalOwner_row_cell_product data]
      _ = P * T := by
        symm
        exact Finset.mul_prod_erase S
          (fun i' => canonicalOwnerCell data j i') hi
  have hPpos : 0 < P := by
    dsimp [P]
    exact canonicalOwnerCell_pos data
  have hquot : (n + j) / P = T := by
    rw [hrow]
    exact Nat.mul_div_cancel_left T hPpos
  simpa [P, hquot] using hcop

/-- An exceptional lower residual profile is one of two completely explicit
vectors.  The unit position and the residue of the lower base modulo six are
recorded together. -/
theorem k5_exceptional_lower_exact_profile
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hprofile : K5ExceptionalResidualProfile
      (canonicalLowerResidual data)) :
    (n % 6 = 5 ∧
        K5ExceptionalUnitTwoProfile (canonicalLowerResidual data)) ∨
      (n % 6 = 1 ∧
        K5ExceptionalUnitFourProfile (canonicalLowerResidual data)) := by
  have hodd := odd_values_of_twos_filter
    (k5_exceptional_lower_twos_eq_odd_positions data hprofile)
  rcases k5_exceptional_lower_even_allocation_mod_six data hprofile with h | h
  · left
    exact ⟨h.1, hodd.1, h.2.1, hodd.2.1, h.2.2, hodd.2.2⟩
  · right
    exact ⟨h.1, hodd.1, h.2.1, hodd.2.1, h.2.2, hodd.2.2⟩

/-- The upper exceptional profile has exactly six CRT classes.  In each class
the entire residual vector, not merely its unit position, is fixed. -/
theorem k5_exceptional_upper_exact_profile
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hprofile : K5ExceptionalResidualProfile
      (canonicalUpperResidual data)) :
    (t = 1 ∧ (n + d) % 24 = 23 ∧
        K5ExceptionalUnitTwoProfile (canonicalUpperResidual data)) ∨
      (t = 3 ∧ (n + d) % 24 = 5 ∧
        K5ExceptionalUnitTwoProfile (canonicalUpperResidual data)) ∨
      (t = 5 ∧ (n + d) % 24 = 11 ∧
        K5ExceptionalUnitTwoProfile (canonicalUpperResidual data)) ∨
      (t = 1 ∧ (n + d) % 24 = 7 ∧
        K5ExceptionalUnitFourProfile (canonicalUpperResidual data)) ∨
      (t = 3 ∧ (n + d) % 24 = 13 ∧
        K5ExceptionalUnitFourProfile (canonicalUpperResidual data)) ∨
      (t = 5 ∧ (n + d) % 24 = 19 ∧
        K5ExceptionalUnitFourProfile (canonicalUpperResidual data)) := by
  have hodd := odd_values_of_twos_filter
    (k5_exceptional_upper_twos_eq_odd_positions data hfour hprofile)
  rcases k5_exceptional_upper_exact_mod_twenty_four data ht hfour hprofile with
    h | h | h | h | h | h
  · exact Or.inl ⟨h.1, h.2.1, hodd.1, h.2.2.1,
      hodd.2.1, h.2.2.2, hodd.2.2⟩
  · exact Or.inr (Or.inl ⟨h.1, h.2.1, hodd.1, h.2.2.1,
      hodd.2.1, h.2.2.2, hodd.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1, hodd.1, h.2.2.1,
      hodd.2.1, h.2.2.2, hodd.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h.1, h.2.1, hodd.1, h.2.2.1,
        hodd.2.1, h.2.2.2, hodd.2.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h.1, h.2.1, hodd.1, h.2.2.1,
        hodd.2.1, h.2.2.2, hodd.2.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h.1, h.2.1, hodd.1, h.2.2.1,
        hodd.2.1, h.2.2.2, hodd.2.2⟩))))

/-- The simultaneous exceptional branch is completely classified by the
two lower classes and the six upper CRT classes.  This compact conjunction is
the exact twelve-class product classification. -/
theorem k5_exceptional_both_exact_profile_classification
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hlower : K5ExceptionalResidualProfile (canonicalLowerResidual data))
    (hupper : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    ((n % 6 = 5 ∧
        K5ExceptionalUnitTwoProfile (canonicalLowerResidual data)) ∨
      (n % 6 = 1 ∧
        K5ExceptionalUnitFourProfile (canonicalLowerResidual data))) ∧
    ((t = 1 ∧ (n + d) % 24 = 23 ∧
        K5ExceptionalUnitTwoProfile (canonicalUpperResidual data)) ∨
      (t = 3 ∧ (n + d) % 24 = 5 ∧
        K5ExceptionalUnitTwoProfile (canonicalUpperResidual data)) ∨
      (t = 5 ∧ (n + d) % 24 = 11 ∧
        K5ExceptionalUnitTwoProfile (canonicalUpperResidual data)) ∨
      (t = 1 ∧ (n + d) % 24 = 7 ∧
        K5ExceptionalUnitFourProfile (canonicalUpperResidual data)) ∨
      (t = 3 ∧ (n + d) % 24 = 13 ∧
        K5ExceptionalUnitFourProfile (canonicalUpperResidual data)) ∨
      (t = 5 ∧ (n + d) % 24 = 19 ∧
        K5ExceptionalUnitFourProfile (canonicalUpperResidual data))) := by
  exact ⟨k5_exceptional_lower_exact_profile data hlower,
    k5_exceptional_upper_exact_profile data ht hfour hupper⟩

/-- Divide the two terms at an exceptional unit crossing by their exact gcd
owner.  The resulting quotients are coprime, and the primitive crossing-square
defect says that the owner divides `C - 4R`.  This is the exceptional-profile
counterpart of the proper-profile primitive quotient relation. -/
theorem k5_exceptional_crossing_primitive_quotient
    {n d t i j : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hi : i = 2 ∨ i = 4)
    (hj : j = 2 ∨ j = 4)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hcross : K5ExceptionalUnitCrossingConstraint data j i) :
    let P := canonicalOwnerCell data j i
    let R := (n + j) / P
    let C := (n + d + i) / P
    n + j = P * R ∧
      n + d + i = P * C ∧
      Nat.Coprime R C ∧
      R < C ∧ C < 2 * R ∧
      P ∣ 4 * R - C := by
  let P := canonicalOwnerCell data j i
  let R := (n + j) / P
  let C := (n + d + i) / P
  rcases hcross with
    ⟨hit, hlower, hupper, hPgt, hPcop, hrow, hgcdShift, hrowDiv, hcolDiv⟩
  have hPpos : 0 < P := by dsimp [P]; omega
  have hPdvdX : P ∣ n + j := by
    dsimp [P]
    exact canonicalOwnerCell_dvd_lower data
  have hPdvdY : P ∣ n + d + i := by
    dsimp [P]
    simpa [upperTermAfterFour, hit] using
      (canonicalOwnerCell_dvd_upper data (j := j) (i := i))
  have hX : n + j = P * R := by
    exact (Nat.mul_div_cancel' hPdvdX).symm
  have hY : n + d + i = P * C := by
    exact (Nat.mul_div_cancel' hPdvdY).symm
  have hgcd : Nat.gcd (n + j) (n + d + i) = P := by
    dsimp [P]
    exact canonicalOwner_fullyOwned_gcd_upper_eq_cell_of_ne
      data (by rcases hj with rfl | rfl <;> norm_num)
        (by rcases hi with rfl | rfl <;> norm_num)
        hit hlower hupper
  have hcopRC : Nat.Coprime R C := by
    have hgpos : 0 < Nat.gcd (n + j) (n + d + i) := by
      rw [hgcd]
      exact hPpos
    simpa [R, C, hgcd] using Nat.coprime_div_gcd_div_gcd hgpos
  have hsquare := k5_exceptional_crossing_owner_sq_dvd_linear_defect
    data hi hj hfour hd hPcop heq
  have hji : j ≤ d + i := by
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> omega
  have hD :
      (((d + i - j : ℕ) : ℤ)) =
        ((n + d + i : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by
    omega
  have hXZ : ((n + j : ℕ) : ℤ) = (P : ℤ) * (R : ℤ) := by
    exact_mod_cast hX
  have hYZ : ((n + d + i : ℕ) : ℤ) = (P : ℤ) * (C : ℤ) := by
    exact_mod_cast hY
  have hdefect :
      (((d + i - j : ℕ) : ℤ) - 3 * ((n + j : ℕ) : ℤ)) =
        (P : ℤ) * ((C : ℤ) - 4 * (R : ℤ)) := by
    rw [hD, hXZ, hYZ]
    ring
  have hPne : (P : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hPpos)
  have hlinear : (P : ℤ) ∣ (C : ℤ) - 4 * (R : ℤ) := by
    rcases hsquare with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply mul_left_cancel₀ hPne
    calc
      (P : ℤ) * ((C : ℤ) - 4 * (R : ℤ)) =
          ((d + i - j : ℕ) : ℤ) - 3 * ((n + j : ℕ) : ℤ) := hdefect.symm
      _ = (P : ℤ) ^ 2 * z := hz
      _ = (P : ℤ) * ((P : ℤ) * z) := by ring
  have hgap : 2 * d < n :=
    twice_gap_lt_n_of_four_solution (by norm_num) hd heq
  have htermLower : n + j < n + d + i := by
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> omega
  have hRC : R < C := by
    rw [hX, hY] at htermLower
    exact (Nat.mul_lt_mul_left hPpos).mp htermLower
  have htermUpper : n + d + i < 2 * (n + j) := by
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> omega
  have hCtwoR : C < 2 * R := by
    rw [hY, hX] at htermUpper
    have hrewritten : P * C < P * (2 * R) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using htermUpper
    exact (Nat.mul_lt_mul_left hPpos).mp hrewritten
  have hCle : C ≤ 4 * R := by omega
  have hlinear' : (P : ℤ) ∣ 4 * (R : ℤ) - (C : ℤ) := by
    have := dvd_neg.mpr hlinear
    convert this using 1 <;> ring
  have hlinearNat : P ∣ 4 * R - C := by
    exact_mod_cast hlinear'
  exact ⟨hX, hY, hcopRC, hRC, hCtwoR, hlinearNat⟩

/-- The orientation-dependent outer owner supplies the third primitive square
congruence.  Column one is paired with crossing column two, and column five
with crossing column four. -/
def K5ExceptionalOuterPrimitiveBranch
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (j i P Q R C : ℕ) : Prop :=
  (i = 2 ∧
    let A := canonicalOwnerCell data j 1
    let T := (n + j) / A
    let E := (n + d + 1) / A
    n + j = A * T ∧ n + d + 1 = A * E ∧
      P * C = A * E + 1 ∧ P * R = A * T ∧
      Nat.Coprime P A ∧ Nat.Coprime Q A ∧ Nat.Coprime A T ∧
      A ∣ E + T ∧ A ^ 2 ∣ P * (C + R) - 1 ∧
      (A * Q) ^ 2 ∣
        (P * (C + R) - 1) * (P * (C + 6 * R) + 1)) ∨
  (i = 4 ∧
    let A := canonicalOwnerCell data j 5
    let T := (n + j) / A
    let E := (n + d + 5) / A
    n + j = A * T ∧ n + d + 5 = A * E ∧
      A * E = P * C + 1 ∧ P * R = A * T ∧
      Nat.Coprime P A ∧ Nat.Coprime Q A ∧ Nat.Coprime A T ∧
      A ∣ E + T ∧ A ^ 2 ∣ P * (C + R) + 1 ∧
      (A * Q) ^ 2 ∣
        (P * (C + R) + 1) * (P * (C + 6 * R) - 1))

/-- The exact three-owner primitive quotient system formed by the exceptional
crossing, the column-three owner, and an outer owner in the same fully owned
row. -/
def K5ExceptionalMiddlePrimitiveSystem
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t) (j i : ℕ) : Prop :=
    let P := canonicalOwnerCell data j i
    let Q := canonicalOwnerCell data j 3
    let R := (n + j) / P
    let C := (n + d + i) / P
    let S := (n + j) / Q
    let D := (n + d + 3) / Q
    n + j = P * R ∧
      n + d + i = P * C ∧
      n + j = Q * S ∧
      n + d + 3 = Q * D ∧
      P * R = Q * S ∧
      ((i = 2 ∧ Q * D = P * C + 1 ∧
          Q ^ 2 ∣ P * (C + 6 * R) + 1) ∨
        (i = 4 ∧ P * C = Q * D + 1 ∧
          Q ^ 2 ∣ P * (C + 6 * R) - 1)) ∧
      Nat.Coprime P Q ∧
      Nat.Coprime R C ∧
      R < C ∧ C < 2 * R ∧
      Nat.Coprime Q S ∧
      P ∣ 4 * R - C ∧
      Q ∣ D + 6 * S ∧
      canonicalUpperResidual data 3 = 2 ∧
      2 ∣ D ∧
      K5ExceptionalOuterPrimitiveBranch data j i P Q R C

private theorem k5_exceptional_outer_owner_base_system
    {n d t j e : ℕ} (data : CanonicalOwnerData 5 n d t)
    (he : e = 1 ∨ e = 5)
    (hj : j = 2 ∨ j = 4)
    (hd : 5 ≤ d)
    (hfour : 4 ∣ n + d + t)
    (hlower : canonicalLowerResidual data j = 1)
    (hrowStar : ∀ e' ∈ Finset.Icc 1 5,
      (((canonicalOwnerCell data j e' : ℕ) : ℤ) ^ 2) ∣
        k5ExceptionalRowSquareDefect n d j e') :
    let A := canonicalOwnerCell data j e
    let T := (n + j) / A
    let E := (n + d + e) / A
    n + j = A * T ∧ n + d + e = A * E ∧
      Nat.Coprime A T ∧ A ∣ E + T := by
  let A := canonicalOwnerCell data j e
  let T := (n + j) / A
  let E := (n + d + e) / A
  have heIcc : e ∈ Finset.Icc 1 5 := by
    rcases he with rfl | rfl <;> norm_num
  have hAdvdX : A ∣ n + j := by
    dsimp [A]
    exact canonicalOwnerCell_dvd_lower data
  have hAdvdY : A ∣ n + d + e := by
    dsimp [A]
    exact dvd_trans (canonicalOwnerCell_dvd_upper data)
      (upperTermAfterFour_dvd_original hfour)
  have hAT : n + j = A * T := (Nat.mul_div_cancel' hAdvdX).symm
  have hAE : n + d + e = A * E := (Nat.mul_div_cancel' hAdvdY).symm
  have hcopAT : Nat.Coprime A T := by
    simpa [A, T] using fully_owned_row_cell_coprime_quotient
      data heIcc hlower
  have hsq := hrowStar e heIcc
  have hdefect : k5ExceptionalRowSquareDefect n d j e =
      (A : ℤ) * ((E : ℤ) + (T : ℤ)) := by
    have hje : j ≤ d + e := by
      rcases he with rfl | rfl <;> rcases hj with rfl | rfl <;> omega
    have hcastD : ((d + e - j : ℕ) : ℤ) =
        ((n + d + e : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by omega
    have hATZ : ((n + j : ℕ) : ℤ) = (A : ℤ) * (T : ℤ) := by
      exact_mod_cast hAT
    have hAEZ : ((n + d + e : ℕ) : ℤ) = (A : ℤ) * (E : ℤ) := by
      exact_mod_cast hAE
    push_cast at hcastD hATZ hAEZ
    rcases he with rfl | rfl <;>
      simp only [k5ExceptionalRowSquareDefect] <;>
      rw [hcastD, hATZ, hAEZ] <;> ring
  have hApos : 0 < A := by
    dsimp [A]
    exact canonicalOwnerCell_pos data
  have hAne : (A : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hApos)
  have hlinZ : (A : ℤ) ∣ (E : ℤ) + (T : ℤ) := by
    rcases hsq with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply mul_left_cancel₀ hAne
    calc
      (A : ℤ) * ((E : ℤ) + (T : ℤ)) =
          k5ExceptionalRowSquareDefect n d j e := hdefect.symm
      _ = (A : ℤ) ^ 2 * z := hz
      _ = (A : ℤ) * ((A : ℤ) * z) := by ring
  have hlin : A ∣ E + T := by exact_mod_cast hlinZ
  exact ⟨hAT, hAE, hcopAT, hlin⟩

/-- The middle cell of the same fully owned row supplies a genuinely
independent quotient congruence.  If `P` is the unit-row/unit-column crossing
and `Q` is the owner in column three, then the two quotient factorizations
form an exact determinant of absolute value one, while the middle row-square
defect forces `Q ∣ D + 6S`.  Thus this conclusion retains both independent
row/column equations rather than restating the crossing congruence. -/
theorem k5_exceptional_crossing_middle_primitive_system
    {n d t i j : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hi : i = 2 ∨ i = 4)
    (hj : j = 2 ∨ j = 4)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hcross : K5ExceptionalUnitCrossingConstraint data j i)
    (hupperThree : canonicalUpperResidual data 3 = 2)
    (hstar : K5ExceptionalSquareStar data j i) :
    K5ExceptionalMiddlePrimitiveSystem data j i := by
  dsimp only [K5ExceptionalMiddlePrimitiveSystem]
  let P := canonicalOwnerCell data j i
  let Q := canonicalOwnerCell data j 3
  let R := (n + j) / P
  let C := (n + d + i) / P
  let S := (n + j) / Q
  let D := (n + d + 3) / Q
  have hprim := k5_exceptional_crossing_primitive_quotient
    data hi hj hfour hd heq hcross
  dsimp only at hprim
  rcases hprim with ⟨hX, hY, hcopRC, hRC, hCtwoR, hPlinear⟩
  change n + j = P * R at hX
  change n + d + i = P * C at hY
  change Nat.Coprime R C at hcopRC
  change P ∣ 4 * R - C at hPlinear
  have hQdvdX : Q ∣ n + j := by
    dsimp [Q]
    exact canonicalOwnerCell_dvd_lower data
  have hQdvdY : Q ∣ n + d + 3 := by
    dsimp [Q]
    have hmod := canonicalOwnerCell_dvd_upper data (j := j) (i := 3)
    by_cases h3t : 3 = t
    · simp only [upperTermAfterFour, if_pos h3t] at hmod
      exact dvd_trans hmod (Nat.div_dvd_of_dvd (by simpa [h3t] using hfour))
    · simpa [upperTermAfterFour, h3t] using hmod
  have hQS : n + j = Q * S := by
    exact (Nat.mul_div_cancel' hQdvdX).symm
  have hQD : n + d + 3 = Q * D := by
    exact (Nat.mul_div_cancel' hQdvdY).symm
  have hPQ : Nat.Coprime P Q := by
    dsimp [P, Q]
    apply canonicalOwnerCells_pairwise_coprime data
    intro hpairs
    have hii : i = 3 := congrArg Prod.snd hpairs
    rcases hi with rfl | rfl <;> omega
  have hcopQS : Nat.Coprime Q S := by
    simpa [Q, S] using fully_owned_row_cell_coprime_quotient
      data (i := 3) (by norm_num) hcross.2.1
  have hsq := hstar.1 3 (by norm_num)
  have hdefect :
      k5ExceptionalRowSquareDefect n d j 3 =
        (Q : ℤ) * ((D : ℤ) + 6 * (S : ℤ)) := by
    simp only [k5ExceptionalRowSquareDefect]
    have hji : j ≤ d + 3 := by
      rcases hj with rfl | rfl <;> omega
    have hcastD :
        ((d + 3 - j : ℕ) : ℤ) =
          ((n + d + 3 : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by
      omega
    have hQSZ : ((n + j : ℕ) : ℤ) = (Q : ℤ) * (S : ℤ) := by
      exact_mod_cast hQS
    have hQDZ : ((n + d + 3 : ℕ) : ℤ) = (Q : ℤ) * (D : ℤ) := by
      exact_mod_cast hQD
    push_cast at hcastD hQSZ hQDZ
    rw [hcastD, hQSZ, hQDZ]
    ring
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact canonicalOwnerCell_pos data
  have hQne : (Q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQpos)
  have hQlinearZ : (Q : ℤ) ∣ (D : ℤ) + 6 * (S : ℤ) := by
    rcases hsq with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply mul_left_cancel₀ hQne
    calc
      (Q : ℤ) * ((D : ℤ) + 6 * (S : ℤ)) =
          k5ExceptionalRowSquareDefect n d j 3 := hdefect.symm
      _ = (Q : ℤ) ^ 2 * z := hz
      _ = (Q : ℤ) * ((Q : ℤ) * z) := by ring
  have hQlinear : Q ∣ D + 6 * S := by
    exact_mod_cast hQlinearZ
  have hQcop6 : Nat.Coprime Q 6 := by
    dsimp [Q]
    exact (hcross.2.2.2.2.2.1 3 (by norm_num)).2.1
  have hQcop2 : Nat.Coprime Q 2 :=
    hQcop6.coprime_dvd_right (by norm_num)
  have h2Y : 2 ∣ n + d + 3 := by
    have hfactor := canonical_upper_term_factorization data hfour (i := 3)
    rw [hupperThree] at hfactor
    refine ⟨(if 3 = t then 4 else 1) * canonicalOwnerColumn data 3, ?_⟩
    rw [hfactor]
    ring
  have h2D : 2 ∣ D := by
    apply hQcop2.symm.dvd_of_dvd_mul_left
    rwa [← hQD]
  have hQsquareMul : Q ^ 2 ∣ Q * (D + 6 * S) := by
    simpa [pow_two] using Nat.mul_dvd_mul_left Q hQlinear
  have hcommon : P * R = Q * S := hX.symm.trans hQS
  have horient :
      (i = 2 ∧ Q * D = P * C + 1 ∧
          Q ^ 2 ∣ P * (C + 6 * R) + 1) ∨
        (i = 4 ∧ P * C = Q * D + 1 ∧
          Q ^ 2 ∣ P * (C + 6 * R) - 1) := by
    rcases hi with rfl | rfl
    · left
      have hdet : Q * D = P * C + 1 := by omega
      refine ⟨rfl, hdet, ?_⟩
      have hid : P * (C + 6 * R) + 1 = Q * (D + 6 * S) := by
        calc
          P * (C + 6 * R) + 1 = P * C + 1 + 6 * (P * R) := by ring
          _ = Q * D + 6 * (Q * S) := by rw [hdet, hcommon]
          _ = Q * (D + 6 * S) := by ring
      rw [hid]
      exact hQsquareMul
    · right
      have hdet : P * C = Q * D + 1 := by omega
      refine ⟨rfl, hdet, ?_⟩
      have hid : P * (C + 6 * R) - 1 = Q * (D + 6 * S) := by
        calc
          P * (C + 6 * R) - 1 = (P * C + 6 * (P * R)) - 1 := by
            congr 1
            ring
          _ = (Q * D + 1 + 6 * (Q * S)) - 1 := by rw [hdet, hcommon]
          _ = Q * D + 6 * (Q * S) := by omega
          _ = Q * (D + 6 * S) := by ring
      rw [hid]
      exact hQsquareMul
  have houter : K5ExceptionalOuterPrimitiveBranch data j i P Q R C := by
    rcases hi with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      let A := canonicalOwnerCell data j 1
      let T := (n + j) / A
      let E := (n + d + 1) / A
      have hb := k5_exceptional_outer_owner_base_system
        data (e := 1) (by left; rfl) hj hd hfour hcross.2.1 hstar.1
      dsimp only at hb
      change n + j = A * T ∧ n + d + 1 = A * E ∧
        Nat.Coprime A T ∧ A ∣ E + T at hb
      rcases hb with ⟨hAT, hAE, hcopAT, hAlin⟩
      have hPA : Nat.Coprime P A := by
        dsimp [P, A]
        apply canonicalOwnerCells_pairwise_coprime data
        intro hpairs
        have hii : 2 = 1 := congrArg Prod.snd hpairs
        omega
      have hQA : Nat.Coprime Q A := by
        dsimp [Q, A]
        apply canonicalOwnerCells_pairwise_coprime data
        intro hpairs
        have hii : 3 = 1 := congrArg Prod.snd hpairs
        omega
      have hdet : P * C = A * E + 1 := by omega
      have hcommonA : P * R = A * T := hX.symm.trans hAT
      have hAsquareMul : A ^ 2 ∣ A * (E + T) := by
        simpa [pow_two] using Nat.mul_dvd_mul_left A hAlin
      have hid : P * (C + R) - 1 = A * (E + T) := by
        calc
          P * (C + R) - 1 = (P * C + P * R) - 1 := by ring
          _ = (A * E + 1 + A * T) - 1 := by rw [hdet, hcommonA]
          _ = A * E + A * T := by omega
          _ = A * (E + T) := by ring
      have hAsquare : A ^ 2 ∣ P * (C + R) - 1 := by
        rw [hid]
        exact hAsquareMul
      have hQsquare : Q ^ 2 ∣ P * (C + 6 * R) + 1 := by
        rcases horient with ho | ho
        · exact ho.2.2
        · omega
      have hcombined : (A * Q) ^ 2 ∣
          (P * (C + R) - 1) * (P * (C + 6 * R) + 1) := by
        convert Nat.mul_dvd_mul hAsquare hQsquare using 1 <;> ring
      exact ⟨hAT, hAE, hdet, hcommonA, hPA, hQA, hcopAT,
        hAlin, hAsquare, hcombined⟩
    · right
      refine ⟨rfl, ?_⟩
      let A := canonicalOwnerCell data j 5
      let T := (n + j) / A
      let E := (n + d + 5) / A
      have hb := k5_exceptional_outer_owner_base_system
        data (e := 5) (by right; rfl) hj hd hfour hcross.2.1 hstar.1
      dsimp only at hb
      change n + j = A * T ∧ n + d + 5 = A * E ∧
        Nat.Coprime A T ∧ A ∣ E + T at hb
      rcases hb with ⟨hAT, hAE, hcopAT, hAlin⟩
      have hPA : Nat.Coprime P A := by
        dsimp [P, A]
        apply canonicalOwnerCells_pairwise_coprime data
        intro hpairs
        have hii : 4 = 5 := congrArg Prod.snd hpairs
        omega
      have hQA : Nat.Coprime Q A := by
        dsimp [Q, A]
        apply canonicalOwnerCells_pairwise_coprime data
        intro hpairs
        have hii : 3 = 5 := congrArg Prod.snd hpairs
        omega
      have hdet : A * E = P * C + 1 := by omega
      have hcommonA : P * R = A * T := hX.symm.trans hAT
      have hAsquareMul : A ^ 2 ∣ A * (E + T) := by
        simpa [pow_two] using Nat.mul_dvd_mul_left A hAlin
      have hid : P * (C + R) + 1 = A * (E + T) := by
        calc
          P * (C + R) + 1 = P * C + 1 + P * R := by ring
          _ = A * E + A * T := by rw [hdet, hcommonA]
          _ = A * (E + T) := by ring
      have hAsquare : A ^ 2 ∣ P * (C + R) + 1 := by
        rw [hid]
        exact hAsquareMul
      have hQsquare : Q ^ 2 ∣ P * (C + 6 * R) - 1 := by
        rcases horient with ho | ho
        · omega
        · exact ho.2.2
      have hcombined : (A * Q) ^ 2 ∣
          (P * (C + R) + 1) * (P * (C + 6 * R) - 1) := by
        convert Nat.mul_dvd_mul hAsquare hQsquare using 1 <;> ring
      exact ⟨hAT, hAE, hdet, hcommonA, hPA, hQA, hcopAT,
        hAlin, hAsquare, hcombined⟩
  exact ⟨hX, hY, hQS, hQD, hcommon, horient,
    hPQ, hcopRC, hRC, hCtwoR, hcopQS, hPlinear, hQlinear,
    hupperThree, h2D, houter⟩

/-- Exact post-cancellation form of the two independent square congruences.
The cofactor `H` is the product left in the fully owned row after removing
the crossing, middle, and selected outer owners. -/
def K5ExceptionalCancelledCofactorBranch
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (j i : ℕ) : Prop :=
  let P := canonicalOwnerCell data j i
  let Q := canonicalOwnerCell data j 3
  let R := (n + j) / P
  let C := (n + d + i) / P
  (i = 2 ∧
    let A := canonicalOwnerCell data j 1
    let H := R / (A * Q)
    let U := (P * (C + R) - 1) / A ^ 2
    let V := (P * (C + 6 * R) + 1) / Q ^ 2
    R = A * Q * H ∧
      A ^ 2 * U = P * (C + R) - 1 ∧
      Q ^ 2 * V = P * (C + 6 * R) + 1 ∧
      Q ^ 2 * V = A ^ 2 * U + 5 * P * A * Q * H + 2 ∧
      A * U < 3 * P * Q * H ∧
      Q * V < 8 * P * A * H) ∨
  (i = 4 ∧
    let A := canonicalOwnerCell data j 5
    let H := R / (A * Q)
    let U := (P * (C + R) + 1) / A ^ 2
    let V := (P * (C + 6 * R) - 1) / Q ^ 2
    R = A * Q * H ∧
      A ^ 2 * U = P * (C + R) + 1 ∧
      Q ^ 2 * V = P * (C + 6 * R) - 1 ∧
      Q ^ 2 * V + 2 = A ^ 2 * U + 5 * P * A * Q * H ∧
      A * U < 3 * P * Q * H ∧
      Q * V < 8 * P * A * H)

/-- Cancel the forced outer and middle owner squares exactly.  The surviving
cofactors satisfy a signed constant-two equation and strict bounds in the
remaining row cofactor `H`. -/
theorem k5_exceptional_cancelled_cofactor_system
    {n d t i j : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hPgt : 1 < canonicalOwnerCell data j i)
    (hsys : K5ExceptionalMiddlePrimitiveSystem data j i) :
    K5ExceptionalCancelledCofactorBranch data j i := by
  dsimp only [K5ExceptionalMiddlePrimitiveSystem] at hsys
  let P := canonicalOwnerCell data j i
  let Q := canonicalOwnerCell data j 3
  let R := (n + j) / P
  let C := (n + d + i) / P
  let S := (n + j) / Q
  let D := (n + d + 3) / Q
  change 1 < P at hPgt
  rcases hsys with ⟨hX, hY, hQS, hQD, hcommon, horient,
    hPQ, hcopRC, hRC, hCtwoR, hcopQS, hPlinear, hQlinear,
    hupperThree, h2D, houter⟩
  change P * R = Q * S at hcommon
  change R < C at hRC
  change C < 2 * R at hCtwoR
  change Nat.Coprime P Q at hPQ
  dsimp only [K5ExceptionalCancelledCofactorBranch]
  have hPpos : 0 < P := by omega
  have hRpos : 0 < R := by omega
  rcases houter with ho | ho
  · left
    refine ⟨ho.1, ?_⟩
    rcases ho.2 with ⟨hAT, hAE, hdet, hcommonA, hPA, hQA, hcopAT,
      hAlin, hAsq, hcombined⟩
    let A := canonicalOwnerCell data j 1
    let H := R / (A * Q)
    let U := (P * (C + R) - 1) / A ^ 2
    let V := (P * (C + 6 * R) + 1) / Q ^ 2
    change Nat.Coprime P A at hPA
    change Nat.Coprime Q A at hQA
    change A ^ 2 ∣ P * (C + R) - 1 at hAsq
    have hQsq : Q ^ 2 ∣ P * (C + 6 * R) + 1 := by
      rcases horient with hm | hm
      · exact hm.2.2
      · omega
    have hQdvdR : Q ∣ R := by
      apply hPQ.symm.dvd_of_dvd_mul_left
      rw [hcommon]
      exact dvd_mul_right Q S
    have hAdvdR : A ∣ R := by
      apply hPA.symm.dvd_of_dvd_mul_left
      rw [hcommonA]
      exact dvd_mul_right A ((n + j) / A)
    have hAQdvdR : A * Q ∣ R :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hQA.symm hAdvdR hQdvdR
    have hR : R = A * Q * H := by
      exact (Nat.mul_div_cancel' hAQdvdR).symm
    have hU : A ^ 2 * U = P * (C + R) - 1 :=
      Nat.mul_div_cancel' hAsq
    have hV : Q ^ 2 * V = P * (C + 6 * R) + 1 :=
      Nat.mul_div_cancel' hQsq
    have hcofactor :
        Q ^ 2 * V = A ^ 2 * U + 5 * P * A * Q * H + 2 := by
      rw [hU, hV]
      have hfive : 5 * P * A * Q * H = 5 * P * R := by
        rw [hR]
        ring
      rw [hfive]
      have hbase : 0 < P * (C + R) :=
        Nat.mul_pos hPpos (by omega)
      calc
        P * (C + 6 * R) + 1 = P * (C + R) + 5 * P * R + 1 := by ring
        _ = (P * (C + R) - 1) + 5 * P * R + 2 := by omega
    have hsum3 : C + R < 3 * R := by omega
    have hF1lt : P * (C + R) - 1 < 3 * P * R := by
      have hs := (Nat.mul_lt_mul_left hPpos).mpr hsum3
      have hb : 0 < P * (C + R) := Nat.mul_pos hPpos (by omega)
      calc
        P * (C + R) - 1 < P * (C + R) := Nat.sub_lt hb (by norm_num)
        _ < P * (3 * R) := hs
        _ = 3 * P * R := by ring
    have hApos : 0 < A := by
      dsimp [A]
      exact canonicalOwnerCell_pos data
    have hUbound : A * U < 3 * P * Q * H := by
      apply (Nat.mul_lt_mul_left hApos).mp
      calc
        A * (A * U) = A ^ 2 * U := by ring
        _ = P * (C + R) - 1 := hU
        _ < 3 * P * R := hF1lt
        _ = A * (3 * P * Q * H) := by rw [hR]; ring
    have hsum8 : C + 6 * R < 8 * R := by omega
    have hF2lt : P * (C + 6 * R) + 1 < 8 * P * R := by
      have hs := (Nat.mul_lt_mul_left hPpos).mpr hsum8
      have hsucc : C + 6 * R + 1 ≤ 8 * R := by omega
      calc
        P * (C + 6 * R) + 1 < P * (C + 6 * R + 1) := by
          rw [show P * (C + 6 * R + 1) = P * (C + 6 * R) + P by ring]
          omega
        _ ≤ P * (8 * R) := Nat.mul_le_mul_left P hsucc
        _ = 8 * P * R := by ring
    have hQpos : 0 < Q := by
      dsimp [Q]
      exact canonicalOwnerCell_pos data
    have hVbound : Q * V < 8 * P * A * H := by
      apply (Nat.mul_lt_mul_left hQpos).mp
      calc
        Q * (Q * V) = Q ^ 2 * V := by ring
        _ = P * (C + 6 * R) + 1 := hV
        _ < 8 * P * R := hF2lt
        _ = Q * (8 * P * A * H) := by rw [hR]; ring
    exact ⟨hR, hU, hV, hcofactor, hUbound, hVbound⟩

  · right
    refine ⟨ho.1, ?_⟩
    rcases ho.2 with ⟨hAT, hAE, hdet, hcommonA, hPA, hQA, hcopAT,
      hAlin, hAsq, hcombined⟩
    let A := canonicalOwnerCell data j 5
    let H := R / (A * Q)
    let U := (P * (C + R) + 1) / A ^ 2
    let V := (P * (C + 6 * R) - 1) / Q ^ 2
    change Nat.Coprime P A at hPA
    change Nat.Coprime Q A at hQA
    change A ^ 2 ∣ P * (C + R) + 1 at hAsq
    have hQsq : Q ^ 2 ∣ P * (C + 6 * R) - 1 := by
      rcases horient with hm | hm
      · omega
      · exact hm.2.2
    have hQdvdR : Q ∣ R := by
      apply hPQ.symm.dvd_of_dvd_mul_left
      rw [hcommon]
      exact dvd_mul_right Q S
    have hAdvdR : A ∣ R := by
      apply hPA.symm.dvd_of_dvd_mul_left
      rw [hcommonA]
      exact dvd_mul_right A ((n + j) / A)
    have hAQdvdR : A * Q ∣ R :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hQA.symm hAdvdR hQdvdR
    have hR : R = A * Q * H := by
      exact (Nat.mul_div_cancel' hAQdvdR).symm
    have hU : A ^ 2 * U = P * (C + R) + 1 :=
      Nat.mul_div_cancel' hAsq
    have hV : Q ^ 2 * V = P * (C + 6 * R) - 1 :=
      Nat.mul_div_cancel' hQsq
    have hcofactor :
        Q ^ 2 * V + 2 = A ^ 2 * U + 5 * P * A * Q * H := by
      rw [hU, hV]
      have hfive : 5 * P * A * Q * H = 5 * P * R := by
        rw [hR]
        ring
      rw [hfive]
      have hbase : 0 < P * (C + 6 * R) :=
        Nat.mul_pos hPpos (by omega)
      calc
        (P * (C + 6 * R) - 1) + 2 = P * (C + 6 * R) + 1 := by omega
        _ = P * (C + R) + 1 + 5 * P * R := by ring
    have hsum3 : C + R < 3 * R := by omega
    have hF1lt : P * (C + R) + 1 < 3 * P * R := by
      have hs := (Nat.mul_lt_mul_left hPpos).mpr hsum3
      have hsucc : C + R + 1 ≤ 3 * R := by omega
      calc
        P * (C + R) + 1 < P * (C + R + 1) := by
          rw [show P * (C + R + 1) = P * (C + R) + P by ring]
          omega
        _ ≤ P * (3 * R) := Nat.mul_le_mul_left P hsucc
        _ = 3 * P * R := by ring
    have hApos : 0 < A := by
      dsimp [A]
      exact canonicalOwnerCell_pos data
    have hUbound : A * U < 3 * P * Q * H := by
      apply (Nat.mul_lt_mul_left hApos).mp
      calc
        A * (A * U) = A ^ 2 * U := by ring
        _ = P * (C + R) + 1 := hU
        _ < 3 * P * R := hF1lt
        _ = A * (3 * P * Q * H) := by rw [hR]; ring
    have hsum8 : C + 6 * R < 8 * R := by omega
    have hF2lt : P * (C + 6 * R) - 1 < 8 * P * R := by
      have hs := (Nat.mul_lt_mul_left hPpos).mpr hsum8
      have hb : 0 < P * (C + 6 * R) := Nat.mul_pos hPpos (by omega)
      calc
        P * (C + 6 * R) - 1 < P * (C + 6 * R) :=
          Nat.sub_lt hb (by norm_num)
        _ < P * (8 * R) := hs
        _ = 8 * P * R := by ring
    have hQpos : 0 < Q := by
      dsimp [Q]
      exact canonicalOwnerCell_pos data
    have hVbound : Q * V < 8 * P * A * H := by
      apply (Nat.mul_lt_mul_left hQpos).mp
      calc
        Q * (Q * V) = Q ^ 2 * V := by ring
        _ = P * (C + 6 * R) - 1 := hV
        _ < 8 * P * R := hF2lt
        _ = Q * (8 * P * A * H) := by rw [hR]; ring
    exact ⟨hR, hU, hV, hcofactor, hUbound, hVbound⟩

/-- All five owner squares in the exceptional fully owned row, expressed in
the common primitive coordinates `P,R,C`. -/
def K5ExceptionalFiveOwnerPrimitiveBranch
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (j i : ℕ) : Prop :=
  let P := canonicalOwnerCell data j i
  let Q := canonicalOwnerCell data j 3
  let R := (n + j) / P
  let C := (n + d + i) / P
  (i = 2 ∧
    let A := canonicalOwnerCell data j 1
    let B := canonicalOwnerCell data j 4
    let W := canonicalOwnerCell data j 5
    let H := R / (A * Q)
    n + j = A * P * Q * B * W ∧ R = A * Q * B * W ∧ H = B * W ∧
      (((A : ℤ) ^ 2) ∣ (P : ℤ) * ((C : ℤ) + (R : ℤ)) - 1) ∧
      (((P : ℤ) ^ 2) ∣ (P : ℤ) * (4 * (R : ℤ) - (C : ℤ))) ∧
      (((Q : ℤ) ^ 2) ∣ (P : ℤ) * ((C : ℤ) + 6 * (R : ℤ)) + 1) ∧
      (((B : ℤ) ^ 2) ∣ (P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) - 2) ∧
      (((W : ℤ) ^ 2) ∣ (P : ℤ) * ((C : ℤ) + (R : ℤ)) + 3) ∧
      ((((n + j : ℕ) : ℤ) ^ 2) ∣
        ((P : ℤ) * ((C : ℤ) + (R : ℤ)) - 1) *
        ((P : ℤ) * (4 * (R : ℤ) - (C : ℤ))) *
        ((P : ℤ) * ((C : ℤ) + 6 * (R : ℤ)) + 1) *
        ((P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) - 2) *
        ((P : ℤ) * ((C : ℤ) + (R : ℤ)) + 3))) ∨
  (i = 4 ∧
    let A := canonicalOwnerCell data j 5
    let B := canonicalOwnerCell data j 2
    let W := canonicalOwnerCell data j 1
    let H := R / (A * Q)
    n + j = A * P * Q * B * W ∧ R = A * Q * B * W ∧ H = B * W ∧
      (((A : ℤ) ^ 2) ∣ (P : ℤ) * ((C : ℤ) + (R : ℤ)) + 1) ∧
      (((P : ℤ) ^ 2) ∣ (P : ℤ) * (4 * (R : ℤ) - (C : ℤ))) ∧
      (((Q : ℤ) ^ 2) ∣ (P : ℤ) * ((C : ℤ) + 6 * (R : ℤ)) - 1) ∧
      (((B : ℤ) ^ 2) ∣ (P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) + 2) ∧
      (((W : ℤ) ^ 2) ∣ (P : ℤ) * ((C : ℤ) + (R : ℤ)) - 3) ∧
      ((((n + j : ℕ) : ℤ) ^ 2) ∣
        ((P : ℤ) * ((C : ℤ) + (R : ℤ)) + 1) *
        ((P : ℤ) * (4 * (R : ℤ) - (C : ℤ))) *
        ((P : ℤ) * ((C : ℤ) + 6 * (R : ℤ)) - 1) *
        ((P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) + 2) *
        ((P : ℤ) * ((C : ℤ) + (R : ℤ)) - 3)))

private lemma five_owner_product_i2
    {n d t j : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hlower : canonicalLowerResidual data j = 1) :
    n + j = canonicalOwnerCell data j 1 * canonicalOwnerCell data j 2 *
      canonicalOwnerCell data j 3 * canonicalOwnerCell data j 4 *
      canonicalOwnerCell data j 5 := by
  calc
    n + j = canonicalOwnerRow data j := by
      rw [canonical_lower_term_factorization data, hlower, one_mul]
    _ = ∏ i' ∈ Finset.Icc 1 5, canonicalOwnerCell data j i' := by
      rw [canonicalOwner_row_cell_product data]
    _ = _ := by
      rw [show Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) by decide]
      norm_num
      ring

/-- The opaque cofactor `H` is exactly the product of the last two row owners,
and all five primitive owner-square congruences combine into one CRT product
divisor. -/
theorem k5_exceptional_five_owner_primitive_system
    {n d t i j : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hj : j = 2 ∨ j = 4)
    (hd : 5 ≤ d)
    (hcross : K5ExceptionalUnitCrossingConstraint data j i)
    (hstar : K5ExceptionalSquareStar data j i)
    (hsys : K5ExceptionalMiddlePrimitiveSystem data j i) :
    K5ExceptionalFiveOwnerPrimitiveBranch data j i := by
  dsimp only [K5ExceptionalMiddlePrimitiveSystem] at hsys
  let P := canonicalOwnerCell data j i
  let Q := canonicalOwnerCell data j 3
  let R := (n + j) / P
  let C := (n + d + i) / P
  let S := (n + j) / Q
  let D := (n + d + 3) / Q
  rcases hsys with ⟨hX, hY, hQS, hQD, hcommon, horient,
    hPQ, hcopRC, hRC, hCtwoR, hcopQS, hPlinear, hQlinear,
    hupperThree, h2D, houter⟩
  change n + j = P * R at hX
  change n + d + i = P * C at hY
  dsimp only [K5ExceptionalFiveOwnerPrimitiveBranch]
  have hPpos : 0 < P := by dsimp [P]; exact canonicalOwnerCell_pos data
  rcases houter with ho | ho
  · left
    have hi2 : i = 2 := ho.1
    subst i
    refine ⟨rfl, ?_⟩
    let A := canonicalOwnerCell data j 1
    let B := canonicalOwnerCell data j 4
    let W := canonicalOwnerCell data j 5
    let H := R / (A * Q)
    rcases ho.2 with ⟨hAT, hAE, hdet, hcommonA, hPA, hQA, hcopAT,
      hAlin, hAsqNat, hcombined⟩
    have hprod := five_owner_product_i2 data hcross.2.1
    have hrow : n + j = A * P * Q * B * W := by
      simpa [A, P, Q, B, W] using hprod
    have hR : R = A * Q * B * W := by
      apply Nat.mul_left_cancel hPpos
      rw [← hX, hrow]
      ring
    have hH : H = B * W := by
      dsimp [H]
      rw [hR]
      have hAQpos : 0 < A * Q := mul_pos
        (canonicalOwnerCell_pos data) (canonicalOwnerCell_pos data)
      rw [show A * Q * B * W = (A * Q) * (B * W) by ring]
      exact Nat.mul_div_cancel_left (B * W) hAQpos
    have hA := hstar.1 1 (by norm_num)
    have hAdef : k5ExceptionalRowSquareDefect n d j 1 =
        (P : ℤ) * ((C : ℤ) + (R : ℤ)) - 1 := by
      simp only [k5ExceptionalRowSquareDefect]
      have hd1 : ((d + 1 - j : ℕ) : ℤ) =
          ((n + d + 1 : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by
        rcases hj with rfl | rfl <;> omega
      have hxz : ((n + j : ℕ) : ℤ) = (P : ℤ) * R := by exact_mod_cast hX
      have hyz : ((n + d + 1 : ℕ) : ℤ) = (P : ℤ) * C - 1 := by
        have hy0 : ((n + d + 2 : ℕ) : ℤ) = (P : ℤ) * C := by exact_mod_cast hY
        omega
      rw [hd1, hxz, hyz]
      push_cast at hxz
      linear_combination 2 * hxz
    rw [hAdef] at hA
    change ((A : ℤ) ^ 2) ∣ _ at hA
    have hP := hstar.1 2 (by norm_num)
    have hPdef : k5ExceptionalRowSquareDefect n d j 2 =
        (P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) := by
      simp only [k5ExceptionalRowSquareDefect]
      have hd2 : ((d + 2 - j : ℕ) : ℤ) =
          ((n + d + 2 : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by
        rcases hj with rfl | rfl <;> omega
      have hxz : ((n + j : ℕ) : ℤ) = (P : ℤ) * R := by exact_mod_cast hX
      have hyz : ((n + d + 2 : ℕ) : ℤ) = (P : ℤ) * C := by exact_mod_cast hY
      rw [hd2, hxz, hyz]
      push_cast at hxz
      linear_combination 3 * hxz
    rw [hPdef] at hP
    have hQNat : Q ^ 2 ∣ P * (C + 6 * R) + 1 := by
      rcases horient with hh | hh
      · exact hh.2.2
      · omega
    have hQ : ((Q : ℤ) ^ 2) ∣
        (P : ℤ) * ((C : ℤ) + 6 * (R : ℤ)) + 1 := by exact_mod_cast hQNat
    have hY4 : n + d + 4 = P * C + 2 := by omega
    have hY5 : n + d + 5 = P * C + 3 := by omega
    have hBraw := hstar.1 4 (by norm_num)
    have hWraw := hstar.1 5 (by norm_num)
    have hB : ((B : ℤ) ^ 2) ∣
        (P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) - 2 := by
      have hdef : k5ExceptionalRowSquareDefect n d j 4 =
          (P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) - 2 := by
        simp only [k5ExceptionalRowSquareDefect]
        have hD4 : ((d + 4 - j : ℕ) : ℤ) =
            ((n + d + 4 : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by
          rcases hj with rfl | rfl <;> omega
        have hxz : ((n + j : ℕ) : ℤ) = (P : ℤ) * (R : ℤ) := by exact_mod_cast hX
        have hyz : ((n + d + 4 : ℕ) : ℤ) = (P : ℤ) * (C : ℤ) + 2 := by exact_mod_cast hY4
        rw [hD4, hxz, hyz]
        push_cast at hxz
        linear_combination 3 * hxz
      rw [hdef] at hBraw
      exact hBraw
    have hW : ((W : ℤ) ^ 2) ∣
        (P : ℤ) * ((C : ℤ) + (R : ℤ)) + 3 := by
      have hdef : k5ExceptionalRowSquareDefect n d j 5 =
          (P : ℤ) * ((C : ℤ) + (R : ℤ)) + 3 := by
        simp only [k5ExceptionalRowSquareDefect]
        have hD5 : ((d + 5 - j : ℕ) : ℤ) =
            ((n + d + 5 : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by
          rcases hj with rfl | rfl <;> omega
        have hxz : ((n + j : ℕ) : ℤ) = (P : ℤ) * (R : ℤ) := by exact_mod_cast hX
        have hyz : ((n + d + 5 : ℕ) : ℤ) = (P : ℤ) * (C : ℤ) + 3 := by exact_mod_cast hY5
        rw [hD5, hxz, hyz]
        push_cast at hxz
        linear_combination 2 * hxz
      rw [hdef] at hWraw
      exact hWraw
    have hall := mul_dvd_mul hA (mul_dvd_mul hP
      (mul_dvd_mul hQ (mul_dvd_mul hB hW)))
    have hcrt : (((n + j : ℕ) : ℤ) ^ 2) ∣
        ((P : ℤ) * ((C : ℤ) + (R : ℤ)) - 1) *
        ((P : ℤ) * (4 * (R : ℤ) - (C : ℤ))) *
        ((P : ℤ) * ((C : ℤ) + 6 * (R : ℤ)) + 1) *
        ((P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) - 2) *
        ((P : ℤ) * ((C : ℤ) + (R : ℤ)) + 3) := by
      convert hall using 1
      · rw [hrow]
        push_cast
        ring
      · ring
    exact ⟨hrow, hR, hH, hA, hP, hQ, hB, hW, hcrt⟩

  · right
    have hi4 : i = 4 := ho.1
    subst i
    refine ⟨rfl, ?_⟩
    let A := canonicalOwnerCell data j 5
    let B := canonicalOwnerCell data j 2
    let W := canonicalOwnerCell data j 1
    let H := R / (A * Q)
    rcases ho.2 with ⟨hAT, hAE, hdet, hcommonA, hPA, hQA, hcopAT,
      hAlin, hAsqNat, hcombined⟩
    have hprod0 := five_owner_product_i2 data hcross.2.1
    have hrow : n + j = A * P * Q * B * W := by
      calc
        n + j = canonicalOwnerCell data j 1 * canonicalOwnerCell data j 2 *
            canonicalOwnerCell data j 3 * canonicalOwnerCell data j 4 *
            canonicalOwnerCell data j 5 := hprod0
        _ = A * P * Q * B * W := by dsimp [A, P, Q, B, W]; ring
    have hR : R = A * Q * B * W := by
      apply Nat.mul_left_cancel hPpos
      rw [← hX, hrow]
      ring
    have hH : H = B * W := by
      dsimp [H]
      rw [hR]
      have hAQpos : 0 < A * Q := mul_pos
        (canonicalOwnerCell_pos data) (canonicalOwnerCell_pos data)
      rw [show A * Q * B * W = (A * Q) * (B * W) by ring]
      exact Nat.mul_div_cancel_left (B * W) hAQpos
    have hA := hstar.1 5 (by norm_num)
    have hAdef : k5ExceptionalRowSquareDefect n d j 5 =
        (P : ℤ) * ((C : ℤ) + (R : ℤ)) + 1 := by
      simp only [k5ExceptionalRowSquareDefect]
      have hd5 : ((d + 5 - j : ℕ) : ℤ) =
          ((n + d + 5 : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by
        rcases hj with rfl | rfl <;> omega
      have hxz : ((n + j : ℕ) : ℤ) = (P : ℤ) * R := by exact_mod_cast hX
      have hyz : ((n + d + 5 : ℕ) : ℤ) = (P : ℤ) * C + 1 := by
        have hy0 : ((n + d + 4 : ℕ) : ℤ) = (P : ℤ) * C := by exact_mod_cast hY
        omega
      rw [hd5, hxz, hyz]
      push_cast at hxz
      linear_combination 2 * hxz
    rw [hAdef] at hA
    change ((A : ℤ) ^ 2) ∣ _ at hA
    have hP := hstar.1 4 (by norm_num)
    have hPdef : k5ExceptionalRowSquareDefect n d j 4 =
        (P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) := by
      simp only [k5ExceptionalRowSquareDefect]
      have hd4 : ((d + 4 - j : ℕ) : ℤ) =
          ((n + d + 4 : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by
        rcases hj with rfl | rfl <;> omega
      have hxz : ((n + j : ℕ) : ℤ) = (P : ℤ) * R := by exact_mod_cast hX
      have hyz : ((n + d + 4 : ℕ) : ℤ) = (P : ℤ) * C := by exact_mod_cast hY
      rw [hd4, hxz, hyz]
      push_cast at hxz
      linear_combination 3 * hxz
    rw [hPdef] at hP
    have hQNat : Q ^ 2 ∣ P * (C + 6 * R) - 1 := by
      rcases horient with hh | hh
      · omega
      · exact hh.2.2
    have hQraw := hstar.1 3 (by norm_num)
    have hQdef : k5ExceptionalRowSquareDefect n d j 3 =
        (P : ℤ) * ((C : ℤ) + 6 * (R : ℤ)) - 1 := by
      simp only [k5ExceptionalRowSquareDefect]
      have hd3 : ((d + 3 - j : ℕ) : ℤ) =
          ((n + d + 3 : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by
        rcases hj with rfl | rfl <;> omega
      have hxz : ((n + j : ℕ) : ℤ) = (P : ℤ) * R := by exact_mod_cast hX
      have hyz : ((n + d + 3 : ℕ) : ℤ) = (P : ℤ) * C - 1 := by omega
      rw [hd3, hxz, hyz]
      push_cast at hxz
      linear_combination 7 * hxz
    rw [hQdef] at hQraw
    have hQ : ((Q : ℤ) ^ 2) ∣
        (P : ℤ) * ((C : ℤ) + 6 * (R : ℤ)) - 1 := hQraw
    have hy0 : ((n + d + 4 : ℕ) : ℤ) = (P : ℤ) * C := by exact_mod_cast hY
    have hY2z : ((n + d + 2 : ℕ) : ℤ) = (P : ℤ) * (C : ℤ) - 2 := by omega
    have hY1z : ((n + d + 1 : ℕ) : ℤ) = (P : ℤ) * (C : ℤ) - 3 := by omega
    have hBraw := hstar.1 2 (by norm_num)
    have hWraw := hstar.1 1 (by norm_num)
    have hB : ((B : ℤ) ^ 2) ∣
        (P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) + 2 := by
      have hdef : k5ExceptionalRowSquareDefect n d j 2 =
          (P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) + 2 := by
        simp only [k5ExceptionalRowSquareDefect]
        have hD2 : ((d + 2 - j : ℕ) : ℤ) =
            ((n + d + 2 : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by
          rcases hj with rfl | rfl <;> omega
        have hxz : ((n + j : ℕ) : ℤ) = (P : ℤ) * (R : ℤ) := by exact_mod_cast hX
        rw [hD2, hxz, hY2z]
        push_cast at hxz
        linear_combination 3 * hxz
      rw [hdef] at hBraw
      exact hBraw
    have hW : ((W : ℤ) ^ 2) ∣
        (P : ℤ) * ((C : ℤ) + (R : ℤ)) - 3 := by
      have hdef : k5ExceptionalRowSquareDefect n d j 1 =
          (P : ℤ) * ((C : ℤ) + (R : ℤ)) - 3 := by
        simp only [k5ExceptionalRowSquareDefect]
        have hD1 : ((d + 1 - j : ℕ) : ℤ) =
            ((n + d + 1 : ℕ) : ℤ) - ((n + j : ℕ) : ℤ) := by
          rcases hj with rfl | rfl <;> omega
        have hxz : ((n + j : ℕ) : ℤ) = (P : ℤ) * (R : ℤ) := by exact_mod_cast hX
        rw [hD1, hxz, hY1z]
        push_cast at hxz
        linear_combination 2 * hxz
      rw [hdef] at hWraw
      exact hWraw
    have hall := mul_dvd_mul hA (mul_dvd_mul hP
      (mul_dvd_mul hQ (mul_dvd_mul hB hW)))
    have hcrt : (((n + j : ℕ) : ℤ) ^ 2) ∣
        ((P : ℤ) * ((C : ℤ) + (R : ℤ)) + 1) *
        ((P : ℤ) * (4 * (R : ℤ) - (C : ℤ))) *
        ((P : ℤ) * ((C : ℤ) + 6 * (R : ℤ)) - 1) *
        ((P : ℤ) * (4 * (R : ℤ) - (C : ℤ)) + 2) *
        ((P : ℤ) * ((C : ℤ) + (R : ℤ)) - 3) := by
      convert hall using 1
      · rw [hrow]
        push_cast
        ring
      · ring
    exact ⟨hrow, hR, hH, hA, hP, hQ, hB, hW, hcrt⟩

/-- Cross-allocation engine for the five primitive targets.  If an owner is
coprime to six, divides the row scale `X`, and divides its designated target
`D`, then any other target which is an integral linear combination of `D` and
`X` up to a remainder in `{±1,±2,±3,±4}` is coprime to that owner. -/
theorem g24_small_remainder_cross_coprime
    {z : ℕ} {D X T c a b : ℤ}
    (hcop : Nat.Coprime z 6)
    (hc : c.natAbs ∣ 36)
    (hzD : (z : ℤ) ∣ D)
    (hzX : (z : ℤ) ∣ X)
    (hrel : T = a * D + b * X + c) :
    IsCoprime (z : ℤ) T := by
  have hzcNat : Nat.Coprime z c.natAbs := by
    apply Nat.Coprime.coprime_dvd_right hc
    simpa using hcop.pow_right 2
  have hzc : IsCoprime (z : ℤ) c := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hzcNat
  rcases hzD with ⟨d, hd⟩
  rcases hzX with ⟨x, hx⟩
  rcases hzc with ⟨u, v, huv⟩
  refine ⟨u - v * (a * d + b * x), v, ?_⟩
  rw [hd, hx] at hrel
  calc
    (u - v * (a * d + b * x)) * (z : ℤ) + v * T =
        u * (z : ℤ) + v * c := by rw [hrel]; ring
    _ = 1 := huv

/-- The exact five-target remainder table in the unit-column-two orientation.
Each row gives the four remainders of the non-designated targets modulo the
designated target and the common row scale. -/
theorem g24_i2_five_target_remainder_table (X u : ℤ) :
    let A := u - 1
    let P := 5 * X - u
    let Q := u + 5 * X + 1
    let B := 5 * X - u - 2
    let W := u + 3
    (P = -A + 5 * X - 1 ∧ Q = A + 5 * X + 2 ∧
      B = -A + 5 * X - 3 ∧ W = A + 4) ∧
    (A = -P + 5 * X - 1 ∧ Q = -P + 10 * X + 1 ∧
      B = P - 2 ∧ W = -P + 5 * X + 3) ∧
    (A = Q - 5 * X - 2 ∧ P = -Q + 10 * X + 1 ∧
      B = -Q + 10 * X - 1 ∧ W = Q - 5 * X + 2) ∧
    (A = -B + 5 * X - 3 ∧ P = B + 2 ∧
      Q = -B + 10 * X - 1 ∧ W = -B + 5 * X + 1) ∧
    (A = W - 4 ∧ P = -W + 5 * X + 3 ∧
      Q = W + 5 * X - 2 ∧ B = -W + 5 * X + 1) := by
  dsimp only
  repeat' apply And.intro
  all_goals ring

/-- The corresponding exact remainder table in the unit-column-four
orientation.  Again every cross remainder has absolute value at most four. -/
theorem g24_i4_five_target_remainder_table (X u : ℤ) :
    let A := u + 1
    let P := 5 * X - u
    let Q := u + 5 * X - 1
    let B := 5 * X - u + 2
    let W := u - 3
    (P = -A + 5 * X + 1 ∧ Q = A + 5 * X - 2 ∧
      B = -A + 5 * X + 3 ∧ W = A - 4) ∧
    (A = -P + 5 * X + 1 ∧ Q = -P + 10 * X - 1 ∧
      B = P + 2 ∧ W = -P + 5 * X - 3) ∧
    (A = Q - 5 * X + 2 ∧ P = -Q + 10 * X - 1 ∧
      B = -Q + 10 * X + 1 ∧ W = Q - 5 * X - 2) ∧
    (A = -B + 5 * X + 3 ∧ P = B - 2 ∧
      Q = -B + 10 * X + 1 ∧ W = -B + 5 * X - 1) ∧
    (A = W + 4 ∧ P = -W + 5 * X - 3 ∧
      Q = W + 5 * X + 2 ∧ B = -W + 5 * X - 1) := by
  dsimp only
  repeat' apply And.intro
  all_goals ring

/-- Dividing five targets by their designated owner squares gives an exact
product identity.  This is stated over `ℤ`, so it remains valid for the signed
primitive targets without introducing absolute values or truncating
subtraction. -/
theorem five_designated_square_quotient_product_identity
    {z₁ z₂ z₃ z₄ z₅ T₁ T₂ T₃ T₄ T₅ X : ℤ}
    (hX : X = z₁ * z₂ * z₃ * z₄ * z₅)
    (h₁ : z₁ ^ 2 ∣ T₁) (h₂ : z₂ ^ 2 ∣ T₂)
    (h₃ : z₃ ^ 2 ∣ T₃) (h₄ : z₄ ^ 2 ∣ T₄)
    (h₅ : z₅ ^ 2 ∣ T₅) :
    ∃ q₁ q₂ q₃ q₄ q₅ : ℤ,
      T₁ = z₁ ^ 2 * q₁ ∧ T₂ = z₂ ^ 2 * q₂ ∧
      T₃ = z₃ ^ 2 * q₃ ∧ T₄ = z₄ ^ 2 * q₄ ∧
      T₅ = z₅ ^ 2 * q₅ ∧
      T₁ * T₂ * T₃ * T₄ * T₅ =
        X ^ 2 * (q₁ * q₂ * q₃ * q₄ * q₅) := by
  rcases h₁ with ⟨q₁, hq₁⟩
  rcases h₂ with ⟨q₂, hq₂⟩
  rcases h₃ with ⟨q₃, hq₃⟩
  rcases h₄ with ⟨q₄, hq₄⟩
  rcases h₅ with ⟨q₅, hq₅⟩
  refine ⟨q₁, q₂, q₃, q₄, q₅, hq₁, hq₂, hq₃, hq₄, hq₅, ?_⟩
  rw [hq₁, hq₂, hq₃, hq₄, hq₅, hX]
  ring

/-- A designated owner is coprime to `6`, so removing its square preserves
divisibility by every prime divisor of six. -/
theorem small_prime_dvd_designated_square_quotient_iff
    {z p : ℕ} {T q : ℤ}
    (hcop : Nat.Coprime z 6)
    (hp : p ∣ 6)
    (hT : T = (z : ℤ) ^ 2 * q) :
    ((p : ℤ) ∣ T ↔ (p : ℤ) ∣ q) := by
  have hzp : Nat.Coprime z p := hcop.coprime_dvd_right hp
  have hpzSqNat : Nat.Coprime p (z ^ 2) := (hzp.pow_left 2).symm
  have hpzSq : IsCoprime (p : ℤ) ((z : ℤ) ^ 2) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hpzSqNat
  constructor
  · intro hdvd
    rw [hT] at hdvd
    exact hpzSq.dvd_of_dvd_mul_left hdvd
  · intro hdvd
    rw [hT]
    exact dvd_mul_of_dvd_right hdvd _

/-- Explicit `2`/`3` specialization used by the exceptional quotient
allocation.  No owner contributes either prime; both valuations are carried
entirely by its signed square quotient. -/
theorem two_three_allocation_to_designated_quotient
    {z : ℕ} {T q : ℤ}
    (hcop : Nat.Coprime z 6)
    (hT : T = (z : ℤ) ^ 2 * q) :
    (((2 : ℤ) ∣ T ↔ (2 : ℤ) ∣ q) ∧
      ((3 : ℤ) ∣ T ↔ (3 : ℤ) ∣ q)) := by
  exact ⟨small_prime_dvd_designated_square_quotient_iff
      hcop (by norm_num) hT,
    small_prime_dvd_designated_square_quotient_iff
      hcop (by norm_num) hT⟩

private theorem k5_exceptional_crossing_constraint_square_star
    {n d t i j : ℕ} (data : CanonicalOwnerData 5 n d t)
    (hi : i = 2 ∨ i = 4)
    (hj : j = 2 ∨ j = 4)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hd : 5 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hupperProfile : K5ExceptionalResidualProfile
      (canonicalUpperResidual data))
    (hcross : K5ExceptionalUnitCrossingConstraint data j i) :
    K5ExceptionalSquareStar data j i := by
  have hupperCop := k5_exceptional_unit_upper_terms_coprime_six
    data ht hfour hupperProfile
  have hyCop : Nat.Coprime (n + d + i) 6 := by
    rcases hi with rfl | rfl
    · exact hupperCop.1 hcross.2.2.1
    · exact hupperCop.2 hcross.2.2.1
  constructor
  · apply k5_even_fullyOwned_row_square_defect_system hj hd
      (fun i' => canonicalOwnerCell data j i')
    · exact fun i' hi' => (hcross.2.2.2.2.2.1 i' hi').2.1
    · exact fun _ _ => canonicalOwnerCell_dvd_lower data
    · exact fun _ _ => dvd_trans (canonicalOwnerCell_dvd_upper data)
        (upperTermAfterFour_dvd_original hfour)
    · exact heq
  · apply k5_even_fullyOwned_column_square_defect_system hi
      (fun j' => canonicalOwnerCell data j' i)
    · exact fun _ _ => hyCop.of_dvd_left
        (dvd_trans (canonicalOwnerCell_dvd_upper data)
          (upperTermAfterFour_dvd_original hfour))
    · exact fun _ _ => canonicalOwnerCell_dvd_lower data
    · exact fun _ _ => dvd_trans (canonicalOwnerCell_dvd_upper data)
        (upperTermAfterFour_dvd_original hfour)
    · exact heq

/-- Every simultaneous exceptional profile enters one of four explicit
two-owner primitive systems.  Together with the exact two-by-six residual CRT
classification above, this equips each of the twelve classes with the second
independent middle-owner congruence and the determinant-one coupling. -/
theorem k5_exceptional_middle_primitive_dispatch
    {n d t : ℕ} (data : CanonicalOwnerData 5 n d t)
    (ht : t ∈ Finset.Icc 1 5)
    (hfour : 4 ∣ n + d + t)
    (hblocks : upperBlockAfterFour 5 n d t = blockProduct 5 n)
    (htail : 10 ^ 1000 ≤ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hlower : K5ExceptionalResidualProfile (canonicalLowerResidual data))
    (hupper : K5ExceptionalResidualProfile (canonicalUpperResidual data)) :
    (d % 6 = 0 ∧ K5ExceptionalMiddlePrimitiveSystem data 2 2) ∨
      (d % 6 = 2 ∧ K5ExceptionalMiddlePrimitiveSystem data 2 4) ∨
      (d % 6 = 4 ∧ K5ExceptionalMiddlePrimitiveSystem data 4 2) ∨
      (d % 6 = 0 ∧ K5ExceptionalMiddlePrimitiveSystem data 4 4) := by
  have hd : 5 ≤ d := by
    have hbase : 5 ≤ 10 ^ 1000 := by
      calc
        5 ≤ 10 ^ 1 := by norm_num
        _ ≤ 10 ^ 1000 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact hbase.trans htail
  have hcases := k5_exceptional_exact_unit_crossing_constraints
    data ht hfour hblocks htail heq hlower hupper
  have hupperThree : canonicalUpperResidual data 3 = 2 := by
    have htwos := k5_exceptional_upper_twos_eq_odd_positions
      data hfour hupper
    have hm : 3 ∈ (Finset.Icc 1 5).filter
        (fun r => canonicalUpperResidual data r = 2) := by
      rw [htwos]
      simp
    exact (Finset.mem_filter.mp hm).2
  rcases hcases with hc | hc | hc | hc
  · left
    refine ⟨hc.1, k5_exceptional_crossing_middle_primitive_system
      data (by left; rfl) (by left; rfl) hfour hd heq hc.2 hupperThree ?_⟩
    exact k5_exceptional_crossing_constraint_square_star data
      (by left; rfl) (by left; rfl) ht hfour hd heq hupper hc.2
  · right; left
    refine ⟨hc.1, k5_exceptional_crossing_middle_primitive_system
      data (by right; rfl) (by left; rfl) hfour hd heq hc.2 hupperThree ?_⟩
    exact k5_exceptional_crossing_constraint_square_star data
      (by right; rfl) (by left; rfl) ht hfour hd heq hupper hc.2
  · right; right; left
    refine ⟨hc.1, k5_exceptional_crossing_middle_primitive_system
      data (by left; rfl) (by right; rfl) hfour hd heq hc.2 hupperThree ?_⟩
    exact k5_exceptional_crossing_constraint_square_star data
      (by left; rfl) (by right; rfl) ht hfour hd heq hupper hc.2
  · right; right; right
    refine ⟨hc.1, k5_exceptional_crossing_middle_primitive_system
      data (by right; rfl) (by right; rfl) hfour hd heq hc.2 hupperThree ?_⟩
    exact k5_exceptional_crossing_constraint_square_star data
      (by right; rfl) (by right; rfl) ht hfour hd heq hupper hc.2

end Erdos686Variant
end Erdos686
