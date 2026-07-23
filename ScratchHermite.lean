import ErdosProblems.Erdos686NormalizedMatching
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

#check Submodule.nontrivial_iff_ne_bot
#check Submodule.exists_mem_ne_zero_of_ne_bot
#check LinearMap.ker_ne_bot_of_finrank_lt

namespace Erdos686
namespace Erdos686Variant

abbrev SquareHermiteCoeffs (m : ℕ) :=
  (Fin (m + 1) → ℚ) × (Fin m → ℚ)

def squareHermiteUEval {m : ℕ} (z : SquareHermiteCoeffs m) (t : ℚ) : ℚ :=
  ∑ r : Fin (m + 1), z.1 r * t ^ (r : ℕ)

def squareHermiteVEval {m : ℕ} (z : SquareHermiteCoeffs m) (t : ℚ) : ℚ :=
  ∑ r : Fin m, z.2 r * t ^ (r : ℕ)

def squareHermiteUDerivEval {m : ℕ} (z : SquareHermiteCoeffs m) (t : ℚ) : ℚ :=
  ∑ r : Fin (m + 1), (r : ℚ) * z.1 r * t ^ ((r : ℕ) - 1)

def squareHermiteVDerivEval {m : ℕ} (z : SquareHermiteCoeffs m) (t : ℚ) : ℚ :=
  ∑ r : Fin m, (r : ℚ) * z.2 r * t ^ ((r : ℕ) - 1)

@[simp] theorem squareHermiteUEval_add {m : ℕ}
    (z w : SquareHermiteCoeffs m) (t : ℚ) :
    squareHermiteUEval (z + w) t =
      squareHermiteUEval z t + squareHermiteUEval w t := by
  simp [squareHermiteUEval, Finset.sum_add_distrib, add_mul]

@[simp] theorem squareHermiteVEval_add {m : ℕ}
    (z w : SquareHermiteCoeffs m) (t : ℚ) :
    squareHermiteVEval (z + w) t =
      squareHermiteVEval z t + squareHermiteVEval w t := by
  simp [squareHermiteVEval, Finset.sum_add_distrib, add_mul]

@[simp] theorem squareHermiteUDerivEval_add {m : ℕ}
    (z w : SquareHermiteCoeffs m) (t : ℚ) :
    squareHermiteUDerivEval (z + w) t =
      squareHermiteUDerivEval z t + squareHermiteUDerivEval w t := by
  simp only [squareHermiteUDerivEval, Prod.fst_add, Pi.add_apply]
  calc
    (∑ r : Fin (m + 1), (r : ℚ) * (z.1 r + w.1 r) *
        t ^ ((r : ℕ) - 1)) =
        ∑ r : Fin (m + 1),
          ((r : ℚ) * z.1 r * t ^ ((r : ℕ) - 1) +
            (r : ℚ) * w.1 r * t ^ ((r : ℕ) - 1)) := by
              apply Finset.sum_congr rfl
              intro r _
              ring
    _ = _ := Finset.sum_add_distrib

@[simp] theorem squareHermiteVDerivEval_add {m : ℕ}
    (z w : SquareHermiteCoeffs m) (t : ℚ) :
    squareHermiteVDerivEval (z + w) t =
      squareHermiteVDerivEval z t + squareHermiteVDerivEval w t := by
  simp only [squareHermiteVDerivEval, Prod.snd_add, Pi.add_apply]
  calc
    (∑ r : Fin m, (r : ℚ) * (z.2 r + w.2 r) *
        t ^ ((r : ℕ) - 1)) =
        ∑ r : Fin m,
          ((r : ℚ) * z.2 r * t ^ ((r : ℕ) - 1) +
            (r : ℚ) * w.2 r * t ^ ((r : ℕ) - 1)) := by
              apply Finset.sum_congr rfl
              intro r _
              ring
    _ = _ := Finset.sum_add_distrib

@[simp] theorem squareHermiteUEval_smul {m : ℕ}
    (c : ℚ) (z : SquareHermiteCoeffs m) (t : ℚ) :
    squareHermiteUEval (c • z) t = c * squareHermiteUEval z t := by
  simp [squareHermiteUEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

@[simp] theorem squareHermiteVEval_smul {m : ℕ}
    (c : ℚ) (z : SquareHermiteCoeffs m) (t : ℚ) :
    squareHermiteVEval (c • z) t = c * squareHermiteVEval z t := by
  simp [squareHermiteVEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

@[simp] theorem squareHermiteUDerivEval_smul {m : ℕ}
    (c : ℚ) (z : SquareHermiteCoeffs m) (t : ℚ) :
    squareHermiteUDerivEval (c • z) t =
      c * squareHermiteUDerivEval z t := by
  simp [squareHermiteUDerivEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

@[simp] theorem squareHermiteVDerivEval_smul {m : ℕ}
    (c : ℚ) (z : SquareHermiteCoeffs m) (t : ℚ) :
    squareHermiteVDerivEval (c • z) t =
      c * squareHermiteVDerivEval z t := by
  simp [squareHermiteVDerivEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

def squareHermiteLinearMap
    (m : ℕ) (node rho alpha beta : Fin m → ℚ) :
    SquareHermiteCoeffs m →ₗ[ℚ] ((Fin m → ℚ) × (Fin m → ℚ)) where
  toFun z :=
    (fun ν =>
      squareHermiteUEval z (node ν) -
        rho ν * squareHermiteVEval z (node ν),
     fun ν =>
      beta ν *
          (squareHermiteUDerivEval z (node ν) -
            rho ν * squareHermiteVDerivEval z (node ν)) -
        alpha ν * squareHermiteVEval z (node ν))
  map_add' z w := by
    ext ν <;> simp <;> ring
  map_smul' c z := by
    ext ν <;> simp <;> ring

theorem scratch_squareHermite_kernel_exists
    (m : ℕ) (node rho alpha beta : Fin m → ℚ) :
    ∃ z : SquareHermiteCoeffs m, z ≠ 0 ∧
      (∀ ν,
        squareHermiteUEval z (node ν) =
          rho ν * squareHermiteVEval z (node ν)) ∧
      (∀ ν,
        beta ν *
            (squareHermiteUDerivEval z (node ν) -
              rho ν * squareHermiteVDerivEval z (node ν)) =
          alpha ν * squareHermiteVEval z (node ν)) := by
  let f := squareHermiteLinearMap m node rho alpha beta
  have hdim :
      Module.finrank ℚ ((Fin m → ℚ) × (Fin m → ℚ)) <
        Module.finrank ℚ (SquareHermiteCoeffs m) := by
    simp [SquareHermiteCoeffs]
  have hker : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨z, hzmem, hz0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨z, hz0, ?_, ?_⟩
  · intro ν
    have hz := LinearMap.mem_ker.mp hzmem
    have hzν := congrArg (fun w => w.1 ν) hz
    simp [f, squareHermiteLinearMap] at hzν
    linarith
  · intro ν
    have hz := LinearMap.mem_ker.mp hzmem
    have hzν := congrArg (fun w => w.2 ν) hz
    simp [f, squareHermiteLinearMap] at hzν
    linarith

abbrev SquareHermiteIntCoeffs (m : ℕ) :=
  (Fin (m + 1) → ℤ) × (Fin m → ℤ)

def squareHermiteIntUEval {m : ℕ}
    (z : SquareHermiteIntCoeffs m) (t : ℤ) : ℤ :=
  ∑ r : Fin (m + 1), z.1 r * t ^ (r : ℕ)

def squareHermiteIntVEval {m : ℕ}
    (z : SquareHermiteIntCoeffs m) (t : ℤ) : ℤ :=
  ∑ r : Fin m, z.2 r * t ^ (r : ℕ)

def squareHermiteIntUDerivEval {m : ℕ}
    (z : SquareHermiteIntCoeffs m) (t : ℤ) : ℤ :=
  ∑ r : Fin (m + 1), (r : ℤ) * z.1 r * t ^ ((r : ℕ) - 1)

def squareHermiteIntVDerivEval {m : ℕ}
    (z : SquareHermiteIntCoeffs m) (t : ℤ) : ℤ :=
  ∑ r : Fin m, (r : ℤ) * z.2 r * t ^ ((r : ℕ) - 1)

def squareHermiteClearRat (D : ℕ) (q : ℚ) : ℤ :=
  q.num * (D / q.den : ℕ)

private theorem squareHermiteClearRat_cast
    {D : ℕ} {q : ℚ} (h : q.den ∣ D) :
    (squareHermiteClearRat D q : ℚ) = (D : ℚ) * q := by
  obtain ⟨t, rfl⟩ := h
  calc
    (squareHermiteClearRat (q.den * t) q : ℚ) =
        ((q.den * t : ℕ) : ℚ) *
          ((q.num : ℚ) / (q.den : ℚ)) := by
            simp only [squareHermiteClearRat]
            rw [Nat.mul_div_right t q.den_pos]
            push_cast
            field_simp [q.den_nz]
    _ = ((q.den * t : ℕ) : ℚ) * q := by rw [q.num_div_den]

def squareHermiteCommonDenom {m : ℕ}
    (z : SquareHermiteCoeffs m) : ℕ :=
  (∏ r : Fin (m + 1), (z.1 r).den) *
    ∏ r : Fin m, (z.2 r).den

def squareHermiteClearCoeffs {m : ℕ}
    (z : SquareHermiteCoeffs m) : SquareHermiteIntCoeffs m :=
  (fun r => squareHermiteClearRat (squareHermiteCommonDenom z) (z.1 r),
   fun r => squareHermiteClearRat (squareHermiteCommonDenom z) (z.2 r))

private theorem squareHermite_den_dvd_common_left {m : ℕ}
    (z : SquareHermiteCoeffs m) (r : Fin (m + 1)) :
    (z.1 r).den ∣ squareHermiteCommonDenom z := by
  apply dvd_trans
    (Finset.dvd_prod_of_mem (fun s : Fin (m + 1) => (z.1 s).den)
      (Finset.mem_univ r))
  exact dvd_mul_right _ _

private theorem squareHermite_den_dvd_common_right {m : ℕ}
    (z : SquareHermiteCoeffs m) (r : Fin m) :
    (z.2 r).den ∣ squareHermiteCommonDenom z := by
  exact dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem (fun s : Fin m => (z.2 s).den)
      (Finset.mem_univ r)) _

private theorem squareHermiteCommonDenom_pos {m : ℕ}
    (z : SquareHermiteCoeffs m) :
    0 < squareHermiteCommonDenom z := by
  apply mul_pos
  · exact Finset.prod_pos fun r _ => (z.1 r).den_pos
  · exact Finset.prod_pos fun r _ => (z.2 r).den_pos

private theorem squareHermiteClearCoeffs_cast_left {m : ℕ}
    (z : SquareHermiteCoeffs m) (r : Fin (m + 1)) :
    ((squareHermiteClearCoeffs z).1 r : ℚ) =
      (squareHermiteCommonDenom z : ℚ) * z.1 r := by
  exact squareHermiteClearRat_cast (squareHermite_den_dvd_common_left z r)

private theorem squareHermiteClearCoeffs_cast_right {m : ℕ}
    (z : SquareHermiteCoeffs m) (r : Fin m) :
    ((squareHermiteClearCoeffs z).2 r : ℚ) =
      (squareHermiteCommonDenom z : ℚ) * z.2 r := by
  exact squareHermiteClearRat_cast (squareHermite_den_dvd_common_right z r)

private theorem squareHermiteClearCoeffs_ne_zero {m : ℕ}
    {z : SquareHermiteCoeffs m} (hz : z ≠ 0) :
    squareHermiteClearCoeffs z ≠ 0 := by
  intro hzero
  apply hz
  apply Prod.ext
  · funext r
    have hcoord := congrArg (fun w => w.1 r) hzero
    have hcast := squareHermiteClearCoeffs_cast_left z r
    have hc0 : (squareHermiteClearCoeffs z).1 r = 0 := by
      simpa using hcoord
    rw [hc0] at hcast
    simp only [Int.cast_zero] at hcast
    have hD :
        (squareHermiteCommonDenom z : ℚ) ≠ 0 := by
      exact_mod_cast (squareHermiteCommonDenom_pos z).ne'
    simp only [Prod.fst_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp hcast.symm).resolve_left hD
  · funext r
    have hcoord := congrArg (fun w => w.2 r) hzero
    have hcast := squareHermiteClearCoeffs_cast_right z r
    have hc0 : (squareHermiteClearCoeffs z).2 r = 0 := by
      simpa using hcoord
    rw [hc0] at hcast
    simp only [Int.cast_zero] at hcast
    have hD :
        (squareHermiteCommonDenom z : ℚ) ≠ 0 := by
      exact_mod_cast (squareHermiteCommonDenom_pos z).ne'
    simp only [Prod.snd_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp hcast.symm).resolve_left hD

private theorem squareHermiteIntUEval_cast_clear {m : ℕ}
    (z : SquareHermiteCoeffs m) (t : ℤ) :
    (squareHermiteIntUEval (squareHermiteClearCoeffs z) t : ℚ) =
      (squareHermiteCommonDenom z : ℚ) *
        squareHermiteUEval z (t : ℚ) := by
  simp only [squareHermiteIntUEval, squareHermiteUEval, Int.cast_sum,
    Int.cast_mul, Int.cast_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [squareHermiteClearCoeffs_cast_left]
  ring

private theorem squareHermiteIntVEval_cast_clear {m : ℕ}
    (z : SquareHermiteCoeffs m) (t : ℤ) :
    (squareHermiteIntVEval (squareHermiteClearCoeffs z) t : ℚ) =
      (squareHermiteCommonDenom z : ℚ) *
        squareHermiteVEval z (t : ℚ) := by
  simp only [squareHermiteIntVEval, squareHermiteVEval, Int.cast_sum,
    Int.cast_mul, Int.cast_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [squareHermiteClearCoeffs_cast_right]
  ring

private theorem squareHermiteIntUDerivEval_cast_clear {m : ℕ}
    (z : SquareHermiteCoeffs m) (t : ℤ) :
    (squareHermiteIntUDerivEval (squareHermiteClearCoeffs z) t : ℚ) =
      (squareHermiteCommonDenom z : ℚ) *
        squareHermiteUDerivEval z (t : ℚ) := by
  simp only [squareHermiteIntUDerivEval, squareHermiteUDerivEval,
    Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [squareHermiteClearCoeffs_cast_left]
  norm_num
  ring

private theorem squareHermiteIntVDerivEval_cast_clear {m : ℕ}
    (z : SquareHermiteCoeffs m) (t : ℤ) :
    (squareHermiteIntVDerivEval (squareHermiteClearCoeffs z) t : ℚ) =
      (squareHermiteCommonDenom z : ℚ) *
        squareHermiteVDerivEval z (t : ℚ) := by
  simp only [squareHermiteIntVDerivEval, squareHermiteVDerivEval,
    Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [squareHermiteClearCoeffs_cast_right]
  norm_num
  ring

theorem scratch_squareHermite_integer_kernel_exists
    (m : ℕ) (node rho alpha beta : Fin m → ℤ) :
    ∃ z : SquareHermiteIntCoeffs m, z ≠ 0 ∧
      (∀ ν,
        squareHermiteIntUEval z (node ν) =
          rho ν * squareHermiteIntVEval z (node ν)) ∧
      (∀ ν,
        beta ν *
            (squareHermiteIntUDerivEval z (node ν) -
              rho ν * squareHermiteIntVDerivEval z (node ν)) =
          alpha ν * squareHermiteIntVEval z (node ν)) := by
  obtain ⟨z, hz0, hvalue, hderiv⟩ :=
    scratch_squareHermite_kernel_exists m
      (fun ν => (node ν : ℚ)) (fun ν => (rho ν : ℚ))
      (fun ν => (alpha ν : ℚ)) (fun ν => (beta ν : ℚ))
  let zInt := squareHermiteClearCoeffs z
  refine ⟨zInt, squareHermiteClearCoeffs_ne_zero hz0, ?_, ?_⟩
  · intro ν
    dsimp [zInt]
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [squareHermiteIntUEval_cast_clear,
      squareHermiteIntVEval_cast_clear]
    rw [hvalue ν]
    ring
  · intro ν
    dsimp [zInt]
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [squareHermiteIntUDerivEval_cast_clear,
      squareHermiteIntVDerivEval_cast_clear,
      squareHermiteIntVEval_cast_clear]
    linear_combination (squareHermiteCommonDenom z : ℚ) * hderiv ν

end Erdos686Variant
end Erdos686
