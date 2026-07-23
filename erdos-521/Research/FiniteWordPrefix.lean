import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

def splitBoolWordEquiv (a b : ℕ) :
    (Fin (a + b) → Bool) ≃ ((Fin a → Bool) × (Fin b → Bool)) :=
  (Equiv.piCongrLeft (fun _ : Fin (a + b) ↦ Bool) finSumFinEquiv).symm.trans
    (Equiv.sumPiEquivProdPi (fun _ ↦ Bool))

@[simp] lemma splitBoolWordEquiv_fst (a b : ℕ) (x : Fin (a + b) → Bool) (i : Fin a) :
    (splitBoolWordEquiv a b x).1 i = x (Fin.castAdd b i) := by
  rfl

@[simp] lemma splitBoolWordEquiv_snd (a b : ℕ) (x : Fin (a + b) → Bool) (i : Fin b) :
    (splitBoolWordEquiv a b x).2 i = x (Fin.natAdd a i) := by
  rfl

lemma sum_prefix_function (a b : ℕ) (F : (Fin a → Bool) → ℝ) :
    (∑ x : Fin (a + b) → Bool, F (fun i ↦ x (Fin.castAdd b i))) =
      (2 : ℝ) ^ b * ∑ y : Fin a → Bool, F y := by
  calc
    (∑ x : Fin (a + b) → Bool, F (fun i ↦ x (Fin.castAdd b i))) =
        ∑ x : Fin (a + b) → Bool, F (splitBoolWordEquiv a b x).1 := by
          apply Finset.sum_congr rfl
          intro x hx
          congr
    _ = ∑ z : (Fin a → Bool) × (Fin b → Bool), F z.1 :=
      Equiv.sum_comp (splitBoolWordEquiv a b) (fun z ↦ F z.1)
    _ = (2 : ℝ) ^ b * ∑ y : Fin a → Bool, F y := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, nsmul_eq_mul]
      simp
      rw [← Finset.mul_sum]

end Erdos521
