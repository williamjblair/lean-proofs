import Mathlib

namespace Erdos959

variable {ι M : Type*} [DecidableEq ι] [DecidableEq M] [CommMonoidWithZero M]

/-- Choose one of two factors at every index of `U`, according to membership in `S`. -/
def binaryFactorProduct (U S : Finset ι) (a b : ι → M) : M :=
  ∏ i ∈ U, if i ∈ S then a i else b i

lemma leftFactor_dvd_binaryProduct_iff
    (U S : Finset ι) (a b : ι → M)
    (ha : ∀ i ∈ U, Prime (a i))
    (haa : ∀ i ∈ U, ∀ j ∈ U, a i ∣ a j → i = j)
    (hab : ∀ i ∈ U, ∀ j ∈ U, ¬a i ∣ b j)
    {i : ι} (hiU : i ∈ U) :
    a i ∣ binaryFactorProduct U S a b ↔ i ∈ S := by
  constructor
  · intro hd
    have hp : Prime (a i) := ha i hiU
    rcases (Prime.dvd_finsetProd_iff hp
      (fun j => if j ∈ S then a j else b j)).mp hd with ⟨j, hjU, hdj⟩
    by_cases hjS : j ∈ S
    · simp only [if_pos hjS] at hdj
      have hij : i = j := haa i hiU j hjU hdj
      simpa [hij] using hjS
    · simp only [if_neg hjS] at hdj
      exact False.elim (hab i hiU j hjU hdj)
  · intro hiS
    have hd := Finset.dvd_prod_of_mem
      (fun j => if j ∈ S then a j else b j) hiU
    simpa only [binaryFactorProduct, if_pos hiS] using hd

lemma binaryFactorProduct_injOn_powerset
    (U : Finset ι) (a b : ι → M)
    (ha : ∀ i ∈ U, Prime (a i))
    (haa : ∀ i ∈ U, ∀ j ∈ U, a i ∣ a j → i = j)
    (hab : ∀ i ∈ U, ∀ j ∈ U, ¬a i ∣ b j) :
    Set.InjOn (fun S => binaryFactorProduct U S a b) (U.powerset : Set (Finset ι)) := by
  intro S hS T hT heq
  change binaryFactorProduct U S a b = binaryFactorProduct U T a b at heq
  have hSU : S ⊆ U := Finset.mem_powerset.mp hS
  have hTU : T ⊆ U := Finset.mem_powerset.mp hT
  ext i
  by_cases hiU : i ∈ U
  · constructor
    · intro hiS
      apply (leftFactor_dvd_binaryProduct_iff U T a b ha haa hab hiU).mp
      rw [← heq]
      exact (leftFactor_dvd_binaryProduct_iff U S a b ha haa hab hiU).mpr hiS
    · intro hiT
      apply (leftFactor_dvd_binaryProduct_iff U S a b ha haa hab hiU).mp
      rw [heq]
      exact (leftFactor_dvd_binaryProduct_iff U T a b ha haa hab hiU).mpr hiT
  · have hiS : i ∉ S := fun hi => hiU (hSU hi)
    have hiT : i ∉ T := fun hi => hiU (hTU hi)
    simp [hiS, hiT]

lemma card_binaryFactorProducts
    (U : Finset ι) (a b : ι → M)
    (ha : ∀ i ∈ U, Prime (a i))
    (haa : ∀ i ∈ U, ∀ j ∈ U, a i ∣ a j → i = j)
    (hab : ∀ i ∈ U, ∀ j ∈ U, ¬a i ∣ b j) :
    (U.powerset.image fun S => binaryFactorProduct U S a b).card = 2 ^ U.card := by
  rw [Finset.card_image_iff.mpr
    (binaryFactorProduct_injOn_powerset U a b ha haa hab)]
  exact Finset.card_powerset U

end Erdos959
