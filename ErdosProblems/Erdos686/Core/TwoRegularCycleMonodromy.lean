/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.LargeOwnerTwoRegularArithmetic
import Mathlib.Algebra.BigOperators.ModEq

/-!
# Erdős 686: cycle transfer monodromy and the product-modulus zero branch

A homogeneous transfer around a finite cycle has one exact monodromy
coefficient: the difference of the products of the forward and backward
coefficients.  If every transfer is valid modulo one common modulus and the
cycle variables are units modulo that modulus, the modulus divides this
coefficient.

Canonical owner-square transfers, however, initially live modulo distinct
pairwise-coprime owner cells.  The universal way to put the transfer at cell
`e` modulo the total owner product is to multiply it by the complementary
owner product.  This file proves that the resulting monodromy determinant has
the product of all complementary factors as a common factor.  As soon as that
common factor already contains the total modulus, the proposed resultant is
identically zero modulo the total modulus.  Thus a useful cycle resultant must
use an additional cross-owner equation; merely lifting the local normalized
square congruences cannot supply it.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The small- and large-prime projections of a nonzero integer are coprime. -/
theorem kSmallPart_coprime_kLargePart
    {k x : ℕ} (hx : x ≠ 0) :
    (kSmallPart k x).Coprime (kLargePart k x) := by
  apply Nat.coprime_of_dvd
  intro p hp hpSmall hpLarge
  have hsmall0 := kSmallPart_ne_zero (k := k) hx
  have hlarge0 := kLargePart_ne_zero k x
  have hpSmallPos := hp.factorization_pos_of_dvd hsmall0 hpSmall
  have hpLargePos := hp.factorization_pos_of_dvd hlarge0 hpLarge
  rw [kSmallPart_factorization] at hpSmallPos
  rw [kLargePart_factorization] at hpLargePos
  by_cases hpk : p ≤ k
  · rw [if_neg (Nat.not_lt.mpr hpk)] at hpLargePos
    omega
  · rw [if_neg hpk] at hpSmallPos
    omega

/-- Every lower-row cofactor is a unit modulo the complete large-owner mass. -/
theorem canonicalLargeOwnerRowCofactor_coprime_mass
    {k n d t j : ℕ} (data : CanonicalOwnerData k n d t)
    (hj : j ∈ Finset.Icc 1 k) :
    (canonicalLargeOwnerRowCofactor data j).Coprime
      (kLargePart k (blockProduct k n)) := by
  have hdiv : canonicalLargeOwnerRowCofactor data j ∣
      kSmallPart k (blockProduct k n) := by
    rw [← canonicalLargeOwnerRowCofactor_product_eq_smallPart data]
    exact Finset.dvd_prod_of_mem (canonicalLargeOwnerRowCofactor data) hj
  exact Nat.Coprime.coprime_dvd_left hdiv
    (kSmallPart_coprime_kLargePart
      (ne_of_gt (blockProduct_pos k n)))

/-- Any finite product of canonical lower-row cofactors from the support is
a unit modulo the total large-owner mass. -/
theorem canonicalLargeOwner_cycleRowCofactor_isCoprime_mass
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (S : Finset (ℕ × ℕ))
    (hS : S ⊆ canonicalLargeOwnerSupport data) :
    IsCoprime (kLargePart k (blockProduct k n) : ℤ)
      ((∏ e ∈ S, canonicalLargeOwnerRowCofactor data e.1 : ℕ) : ℤ) := by
  have hnat :
      (∏ e ∈ S, canonicalLargeOwnerRowCofactor data e.1).Coprime
        (kLargePart k (blockProduct k n)) := by
    apply Nat.Coprime.prod_left
    intro e he
    have heSupport := hS he
    have heRow := (Finset.mem_product.mp
      (Finset.mem_filter.mp heSupport).1).1
    exact canonicalLargeOwnerRowCofactor_coprime_mass data heRow
  exact hnat.symm.isCoprime

/-- Homogeneous monodromy coefficient for a finite family of transfers. -/
def cycleTransferResultant
    {ι : Type*} (S : Finset ι) (a b : ι → ℤ) : ℤ :=
  (∏ e ∈ S, a e) - ∏ e ∈ S, b e

/-- Product of all local moduli except the one at `e`. -/
def cycleComplementaryProduct
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → ℕ) (e : ι) : ℕ :=
  ∏ f ∈ S.erase e, p f

/-- A local modulus times its complementary product is the total modulus. -/
theorem cycleComplementaryProduct_mul
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → ℕ) {e : ι} (he : e ∈ S) :
    p e * cycleComplementaryProduct S p e = ∏ f ∈ S, p f := by
  unfold cycleComplementaryProduct
  exact Finset.mul_prod_erase S p he

private theorem pairwise_coprime_product_dvd_nat
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → ℕ) (z : ℕ)
    (hpair : (S : Set ι).Pairwise (Function.onFun Nat.Coprime p))
    (hdvd : ∀ e ∈ S, p e ∣ z) :
    (∏ e ∈ S, p e) ∣ z := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert e S he ih =>
      rw [Finset.prod_insert he]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · apply Nat.Coprime.prod_right
        intro f hf
        exact hpair (by simp) (by simp [hf])
          (Ne.symm (ne_of_mem_of_not_mem hf he))
      · exact hdvd e (by simp)
      · apply ih
        · intro f hf g hg hfg
          exact hpair (by simp [hf]) (by simp [hg]) hfg
        · intro f hf
          exact hdvd f (by simp [hf])

/-- For at least two pairwise-coprime local moduli, the product of all
complementary products already contains the total modulus. -/
theorem cycleTotalProduct_dvd_product_complements
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → ℕ)
    (hcard : 2 ≤ S.card)
    (hpair : (S : Set ι).Pairwise (Function.onFun Nat.Coprime p)) :
    (∏ e ∈ S, p e) ∣
      ∏ e ∈ S, cycleComplementaryProduct S p e := by
  apply pairwise_coprime_product_dvd_nat S p _ hpair
  intro f hf
  have hex : ∃ e ∈ S, e ≠ f := by
    by_contra hnot
    push Not at hnot
    have hsub : S ⊆ {f} := by
      intro e he
      simp [hnot e he]
    have hle := Finset.card_le_card hsub
    simp at hle
    omega
  obtain ⟨e, he, hef⟩ := hex
  have hfErase : f ∈ S.erase e := Finset.mem_erase.mpr ⟨Ne.symm hef, hf⟩
  have hlocal : p f ∣ cycleComplementaryProduct S p e := by
    unfold cycleComplementaryProduct
    exact Finset.dvd_prod_of_mem p hfErase
  exact dvd_trans hlocal (Finset.dvd_prod_of_mem
    (cycleComplementaryProduct S p) he)

/-- Scaling every local transfer scales the cycle resultant by the product
of the local scale factors. -/
theorem cycleTransferResultant_smul
    {ι : Type*} (S : Finset ι) (scale a b : ι → ℤ) :
    cycleTransferResultant S (fun e => scale e * a e)
        (fun e => scale e * b e) =
      (∏ e ∈ S, scale e) * cycleTransferResultant S a b := by
  simp only [cycleTransferResultant]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

/-- A map which preserves a finite set and is injective on it preserves the
product of any weight around that set. -/
theorem finset_prod_comp_eq_of_maps_injective
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (next : ι → ι) (x : ι → ℤ)
    (hmap : ∀ e ∈ S, next e ∈ S)
    (hinj : ∀ e ∈ S, ∀ f ∈ S, next e = next f → e = f) :
    (∏ e ∈ S, x (next e)) = ∏ e ∈ S, x e := by
  apply Finset.prod_bij (fun e _ => next e)
  · exact hmap
  · exact hinj
  · intro y hy
    have hsubset : S.image next ⊆ S := by
      intro z hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      exact hmap e he
    have hcard : (S.image next).card = S.card := by
      rw [Finset.card_image_iff.mpr]
      intro e he f hf hef
      exact hinj e he f hf hef
    have heq : S.image next = S :=
      Finset.eq_of_subset_of_card_le hsubset (by rw [hcard])
    have hyImage : y ∈ S.image next := by rwa [heq]
    obtain ⟨e, he, hnext⟩ := Finset.mem_image.mp hyImage
    exact ⟨e, he, hnext⟩
  · intro e he
    rfl

/-- Common-modulus cycle monodromy.  Multiplying all local transfer
congruences and using the cyclic permutation gives the resultant times the
product of the cycle variables. -/
theorem cycleTransferResultant_mul_variables_dvd
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (next : ι → ι)
    (a b x : ι → ℤ) (M : ℤ)
    (hmap : ∀ e ∈ S, next e ∈ S)
    (hinj : ∀ e ∈ S, ∀ f ∈ S, next e = next f → e = f)
    (hlocal : ∀ e ∈ S, M ∣ a e * x e - b e * x (next e)) :
    M ∣ cycleTransferResultant S a b * (∏ e ∈ S, x e) := by
  have hlocalMod : ∀ e ∈ S,
      a e * x e ≡ b e * x (next e) [ZMOD M] := by
    intro e he
    apply Int.modEq_iff_dvd.mpr
    simpa [sub_eq_add_neg, add_comm] using dvd_neg.mpr (hlocal e he)
  have hprodMod := Int.ModEq.prod hlocalMod
  have hnext := finset_prod_comp_eq_of_maps_injective S next x hmap hinj
  have hdvd := Int.modEq_iff_dvd.mp hprodMod
  apply dvd_neg.mp
  convert hdvd using 1
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hnext]
  simp only [cycleTransferResultant]
  ring

/-- If the product of the cycle variables is a unit modulo the common
modulus, the fixed monodromy coefficient itself vanishes modulo the modulus. -/
theorem cycleTransferResultant_dvd_of_isCoprime_variables
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (next : ι → ι)
    (a b x : ι → ℤ) (M : ℤ)
    (hmap : ∀ e ∈ S, next e ∈ S)
    (hinj : ∀ e ∈ S, ∀ f ∈ S, next e = next f → e = f)
    (hlocal : ∀ e ∈ S, M ∣ a e * x e - b e * x (next e))
    (hcop : IsCoprime M (∏ e ∈ S, x e)) :
    M ∣ cycleTransferResultant S a b := by
  exact hcop.dvd_of_dvd_mul_right
    (cycleTransferResultant_mul_variables_dvd
      S next a b x M hmap hinj hlocal)

/-- Nonzero branch of the common-modulus monodromy theorem: a nonvanishing
cycle resultant has absolute value at least the absolute value of the modulus. -/
theorem cycleTransferResultant_zero_or_modulus_le
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (next : ι → ι)
    (a b x : ι → ℤ) (M : ℤ)
    (hmap : ∀ e ∈ S, next e ∈ S)
    (hinj : ∀ e ∈ S, ∀ f ∈ S, next e = next f → e = f)
    (hlocal : ∀ e ∈ S, M ∣ a e * x e - b e * x (next e))
    (hcop : IsCoprime M (∏ e ∈ S, x e)) :
    cycleTransferResultant S a b = 0 ∨
      M.natAbs ≤ (cycleTransferResultant S a b).natAbs := by
  by_cases hzero : cycleTransferResultant S a b = 0
  · exact Or.inl hzero
  · right
    apply Nat.le_of_dvd (Int.natAbs_pos.mpr hzero)
    exact Int.natAbs_dvd_natAbs.mpr
      (cycleTransferResultant_dvd_of_isCoprime_variables
        S next a b x M hmap hinj hlocal hcop)

/-- If the product of the row scales already contains the common modulus,
then the scaled cycle resultant is automatically zero modulo that modulus. -/
theorem scaled_cycleTransferResultant_zero
    {ι : Type*} (S : Finset ι) (scale a b : ι → ℤ) (M : ℤ)
    (hscale : M ∣ ∏ e ∈ S, scale e) :
    M ∣ cycleTransferResultant S (fun e => scale e * a e)
      (fun e => scale e * b e) := by
  rw [cycleTransferResultant_smul]
  exact dvd_mul_of_dvd_left hscale _

/-- Exact classification of the universal product-modulus lift.  Suppose a
local transfer at `e` is valid modulo `p e`, and `scale e * p e = M` lifts it
to the common modulus.  The lifted transfers do produce the formal monodromy
congruence.  But if the product of the complementary scales contains `M`, its
resultant already vanishes modulo `M`, independently of all cycle variables. -/
theorem varying_modulus_cycle_lift_zero_branch
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (next : ι → ι)
    (p scale a b x : ι → ℤ) (M : ℤ)
    (hmap : ∀ e ∈ S, next e ∈ S)
    (hinj : ∀ e ∈ S, ∀ f ∈ S, next e = next f → e = f)
    (hfactor : ∀ e ∈ S, scale e * p e = M)
    (hlocal : ∀ e ∈ S, p e ∣ a e * x e - b e * x (next e))
    (hscale : M ∣ ∏ e ∈ S, scale e) :
    M ∣ cycleTransferResultant S (fun e => scale e * a e)
          (fun e => scale e * b e) * (∏ e ∈ S, x e) ∧
      M ∣ cycleTransferResultant S (fun e => scale e * a e)
        (fun e => scale e * b e) := by
  have hlifted : ∀ e ∈ S,
      M ∣ (scale e * a e) * x e -
        (scale e * b e) * x (next e) := by
    intro e he
    obtain ⟨q, hq⟩ := hlocal e he
    refine ⟨q, ?_⟩
    rw [← hfactor e he]
    calc
      (scale e * a e) * x e - (scale e * b e) * x (next e) =
          scale e * (a e * x e - b e * x (next e)) := by ring
      _ = scale e * (p e * q) := by rw [hq]
      _ = (scale e * p e) * q := by ring
  exact ⟨
    cycleTransferResultant_mul_variables_dvd S next
      (fun e => scale e * a e) (fun e => scale e * b e)
      x M hmap hinj hlifted,
    scaled_cycleTransferResultant_zero S scale a b M hscale⟩

/-- Pairwise-coprime owner specialization of the zero-branch theorem.  With
at least two local owner moduli, complementary-product lifting always makes
the common-modulus cycle resultant divisible by the total owner product
before any arithmetic information from the transfers is used. -/
theorem pairwise_owner_cycle_lift_zero_branch
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (next : ι → ι)
    (p : ι → ℕ) (a b x : ι → ℤ)
    (hcard : 2 ≤ S.card)
    (hpair : (S : Set ι).Pairwise (Function.onFun Nat.Coprime p))
    (hmap : ∀ e ∈ S, next e ∈ S)
    (hinj : ∀ e ∈ S, ∀ f ∈ S, next e = next f → e = f)
    (hlocal : ∀ e ∈ S,
      (p e : ℤ) ∣ a e * x e - b e * x (next e)) :
    let M : ℤ := ((∏ e ∈ S, p e : ℕ) : ℤ)
    let scale : ι → ℤ := fun e => (cycleComplementaryProduct S p e : ℤ)
    M ∣ cycleTransferResultant S (fun e => scale e * a e)
          (fun e => scale e * b e) * (∏ e ∈ S, x e) ∧
      M ∣ cycleTransferResultant S (fun e => scale e * a e)
        (fun e => scale e * b e) := by
  dsimp only
  apply varying_modulus_cycle_lift_zero_branch
    (p := fun e => (p e : ℤ))
    (scale := fun e => (cycleComplementaryProduct S p e : ℤ))
  · exact hmap
  · exact hinj
  · intro e he
    exact_mod_cast (Finset.prod_erase_mul S p he)
  · exact hlocal
  · exact_mod_cast cycleTotalProduct_dvd_product_complements
      S p hcard hpair

#print axioms cycleTransferResultant_smul
#print axioms kSmallPart_coprime_kLargePart
#print axioms canonicalLargeOwnerRowCofactor_coprime_mass
#print axioms canonicalLargeOwner_cycleRowCofactor_isCoprime_mass
#print axioms finset_prod_comp_eq_of_maps_injective
#print axioms cycleTransferResultant_mul_variables_dvd
#print axioms cycleTransferResultant_dvd_of_isCoprime_variables
#print axioms cycleTransferResultant_zero_or_modulus_le
#print axioms scaled_cycleTransferResultant_zero
#print axioms varying_modulus_cycle_lift_zero_branch
#print axioms cycleComplementaryProduct_mul
#print axioms cycleTotalProduct_dvd_product_complements
#print axioms pairwise_owner_cycle_lift_zero_branch

end Erdos686Variant
end Erdos686
