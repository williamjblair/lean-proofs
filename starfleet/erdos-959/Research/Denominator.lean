import Mathlib

namespace Erdos959

lemma reduced_denominator_dvd_target
    {A D s t : ℕ} (hcop : D.Coprime A) (heq : D * t = A * s) :
    D ∣ s := by
  apply hcop.dvd_of_dvd_mul_left
  exact ⟨t, heq.symm⟩

lemma prime_product_dvd_prime_product_imp_subset
    {U J K : Finset ℕ}
    (hprime : ∀ p ∈ U, p.Prime)
    (hJU : J ⊆ U) (hKU : K ⊆ U)
    (hdiv : (∏ p ∈ J, p) ∣ ∏ p ∈ K, p) :
    J ⊆ K := by
  intro p hpJ
  have pp : p.Prime := hprime p (hJU hpJ)
  have hpdivJ : p ∣ ∏ q ∈ J, q := by
    exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hpJ
  have hpdivK : p ∣ ∏ q ∈ K, q := hpdivJ.trans hdiv
  rcases (Prime.dvd_finsetProd_iff pp.prime (fun q : ℕ => q)).mp hpdivK with
    ⟨q, hqK, hpq⟩
  have qp : q.Prime := hprime q (hKU hqK)
  rcases (Nat.dvd_prime qp).mp hpq with hp1 | hpqeq
  · exact False.elim (pp.ne_one hp1)
  · simpa [hpqeq] using hqK

lemma reduced_denominator_support_subset
    {A D s t : ℕ} {U J K : Finset ℕ}
    (hcop : D.Coprime A) (heq : D * t = A * s)
    (hD : D = ∏ p ∈ J, p) (hs : s = ∏ p ∈ K, p)
    (hprime : ∀ p ∈ U, p.Prime)
    (hJU : J ⊆ U) (hKU : K ⊆ U) :
    J ⊆ K := by
  apply prime_product_dvd_prime_product_imp_subset hprime hJU hKU
  rw [← hD, ← hs]
  exact reduced_denominator_dvd_target hcop heq

end Erdos959
