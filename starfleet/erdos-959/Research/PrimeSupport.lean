import Research.Denominator

namespace Erdos959

lemma prime_finset_product_squarefree
    (K : Finset ℕ) (hp : ∀ p ∈ K, p.Prime) :
    Squarefree (∏ p ∈ K, p) := by
  induction K using Finset.induction_on with
  | empty => simp
  | @insert p K hpK ih =>
      have pp : p.Prime := hp p (Finset.mem_insert_self p K)
      have hpRest : ∀ q ∈ K, q.Prime := by
        intro q hq
        exact hp q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hpK]
      apply Nat.squarefree_mul_iff.mpr
      refine ⟨?_, pp.prime.squarefree, ih hpRest⟩
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes pp (hpRest q hq)).mpr (fun hpq => hpK (hpq ▸ hq))

lemma divisor_of_prime_finset_product_has_support
    (K : Finset ℕ) (hp : ∀ p ∈ K, p.Prime)
    {D : ℕ} (hDpos : 0 < D) (hdiv : D ∣ ∏ p ∈ K, p) :
    ∃ J : Finset ℕ, J ⊆ K ∧ D = ∏ p ∈ J, p := by
  let s := ∏ p ∈ K, p
  have hsPos : 0 < s := Finset.prod_pos fun p hpK => (hp p hpK).pos
  have hsSq : Squarefree s := prime_finset_product_squarefree K hp
  have hDSq : Squarefree D := Squarefree.squarefree_of_dvd hdiv hsSq
  let J := D.primeFactors
  have hJsub : J ⊆ K := by
    have hmono : D.primeFactors ⊆ s.primeFactors :=
      Nat.primeFactors_mono hdiv (by omega)
    simpa [J, s, Nat.primeFactors_prod hp] using hmono
  refine ⟨J, hJsub, ?_⟩
  rw [Nat.prod_primeFactors_of_squarefree hDSq]

end Erdos959
