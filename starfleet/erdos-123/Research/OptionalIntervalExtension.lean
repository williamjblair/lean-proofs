import Research.RadixAPRealization

namespace Erdos123

set_option maxHeartbeats 1000000

/-- If every optional summand is no larger than an existing interval width plus
one, adjoining arbitrary subsets of those summands extends the interval all
the way by their total sum. -/
theorem interval_decompose_with_optional {p : Finset ℕ} {L U n : ℕ}
    (hLU : L ≤ U)
    (hp : ∀ x ∈ p, x ≤ U - L + 1)
    (hnL : L ≤ n) (hnU : n ≤ U + p.sum id) :
    ∃ q : Finset ℕ, q ⊆ p ∧ ∃ m : ℕ,
      L ≤ m ∧ m ≤ U ∧ n = m + q.sum id := by
  induction p using Finset.induction generalizing n with
  | empty =>
      refine ⟨∅, by simp, n, hnL, ?_, by simp⟩
      simpa using hnU
  | @insert x p hxp ih =>
      rw [Finset.sum_insert hxp] at hnU
      simp only [id_eq] at hnU
      by_cases hsmall : n ≤ U + p.sum id
      · rcases ih (fun y hy => hp y (Finset.mem_insert_of_mem hy)) hnL hsmall with
          ⟨q, hqp, m, hmL, hmU, hnm⟩
        exact ⟨q, hqp.trans (Finset.subset_insert x p), m, hmL, hmU, hnm⟩
      · have hxBound := hp x (by simp)
        have hxn : x ≤ n := by omega
        have hXL : x + L ≤ U + 1 := by
          calc
            x + L ≤ (U - L + 1) + L := Nat.add_le_add_right hxBound L
            _ = U + 1 := by
              rw [show U - L + 1 + L = (U - L + L) + 1 by omega,
                Nat.sub_add_cancel hLU]
        have hxLn : x + L ≤ n := hXL.trans (by omega)
        have hnSubL : L ≤ n - x := by
          apply Nat.le_sub_of_add_le
          simpa [Nat.add_comm] using hxLn
        have hnSubU : n - x ≤ U + p.sum id := by
          apply Nat.sub_le_iff_le_add.mpr
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnU
        rcases ih (fun y hy => hp y (Finset.mem_insert_of_mem hy))
            hnSubL hnSubU with ⟨q, hqp, m, hmL, hmU, hnm⟩
        have hxq : x ∉ q := fun hxq => hxp (hqp hxq)
        refine ⟨insert x q, ?_, m, hmL, hmU, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyq
          · simp
          · exact Finset.mem_insert_of_mem (hqp hyq)
        · rw [Finset.sum_insert hxq]
          simp only [id_eq]
          calc
            n = (n - x) + x := (Nat.sub_add_cancel hxn).symm
            _ = (m + q.sum id) + x := by rw [hnm]
            _ = m + (x + q.sum id) := by omega

/-- An exact-level represented interval can be extended by a disjoint optional
finset whose terms fit below its width.  Exact degree guarantees primitive
unions automatically. -/
theorem representable_interval_extend_by_level_finset
    {a b c D L U : ℕ} {p : Finset ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hLU : L ≤ U)
    (hpBound : ∀ x ∈ p, x ≤ U - L + 1)
    (hpSmooth : ∀ x ∈ p, x ∈ Smooth3 a b c)
    (hpDegree : ∀ x ∈ p, ∃ i j k : ℕ,
      i + j + k = D ∧ x = eval3 a b c i j k)
    (hbase : ∀ n : ℕ, L ≤ n → n ≤ U →
      ∃ s : Finset ℕ,
        (∀ x ∈ s, x ∈ Smooth3 a b c) ∧
        (∀ x ∈ s, ∃ i j k : ℕ,
          i + j + k = D ∧ x = eval3 a b c i j k) ∧
        Disjoint s p ∧ s.sum id = n) :
    ∀ n : ℕ, L ≤ n → n ≤ U + p.sum id →
      IsRepresentable (Smooth3 a b c) n := by
  intro n hnL hnU
  rcases interval_decompose_with_optional hLU hpBound hnL hnU with
    ⟨q, hqp, m, hmL, hmU, hnm⟩
  rcases hbase m hmL hmU with ⟨s, hsSmooth, hsDegree, hsp, hsSum⟩
  have hsq : Disjoint s q := hsp.mono_right hqp
  let t := s ∪ q
  refine ⟨t, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hxs | hxq
    · exact hsSmooth x hxs
    · exact hpSmooth x (hqp hxq)
  · apply isPrimitive_of_exact_level ha hb hc hab hac hbc
    intro x hx
    rcases Finset.mem_union.mp hx with hxs | hxq
    · exact hsDegree x hxs
    · exact hpDegree x (hqp hxq)
  · dsimp [t]
    rw [Finset.sum_union hsq, hsSum, hnm]

end Erdos123
