import Research.Erdos769

/-!
# Cutoff bridge for a negative answer to Erdős 769

These lemmas isolate the order-theoretic part of the proposed disproof.  An
explicit eventual-admissibility threshold automatically bounds the minimal
cutoff.  Thresholds which are arbitrarily smaller than `n^n` contradict the
canonical big-Omega proposition.
-/

namespace Erdos769

/-- Any explicit eventual-admissibility threshold bounds an actual minimal
cutoff.  This uses only well-ordering of `ℕ`; no pre-existing cutoff theorem is
needed. -/
theorem exists_cutoff_le_of_eventually_admissible {n U : ℕ}
    (hU : ∀ k, U ≤ k → Admissible n k) :
    ∃ c, IsCutoff n c ∧ c ≤ U := by
  classical
  let P : ℕ → Prop := fun c => ∀ k, c ≤ k → Admissible n k
  have hex : ∃ c, P c := ⟨U, hU⟩
  let c := Nat.find hex
  have hcP : P c := Nat.find_spec hex
  have hcU : c ≤ U := Nat.find_min' hex hU
  refine ⟨c, ?_, hcU⟩
  constructor
  · exact hcP
  · by_cases hc0 : c = 0
    · exact Or.inl hc0
    · right
      intro hadm
      have hprev : P (c - 1) := by
        intro k hk
        by_cases hck : c ≤ k
        · exact hcP k hck
        · have hkeq : k = c - 1 := by omega
          simpa [hkeq] using hadm
      have hlt : c - 1 < c := by omega
      exact (Nat.find_min hex hlt) hprev

/-- If, for every proposed rational lower-bound constant and starting point,
there is a dimension with a smaller explicit eventual-admissibility threshold,
then the canonical `c(n) ≫ n^n` proposition is false. -/
theorem erdos769LowerBound_false_of_thresholds
    (U : ℕ → ℕ)
    (hU : ∀ A B N : ℕ, 0 < A → 0 < B →
      ∃ n, N ≤ n ∧ B * U n < A * n ^ n ∧
        ∀ k, U n ≤ k → Admissible n k) :
    ¬ Erdos769LowerBound := by
  rintro ⟨A, B, N, hA, hB, hlower⟩
  obtain ⟨n, hnN, hsmall, hadm⟩ := hU A B N hA hB
  obtain ⟨c, hcut, hcU⟩ :=
    exists_cutoff_le_of_eventually_admissible hadm
  have hl := hlower n c hnN hcut
  have hBc : B * c ≤ B * U n := Nat.mul_le_mul_left B hcU
  omega

end Erdos769
