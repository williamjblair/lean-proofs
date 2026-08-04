import Research.EdgeCodeFinset

namespace Erdos123

/-- The fixed unscaled digit underlying every layer of the edge code. -/
def edgeBaseDigit (a b c r : ℕ) : ℕ :=
  (Finset.range r).sum (correctionTerm c a b (c - 1))

/-- Every edge digit is a power of `a` times one fixed digit. -/
theorem edgeDigit_eq_pow_mul_base (a b c E r : ℕ) :
    edgeDigit a b c E r =
      a ^ (E - edgeDigitDepth c) * edgeBaseDigit a b c r := by
  unfold edgeDigit edgeDigitTerm edgeBaseDigit
  rw [Finset.mul_sum]

/-- At the bottom reserved degree the edge digit is exactly the base digit. -/
theorem edgeDigit_at_depth (a b c r : ℕ) :
    edgeDigit a b c (edgeDigitDepth c) r = edgeBaseDigit a b c r := by
  rw [edgeDigit_eq_pow_mul_base]
  simp

/-- Closed stationary formula for F-019's position-dependent code.  Although
its original definition uses a different homogeneous edge degree at every
position, all dependence on the depth is just the mixed weight
`c^i * a^(n-1-i)`. -/
theorem edgeCodeEval_stationary (a b c n : ℕ) (word : Fin n → Fin c) :
    edgeCodeEval a b c n word =
      ∑ i : Fin n, c ^ (i : ℕ) * a ^ (n - 1 - (i : ℕ)) *
        edgeBaseDigit a b c (word i : ℕ) := by
  unfold edgeCodeEval radixEval
  apply Finset.sum_congr rfl
  intro i _hi
  change c ^ (i : ℕ) * edgeDigit a b c (edgeCodeDegree c n i) (word i : ℕ) = _
  rw [edgeDigit_eq_pow_mul_base]
  simp only [edgeCodeDegree]
  have hsub :
      edgeDigitDepth c + (n - 1 - (i : ℕ)) - edgeDigitDepth c =
        n - 1 - (i : ℕ) := by omega
  rw [hsub]
  ac_rfl

/-- Exact one-step recurrence: old positions are multiplied by `a`, while the
new top c-adic layer contributes `c^n` times one fixed digit. -/
theorem edgeCodeEval_succ (a b c n : ℕ) (word : Fin (n + 1) → Fin c) :
    edgeCodeEval a b c (n + 1) word =
      a * edgeCodeEval a b c n (fun i => word i.castSucc) +
      c ^ n * edgeBaseDigit a b c (word (Fin.last n) : ℕ) := by
  rw [edgeCodeEval_stationary, Fin.sum_univ_castSucc,
    edgeCodeEval_stationary]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Fin.coe_castSucc]
    have hi : (i : ℕ) ≤ n - 1 := by omega
    have hpow : n + 1 - 1 - (i : ℕ) = (n - 1 - (i : ℕ)) + 1 := by omega
    rw [hpow, pow_succ]
    ac_rfl
  · simp

end Erdos123
