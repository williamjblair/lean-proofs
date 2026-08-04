import Mathlib

namespace Erdos123

/-- A positive near-relation `p*α-q*β=d` produces an eventually dense
nonnegative additive semigroup: every sufficiently large `x` has a semigroup
point in `(x-ε,x]`. -/
theorem additiveSemigroup_eventually_leftDense
    {α β d ε : ℝ} {p q : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hp : 0 < p) (hq : 0 < q)
    (hd : d = (p : ℝ) * α - (q : ℝ) * β)
    (hdPos : 0 < d) (hdε : d < ε) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ u v : ℕ, x - ε < (u : ℝ) * α + (v : ℝ) * β ∧
        (u : ℝ) * α + (v : ℝ) * β ≤ x := by
  let s : ℝ := (q : ℝ) * β
  have hsPos : 0 < s := mul_pos (by exact_mod_cast hq) hβ
  rcases Archimedean.arch s hdPos with ⟨K₀, hK₀⟩
  refine ⟨((K₀ : ℝ) + 1) * s, ?_⟩
  intro x hx
  rcases existsUnique_zsmul_near_of_pos hsPos x with ⟨K, hK, _hKuniq⟩
  simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one] at hK
  have hKnonneg : 0 ≤ K := by
    by_contra hneg
    have hKle : (K : ℝ) + 1 ≤ 0 := by exact_mod_cast (show K + 1 ≤ 0 by omega)
    nlinarith
  let k : ℕ := K.toNat
  have hkCast : (k : ℝ) = (K : ℝ) := by
    have hkInt : (k : ℤ) = K := Int.toNat_of_nonneg hKnonneg
    exact_mod_cast hkInt
  have hK₀le : K₀ ≤ k := by
    have hcast : (K₀ : ℝ) ≤ (k : ℝ) := by
      rw [hkCast]
      nlinarith
    exact_mod_cast hcast
  have hsOverlap : s ≤ (k : ℝ) * d := by
    have hK₀' : s ≤ (K₀ : ℝ) * d := by simpa [nsmul_eq_mul] using hK₀
    have hNat : (K₀ : ℝ) * d ≤ (k : ℝ) * d := by
      gcongr
    exact hK₀'.trans hNat
  have hkLower : (k : ℝ) * s ≤ x := by
    rw [hkCast]
    exact hK.1
  have hkUpper : x < ((k : ℝ) + 1) * s := by
    rw [hkCast]
    exact hK.2
  have hgNonneg : 0 ≤ x - (k : ℝ) * s := by linarith
  have hgLt : x - (k : ℝ) * s < (k : ℝ) * d := by linarith

  rcases existsUnique_zsmul_near_of_pos hdPos (x - (k : ℝ) * s) with
    ⟨T, hT, _hTuniq⟩
  simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one] at hT
  have hTnonneg : 0 ≤ T := by
    by_contra hneg
    have hTle : (T : ℝ) + 1 ≤ 0 := by exact_mod_cast (show T + 1 ≤ 0 by omega)
    nlinarith
  let t : ℕ := T.toNat
  have htCast : (t : ℝ) = (T : ℝ) := by
    have htInt : (t : ℤ) = T := Int.toNat_of_nonneg hTnonneg
    exact_mod_cast htInt
  have htLe : t ≤ k := by
    have hcast : (T : ℝ) < (k : ℝ) := by
      by_contra hnot
      have hge : (k : ℝ) ≤ (T : ℝ) := le_of_not_gt hnot
      nlinarith
    have hint : T < (k : ℤ) := by exact_mod_cast hcast
    have htInt : (t : ℤ) = T := Int.toNat_of_nonneg hTnonneg
    omega

  refine ⟨p * t, q * (k - t), ?_, ?_⟩
  · have hcastSub : ((k - t : ℕ) : ℝ) = (k : ℝ) - (t : ℝ) :=
      Nat.cast_sub htLe
    rw [Nat.cast_mul, Nat.cast_mul, hcastSub, htCast]
    have hExpr :
        (p : ℝ) * (T : ℝ) * α + (q : ℝ) * ((k : ℝ) - (T : ℝ)) * β =
          (k : ℝ) * s + (T : ℝ) * d := by
      rw [hd]
      dsimp [s]
      ring
    rw [hExpr]
    nlinarith [hT.2]
  · have hcastSub : ((k - t : ℕ) : ℝ) = (k : ℝ) - (t : ℝ) :=
      Nat.cast_sub htLe
    rw [Nat.cast_mul, Nat.cast_mul, hcastSub, htCast]
    have hExpr :
        (p : ℝ) * (T : ℝ) * α + (q : ℝ) * ((k : ℝ) - (T : ℝ)) * β =
          (k : ℝ) * s + (T : ℝ) * d := by
      rw [hd]
      dsimp [s]
      ring
    rw [hExpr]
    nlinarith [hT.1]

end Erdos123
