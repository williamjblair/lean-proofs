import Research.WeightedSuppression

namespace Erdos959

lemma finset_product_le_card_pow
    {α : Type*} [DecidableEq α] (J : Finset α) (p : α → ℕ) (P : ℕ)
    (hp : ∀ i ∈ J, p i ≤ P) :
    (∏ i ∈ J, p i) ≤ P ^ J.card := by
  calc
    (∏ i ∈ J, p i) ≤ ∏ _i ∈ J, P := by
      exact Finset.prod_le_prod' (fun i hi => hp i hi)
    _ = P ^ J.card := Finset.prod_const P

lemma constant_mul_pow_le_pow_of_base
    {C x y j : ℕ} (hC : 1 < C) (hj : 1 ≤ j) (hbase : C * x ≤ y) :
    C * x ^ j ≤ y ^ j := by
  have hCpow : C ≤ C ^ j := by
    have : C ^ 1 ≤ C ^ j :=
      (Nat.pow_le_pow_iff_right hC).mpr hj
    simpa using this
  calc
    C * x ^ j ≤ C ^ j * x ^ j := Nat.mul_le_mul_right _ hCpow
    _ = (C * x) ^ j := (mul_pow C x j).symm
    _ ≤ y ^ j := Nat.pow_le_pow_left hbase j

lemma support_numeric_condition
    {α : Type*} [DecidableEq α]
    (U J : Finset α) (p : α → ℕ) (P h A : ℕ)
    (hJU : J ⊆ U) (hj : 1 ≤ J.card)
    (hp : ∀ i ∈ U, p i ≤ P)
    (hA : A < 2 * ∏ i ∈ J, p i)
    (hbase : (128 * 11520 ^ 2) * P * h ^ 2 ≤ 4 * U.card ^ 2) :
    11520 ^ 2 * (64 * A) * h ^ (2 * J.card) ≤
      U.card ^ (2 * J.card) * 4 ^ J.card := by
  let j := J.card
  let k := U.card
  have hprod : (∏ i ∈ J, p i) ≤ P ^ j :=
    finset_product_le_card_pow J p P fun i hi => hp i (hJU hi)
  have hA' : 64 * A ≤ 128 * P ^ j := by
    have hAD : 64 * A ≤ 128 * ∏ i ∈ J, p i := by omega
    exact hAD.trans (Nat.mul_le_mul_left 128 hprod)
  have hstart :
      11520 ^ 2 * (64 * A) * h ^ (2 * j) ≤
        (128 * 11520 ^ 2) * (P * h ^ 2) ^ j := by
    calc
      11520 ^ 2 * (64 * A) * h ^ (2 * j) ≤
          11520 ^ 2 * (128 * P ^ j) * h ^ (2 * j) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hA')
      _ = (128 * 11520 ^ 2) * (P * h ^ 2) ^ j := by
        rw [mul_pow]
        ring
  have hbase' : (128 * 11520 ^ 2) * (P * h ^ 2) ≤
      4 * k ^ 2 := by
    simpa [k, mul_assoc] using hbase
  have hpowers := constant_mul_pow_le_pow_of_base
    (C := 128 * 11520 ^ 2) (x := P * h ^ 2) (y := 4 * k ^ 2)
    (j := j) (by norm_num) hj hbase'
  calc
    11520 ^ 2 * (64 * A) * h ^ (2 * J.card) ≤
        (128 * 11520 ^ 2) * (P * h ^ 2) ^ j := hstart
    _ ≤ (4 * k ^ 2) ^ j := hpowers
    _ = k ^ (2 * J.card) * 4 ^ J.card := by
      dsimp [j, k]
      rw [mul_pow]
      ring

end Erdos959
