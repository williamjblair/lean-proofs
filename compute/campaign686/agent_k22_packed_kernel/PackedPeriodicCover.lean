import Mathlib

namespace Erdos686.K22PackedKernel

/-- Repeat a low-bit-first residue mask by balanced doubling. -/
def periodicPowMask (w p pattern : ℕ) : ℕ → BitVec w
  | 0 => BitVec.ofNat w pattern
  | e + 1 =>
      let previous := periodicPowMask w p pattern e
      previous ||| (previous <<< (p * 2 ^ e))

/-- A true residue bit propagates into the corresponding bit of a sufficiently
long balanced periodic mask.  Only this soundness direction is needed by the
cover certificate. -/
theorem periodicPowMask_getLsbD_true
    {w p pattern e i : ℕ} (hiw : i < w) (hi : i < p * 2 ^ e)
    (hbit : pattern.testBit (i % p) = true) :
    (periodicPowMask w p pattern e).getLsbD i = true := by
  induction e generalizing i with
  | zero =>
      have hip : i < p := by simpa using hi
      have himod : i % p = i := Nat.mod_eq_of_lt hip
      rw [himod] at hbit
      rw [periodicPowMask, BitVec.getLsbD_ofNat]
      simp [hiw, hbit]
  | succ e ih =>
      let shift := p * 2 ^ e
      have htotal : p * 2 ^ (e + 1) = 2 * shift := by
        dsimp [shift]
        rw [pow_succ]
        ring
      rw [periodicPowMask, BitVec.getLsbD_or]
      by_cases hfirst : i < shift
      · have hprev := ih hiw hfirst hbit
        simp [hprev]
      · have hle : shift ≤ i := Nat.le_of_not_gt hfirst
        have hj : i - shift < p * 2 ^ e := by
          rw [htotal] at hi
          dsimp [shift] at hle ⊢
          omega
        have hmod : (i - shift) % p = i % p := by
          conv_rhs => rw [← Nat.add_sub_of_le hle]
          simp [shift, Nat.add_mod]
        have hjw : i - shift < w := by omega
        have hprev := ih hjw hj (by simpa [hmod] using hbit)
        rw [BitVec.getLsbD_shiftLeft]
        simp [hiw, hfirst, hprev, shift]

/-- Intersect periodic masks, stopping as soon as the accumulator is zero. -/
def intersectPeriodicItems (w e : ℕ) : BitVec w → List (ℕ × ℕ) → BitVec w
  | acc, [] => acc
  | acc, (p, pattern) :: rest =>
      if acc = BitVec.zero w then BitVec.zero w
      else intersectPeriodicItems w e
        (acc.and (periodicPowMask w p pattern e)) rest

/-- If the accumulator bit and every listed residue bit are true, then the
same bit is true after the packed intersection. -/
theorem intersectPeriodicItems_getLsbD_true
    {w e i : ℕ} {acc : BitVec w} {items : List (ℕ × ℕ)}
    (hiw : i < w) (hacc : acc.getLsbD i = true)
    (hitem : ∀ item ∈ items,
      i < item.1 * 2 ^ e ∧ item.2.testBit (i % item.1) = true) :
    (intersectPeriodicItems w e acc items).getLsbD i = true := by
  induction items generalizing acc with
  | nil => simpa [intersectPeriodicItems] using hacc
  | cons item rest ih =>
      have hhead := hitem item (by simp)
      have hmask := periodicPowMask_getLsbD_true hiw hhead.1 hhead.2
      have hacc_ne : acc ≠ BitVec.zero w := by
        intro hzero
        subst acc
        simpa using hacc
      rw [intersectPeriodicItems, if_neg hacc_ne]
      apply ih
      · simpa using congrArg id (show
          (acc.and (periodicPowMask w item.1 item.2 e)).getLsbD i = true by
            simp [hacc, hmask])
      · intro next hnext
        exact hitem next (by simp [hnext])

/-- A kernel-checked zero packed intersection rules out any index whose
residue bit is true in every listed mask. -/
theorem no_index_of_intersection_zero
    {w e i : ℕ} {items : List (ℕ × ℕ)}
    (hiw : i < w)
    (hzero : intersectPeriodicItems w e (BitVec.allOnes w) items =
      BitVec.zero w)
    (hitem : ∀ item ∈ items,
      i < item.1 * 2 ^ e ∧ item.2.testBit (i % item.1) = true) : False := by
  have htrue := intersectPeriodicItems_getLsbD_true hiw
    (acc := BitVec.allOnes w) (items := items) (by simp [hiw]) hitem
  rw [hzero] at htrue
  simpa using htrue

end Erdos686.K22PackedKernel
