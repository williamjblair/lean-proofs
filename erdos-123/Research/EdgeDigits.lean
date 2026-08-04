import Research.CorrectionGadget
import Research.RadixInjection

namespace Erdos123

/-- Number of edge degrees reserved for a block of `c-1` equal-residue terms. -/
def edgeDigitDepth (c : ℕ) : ℕ := c.totient * (c - 2)

/-- The `t`-th reserved term on the `a,b` edge of homogeneous degree `E`.
For `E ≥ edgeDigitDepth c` and `t<c-1`, its two exponents sum to `E`. -/
def edgeDigitTerm (a b c E t : ℕ) : ℕ :=
  a ^ (E - edgeDigitDepth c) * correctionTerm c a b (c - 1) t

/-- Nested subset digit: choose the first `r` terms of the reserved edge block. -/
def edgeDigit (a b c E r : ℕ) : ℕ :=
  (Finset.range r).sum (edgeDigitTerm a b c E)

/-- Every reserved edge term has the same unit residue modulo `c`. -/
theorem edgeDigitTerm_modEq {a b c E t : ℕ}
    (hca : Nat.Coprime c a) (hcb : Nat.Coprime c b) :
    edgeDigitTerm a b c E t ≡ a ^ (E - edgeDigitDepth c) [MOD c] := by
  have h := correctionTerm_modEq_one (r := c - 1) (t := t) hca hcb
  simpa [edgeDigitTerm] using h.mul_left (a ^ (E - edgeDigitDepth c))

/-- A nested digit of length `r` is congruent to `r` times the common edge
unit. -/
theorem edgeDigit_modEq {a b c E r : ℕ}
    (hca : Nat.Coprime c a) (hcb : Nat.Coprime c b) :
    edgeDigit a b c E r ≡ r * a ^ (E - edgeDigitDepth c) [MOD c] := by
  have hsum :
      (Finset.range r).sum (edgeDigitTerm a b c E) ≡
        (Finset.range r).sum
          (fun _t => a ^ (E - edgeDigitDepth c)) [MOD c] :=
    Nat.ModEq.sum (fun t _ht => edgeDigitTerm_modEq hca hcb)
  simpa [edgeDigit] using hsum

/-- The `c` nested edge digits have pairwise distinct residues modulo `c`.
Thus they can serve as one position of the radix code in F-018. -/
theorem edgeDigit_residue_injective {a b c E : ℕ} (hc : 1 < c)
    (hca : Nat.Coprime c a) (hcb : Nat.Coprime c b) :
    Function.Injective (fun r : Fin c => edgeDigit a b c E r % c) := by
  intro r s hrs
  have hrsMod : edgeDigit a b c E r ≡ edgeDigit a b c E s [MOD c] := hrs
  have hr := edgeDigit_modEq (E := E) (r := (r : ℕ)) hca hcb
  have hs := edgeDigit_modEq (E := E) (r := (s : ℕ)) hca hcb
  have hmul :
      a ^ (E - edgeDigitDepth c) * (r : ℕ) ≡
        a ^ (E - edgeDigitDepth c) * (s : ℕ) [MOD c] := by
    simpa [Nat.mul_comm] using hr.symm.trans (hrsMod.trans hs)
  have hcop : Nat.Coprime c (a ^ (E - edgeDigitDepth c)) :=
    hca.pow_right _
  have hrs' : (r : ℕ) ≡ (s : ℕ) [MOD c] :=
    Nat.ModEq.cancel_left_of_coprime hcop hmul
  apply Fin.ext
  exact Nat.ModEq.eq_of_lt_of_lt hrs' r.isLt s.isLt

/-- The reserved edge term really lies on homogeneous degree `E`. -/
theorem edgeDigitTerm_exponent_sum {c E t : ℕ}
    (hE : edgeDigitDepth c ≤ E) (ht : t < c - 1) :
    (E - edgeDigitDepth c + c.totient * t) +
        c.totient * (c - 1 - 1 - t) = E := by
  have ht' : t ≤ c - 2 := by omega
  have hsplit : t + (c - 2 - t) = c - 2 := by omega
  have hmul : c.totient * t + c.totient * (c - 2 - t) =
      c.totient * (c - 2) := by
    rw [← Nat.mul_add, hsplit]
  have hcsub : c - 1 - 1 - t = c - 2 - t := by omega
  simp only [edgeDigitDepth] at hE ⊢
  rw [hcsub, add_assoc, hmul]
  exact Nat.sub_add_cancel hE

/-- Degree of the `a,b` edge paired with c-adic position `i`. -/
def edgeCodeDegree (c n : ℕ) (i : Fin n) : ℕ :=
  edgeDigitDepth c + (n - 1 - (i : ℕ))

/-- Numeric evaluation of the nested edge choices in `n` consecutive c-adic
layers of one homogeneous level. -/
def edgeCodeEval (a b c n : ℕ) (word : Fin n → Fin c) : ℕ :=
  radixEval (fun i r =>
    edgeDigit a b c (edgeCodeDegree c n i) (r : ℕ)) word

/-- The `c^n` edge-choice words give pairwise distinct residues modulo `c^n`.
This is the promised complete-residue subsystem inside consecutive layers of a
homogeneous level. -/
theorem edgeCodeEval_mod_injective {a b c n : ℕ} (hc : 1 < c)
    (hca : Nat.Coprime c a) (hcb : Nat.Coprime c b) :
    Function.Injective
      (fun word : Fin n → Fin c => edgeCodeEval a b c n word % c ^ n) := by
  unfold edgeCodeEval
  apply radixEval_mod_injective hc
  intro i
  exact edgeDigit_residue_injective hc hca hcb

/-- Every term used at c-adic position `i` has total three-variable exponent
`edgeDigitDepth c + n - 1`, independent of `i` and of the nested-digit index. -/
theorem edgeCodeTerm_total_degree {c n : ℕ} (i : Fin n) {t : ℕ}
    (ht : t < c - 1) :
    ((edgeCodeDegree c n i - edgeDigitDepth c + c.totient * t) +
      c.totient * (c - 1 - 1 - t)) + (i : ℕ) =
      edgeDigitDepth c + n - 1 := by
  have hi : (i : ℕ) ≤ n - 1 := by omega
  have hE : edgeDigitDepth c ≤ edgeCodeDegree c n i := by
    simp [edgeCodeDegree]
  rw [edgeDigitTerm_exponent_sum hE ht]
  simp only [edgeCodeDegree]
  omega

end Erdos123
