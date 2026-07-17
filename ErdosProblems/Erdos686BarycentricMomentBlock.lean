/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686BarycentricMomentLadder
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Erdős 686: exact normalized moment block and degree-transfer interface

This module completes the finite generating-polynomial part of the audited
moment ladder.  It proves, without a Laurent-series quotient, that under

* `c = 0`,
* `mu_0 = ... = mu_(q-1) = 0`, and
* `nu_0 = ... = nu_(q-2) = 0`,

the normalized product difference has no term below order `q*k` and its
order-`q*k` coefficient is exactly

`(mu_q + nu_(q-1))^k - 4*mu_q^k`.

The conversion from this normalized order at infinity to the degree of a
specific `matchingPhi` is isolated in `MomentDegreeTransferCertificate`.
Thus the exact degree formulas are certificate-backed, while construction of
the concrete reversal certificate remains a separate obligation.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators
open Polynomial

/-- Vanishing of `mu_0,...,mu_(q-1)`. -/
def LowerMuVanishes (mu : ℕ → ℚ) (q : ℕ) : Prop :=
  ∀ t < q, mu t = 0

/-- Vanishing of `nu_0,...,nu_(q-2)`.  This formulation handles the empty
prefixes at `q=0` and `q=1` without a special convention. -/
def LowerNuVanishes (nu : ℕ → ℚ) (q : ℕ) : Prop :=
  ∀ t, t + 1 < q → nu t = 0

/-- A finite moment generating polynomial through index `m`. -/
noncomputable def momentGeneratingPolynomial
    (m : ℕ) (a : ℕ → ℚ) : Polynomial ℚ :=
  (Polynomial.ofFn (m + 1)) fun i => a i.1

@[simp]
theorem momentGeneratingPolynomial_coeff
    {m t : ℕ} {a : ℕ → ℚ} (ht : t ≤ m) :
    (momentGeneratingPolynomial m a).coeff t = a t := by
  unfold momentGeneratingPolynomial
  simpa using
    (Polynomial.ofFn_coeff_eq_val_of_lt
      (fun i : Fin (m + 1) => a i.1) (show t < m + 1 by omega))

/-- One normalized left factor
`c + M_mu + X*M_nu + h*X*M_mu`. -/
noncomputable def normalizedLeftMomentFactor
    (m : ℕ) (c : ℚ) (muSeq nuSeq : ℕ → ℚ) (h : ℚ) : Polynomial ℚ :=
  C c + momentGeneratingPolynomial m muSeq +
    X * momentGeneratingPolynomial m nuSeq +
    C h * (X * momentGeneratingPolynomial m muSeq)

/-- One normalized right factor `M_mu + h*X*M_mu`. -/
noncomputable def normalizedRightMomentFactor
    (m : ℕ) (muSeq : ℕ → ℚ) (h : ℚ) : Polynomial ℚ :=
  momentGeneratingPolynomial m muSeq +
    C h * (X * momentGeneratingPolynomial m muSeq)

/-- The normalized product-difference block. -/
noncomputable def normalizedMomentBlock
    (m k : ℕ) (c : ℚ) (muSeq nuSeq : ℕ → ℚ)
    (h : Fin k → ℚ) : Polynomial ℚ :=
  (∏ i : Fin k, normalizedLeftMomentFactor m c muSeq nuSeq (h i)) -
    C 4 * (∏ i : Fin k, normalizedRightMomentFactor m muSeq (h i))

/-- Every coefficient below `q` in a normalized left factor vanishes under
the moment-prefix hypotheses. -/
theorem normalizedLeftMomentFactor_coeff_lt
    {m q t : ℕ} {c : ℚ} {muSeq nuSeq : ℕ → ℚ} {h : ℚ}
    (hq : q ≤ m) (hc : c = 0)
    (hmu : LowerMuVanishes muSeq q)
    (hnu : LowerNuVanishes nuSeq q)
    (ht : t < q) :
    (normalizedLeftMomentFactor m c muSeq nuSeq h).coeff t = 0 := by
  subst c
  cases t with
  | zero =>
      have hmu0 : muSeq 0 = 0 := hmu 0 ht
      simp [normalizedLeftMomentFactor,
        momentGeneratingPolynomial_coeff (a := muSeq) (by omega), hmu0]
  | succ s =>
      have hmuSucc : muSeq (s + 1) = 0 := hmu (s + 1) ht
      have hmuPrev : muSeq s = 0 := hmu s (by omega)
      have hnuPrev : nuSeq s = 0 := hnu s ht
      simp [normalizedLeftMomentFactor,
        momentGeneratingPolynomial_coeff (a := muSeq) (by omega),
        momentGeneratingPolynomial_coeff (a := nuSeq) (by omega),
        hmuSucc, hmuPrev, hnuPrev]

/-- Every coefficient below `q` in a normalized right factor vanishes. -/
theorem normalizedRightMomentFactor_coeff_lt
    {m q t : ℕ} {muSeq : ℕ → ℚ} {h : ℚ}
    (hq : q ≤ m)
    (hmu : LowerMuVanishes muSeq q)
    (ht : t < q) :
    (normalizedRightMomentFactor m muSeq h).coeff t = 0 := by
  cases t with
  | zero =>
      have hmu0 : muSeq 0 = 0 := hmu 0 ht
      simp [normalizedRightMomentFactor,
        momentGeneratingPolynomial_coeff (a := muSeq) (by omega), hmu0]
  | succ s =>
      have hmuSucc : muSeq (s + 1) = 0 := hmu (s + 1) ht
      have hmuPrev : muSeq s = 0 := hmu s (by omega)
      simp [normalizedRightMomentFactor,
        momentGeneratingPolynomial_coeff (a := muSeq) (by omega),
        hmuSucc, hmuPrev]

/-- The order-`q` coefficient of every normalized left factor is
`mu_q + nu_(q-1)`. -/
theorem normalizedLeftMomentFactor_coeff_eq
    {m q : ℕ} {c : ℚ} {muSeq nuSeq : ℕ → ℚ} {h : ℚ}
    (hq : q ≤ m) (hqpos : 1 ≤ q)
    (hmu : LowerMuVanishes muSeq q) :
    (normalizedLeftMomentFactor m c muSeq nuSeq h).coeff q =
      muSeq q + nuSeq (q - 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hmuPrev : muSeq s = 0 := hmu s (Nat.lt_succ_self s)
  simp [normalizedLeftMomentFactor,
    momentGeneratingPolynomial_coeff (a := muSeq) (by omega),
    momentGeneratingPolynomial_coeff (a := nuSeq) (by omega),
    hmuPrev]

/-- The order-`q` coefficient of every normalized right factor is `mu_q`. -/
theorem normalizedRightMomentFactor_coeff_eq
    {m q : ℕ} {muSeq : ℕ → ℚ} {h : ℚ}
    (hq : q ≤ m) (hqpos : 1 ≤ q)
    (hmu : LowerMuVanishes muSeq q) :
    (normalizedRightMomentFactor m muSeq h).coeff q = muSeq q := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hmuPrev : muSeq s = 0 := hmu s (Nat.lt_succ_self s)
  simp [normalizedRightMomentFactor,
    momentGeneratingPolynomial_coeff (a := muSeq) (by omega), hmuPrev]

/-- A product of `k` factors, each divisible by `X^q`, has its order-`qk`
coefficient equal to the product of the quotient constant coefficients. -/
theorem coeff_prod_of_common_X_order
    {k q : ℕ} (F G : Fin k → Polynomial ℚ)
    (hfactor : ∀ i, F i = X ^ q * G i) :
    (∏ i : Fin k, F i).coeff (q * k) =
      ∏ i : Fin k, (G i).coeff 0 := by
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  have hX : (∏ _i : Fin k, X ^ q) = X ^ (q * k) := by
    simp [← pow_mul]
  rw [hX, Polynomial.coeff_X_pow_mul']
  simp

/-- Exact generating-polynomial identity for the next moment block. -/
theorem normalizedMomentBlock_coeff
    {m k q : ℕ} {c : ℚ} {muSeq nuSeq : ℕ → ℚ}
    (h : Fin k → ℚ)
    (hq : q ≤ m) (hqpos : 1 ≤ q) (hc : c = 0)
    (hmu : LowerMuVanishes muSeq q)
    (hnu : LowerNuVanishes nuSeq q) :
    (normalizedMomentBlock m k c muSeq nuSeq h).coeff (q * k) =
      momentDelta k (muSeq q) (nuSeq (q - 1)) := by
  have hdivLeft : ∀ i : Fin k,
      X ^ q ∣ normalizedLeftMomentFactor m c muSeq nuSeq (h i) := by
    intro i
    rw [Polynomial.X_pow_dvd_iff]
    intro t ht
    exact normalizedLeftMomentFactor_coeff_lt hq hc hmu hnu ht
  have hdivRight : ∀ i : Fin k,
      X ^ q ∣ normalizedRightMomentFactor m muSeq (h i) := by
    intro i
    rw [Polynomial.X_pow_dvd_iff]
    intro t ht
    exact normalizedRightMomentFactor_coeff_lt hq hmu ht
  choose L hL using hdivLeft
  choose R hR using hdivRight
  have hLc : ∀ i : Fin k,
      (L i).coeff 0 = muSeq q + nuSeq (q - 1) := by
    intro i
    have hcoeff := normalizedLeftMomentFactor_coeff_eq
      (c := c) (h := h i) hq hqpos hmu
    rw [hL i, Polynomial.coeff_X_pow_mul'] at hcoeff
    simpa using hcoeff
  have hRc : ∀ i : Fin k, (R i).coeff 0 = muSeq q := by
    intro i
    have hcoeff := normalizedRightMomentFactor_coeff_eq
      (h := h i) hq hqpos hmu
    rw [hR i, Polynomial.coeff_X_pow_mul'] at hcoeff
    simpa using hcoeff
  have hprodLeft :
      (∏ i : Fin k, normalizedLeftMomentFactor m c muSeq nuSeq (h i)).coeff
          (q * k) = (muSeq q + nuSeq (q - 1)) ^ k := by
    rw [coeff_prod_of_common_X_order _ L hL]
    simp [hLc]
  have hprodRight :
      (∏ i : Fin k, normalizedRightMomentFactor m muSeq (h i)).coeff
          (q * k) = muSeq q ^ k := by
    rw [coeff_prod_of_common_X_order _ R hR]
    simp [hRc]
  rw [normalizedMomentBlock, coeff_sub, coeff_C_mul,
    hprodLeft, hprodRight]
  rfl

/-- The normalized block has no coefficient below order `qk`. -/
theorem normalizedMomentBlock_coeff_lt
    {m k q t : ℕ} {c : ℚ} {muSeq nuSeq : ℕ → ℚ}
    (h : Fin k → ℚ)
    (hq : q ≤ m) (hc : c = 0)
    (hmu : LowerMuVanishes muSeq q)
    (hnu : LowerNuVanishes nuSeq q)
    (ht : t < q * k) :
    (normalizedMomentBlock m k c muSeq nuSeq h).coeff t = 0 := by
  have hdivLeft : ∀ i : Fin k,
      X ^ q ∣ normalizedLeftMomentFactor m c muSeq nuSeq (h i) := by
    intro i
    rw [Polynomial.X_pow_dvd_iff]
    intro s hs
    exact normalizedLeftMomentFactor_coeff_lt hq hc hmu hnu hs
  have hdivRight : ∀ i : Fin k,
      X ^ q ∣ normalizedRightMomentFactor m muSeq (h i) := by
    intro i
    rw [Polynomial.X_pow_dvd_iff]
    intro s hs
    exact normalizedRightMomentFactor_coeff_lt hq hmu hs
  choose L hL using hdivLeft
  choose R hR using hdivRight
  have hprodLeft : X ^ (q * k) ∣
      ∏ i : Fin k, normalizedLeftMomentFactor m c muSeq nuSeq (h i) := by
    refine ⟨∏ i : Fin k, L i, ?_⟩
    simp_rw [hL]
    rw [Finset.prod_mul_distrib]
    simp [← pow_mul]
  have hprodRight : X ^ (q * k) ∣
      ∏ i : Fin k, normalizedRightMomentFactor m muSeq (h i) := by
    refine ⟨∏ i : Fin k, R i, ?_⟩
    simp_rw [hR]
    rw [Finset.prod_mul_distrib]
    simp [← pow_mul]
  have hblock : X ^ (q * k) ∣ normalizedMomentBlock m k c muSeq nuSeq h := by
    rw [normalizedMomentBlock]
    exact dvd_sub hprodLeft (dvd_mul_of_dvd_right hprodRight (C 4))
  exact (Polynomial.X_pow_dvd_iff.mp hblock) t ht

/-- A first nonzero moment pair produces a nonzero next block. -/
theorem momentDelta_ne_zero_of_first_nonzero
    {muq nuPred : ℚ} {k : ℕ} (hk : 3 ≤ k)
    (hpair : muq ≠ 0 ∨ nuPred ≠ 0) :
    momentDelta k muq nuPred ≠ 0 := by
  intro hzero
  exact hpair.elim
    (fun hmu => hmu ((rational_momentDelta_eq_zero_iff hk).mp hzero).1)
    (fun hnu => hnu ((rational_momentDelta_eq_zero_iff hk).mp hzero).2)

/-- At-infinity degree-transfer certificate.  This is the exact interface to
supply when the normalized finite block is attached to a concrete matching
polynomial. -/
structure MomentDegreeTransferCertificate
    (Phi block : Polynomial ℚ) (m k q : ℕ) : Prop where
  degree_of_first_nonzero_block :
    block.coeff (q * k) ≠ 0 → Phi.natDegree = k * (m - q)

/-- Once the reversal transfer is certified, the exact block identity gives
`deg Phi = k*(m-q)` for the first nonzero moment pair. -/
theorem momentPhi_natDegree
    {m k q : ℕ} {c : ℚ} {muSeq nuSeq : ℕ → ℚ}
    (h : Fin k → ℚ) (Phi : Polynomial ℚ)
    (hq : q ≤ m) (hqpos : 1 ≤ q) (hc : c = 0)
    (hmu : LowerMuVanishes muSeq q)
    (hnu : LowerNuVanishes nuSeq q)
    (hk : 3 ≤ k)
    (hpair : muSeq q ≠ 0 ∨ nuSeq (q - 1) ≠ 0)
    (htransfer : MomentDegreeTransferCertificate Phi
      (normalizedMomentBlock m k c muSeq nuSeq h) m k q) :
    Phi.natDegree = k * (m - q) := by
  apply htransfer.degree_of_first_nonzero_block
  rw [normalizedMomentBlock_coeff h hq hqpos hc hmu hnu]
  exact momentDelta_ne_zero_of_first_nonzero hk hpair

/-- Arithmetic identity behind division by a square support polynomial. -/
theorem moment_degree_subtract_square
    {m k q : ℕ} (hq : q ≤ m) (hk : 2 ≤ k)
    (hfeasible : q * k ≤ m * (k - 2)) :
    k * (m - q) = 2 * m + (m * (k - 2) - q * k) := by
  have hleft : k * (m - q) = k * m - k * q := by
    rw [Nat.mul_sub_left_distrib]
  have hkdecomp : k = (k - 2) + 2 := by omega
  have hkm : k * m = 2 * m + m * (k - 2) := by
    calc
      k * m = ((k - 2) + 2) * m := by rw [← hkdecomp]
      _ = 2 * m + m * (k - 2) := by ring
  have hqk : q * k = k * q := Nat.mul_comm q k
  have hfeasible' : k * q ≤ m * (k - 2) := by
    simpa [hqk] using hfeasible
  rw [hleft, hkm, hqk]
  omega

/-- If `Phi = W^2*Q`, `deg W = m`, and the first nonzero block gives
`deg Phi = k*(m-q)`, then `deg Q = m*(k-2)-q*k`. -/
theorem momentQuotient_natDegree
    {m k q : ℕ} {Phi W Q : Polynomial ℚ}
    (hPhi : Phi.natDegree = k * (m - q))
    (hW : W.natDegree = m) (hWne : W ≠ 0) (hQne : Q ≠ 0)
    (hfactor : Phi = W ^ 2 * Q)
    (hq : q ≤ m) (hk : 2 ≤ k)
    (hfeasible : q * k ≤ m * (k - 2)) :
    Q.natDegree = m * (k - 2) - q * k := by
  have hdegree : Phi.natDegree = 2 * m + Q.natDegree := by
    rw [hfactor, Polynomial.natDegree_mul (pow_ne_zero 2 hWne) hQne,
      Polynomial.natDegree_pow, hW]
  have harith := moment_degree_subtract_square hq hk hfeasible
  omega

#print axioms normalizedMomentBlock_coeff
#print axioms normalizedMomentBlock_coeff_lt
#print axioms momentDelta_ne_zero_of_first_nonzero
#print axioms momentPhi_natDegree
#print axioms momentQuotient_natDegree

end Erdos686Variant
end Erdos686
