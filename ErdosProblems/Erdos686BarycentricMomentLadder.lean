/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686BarycentricMatching
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Erdős 686: exact barycentric moment-block cancellation ladder

For nodes `j_i`, weights `w_i`, and offsets `rho_i`, define

`mu_q = sum_i w_i j_i^q`,
`nu_q = sum_i w_i rho_i j_i^q`.

The normalized factors at infinity are encoded as finite generating
polynomials.  If `c = 0`, the moments `mu_0,...,mu_(q-1)` vanish, and the
moments `nu_0,...,nu_(q-2)` vanish, every left and right factor starts in
order `q`.  Their order-`q` coefficients are respectively
`mu_q + nu_(q-1)` and `mu_q`.  Consequently the order-`qk` block coefficient
is exactly

`Delta_q = (mu_q + nu_(q-1))^k - 4 mu_q^k`.

The final conversion from order at infinity to the degree of a concrete
matching polynomial is exposed as an explicit certificate interface.  It is
not silently identified with the coefficient calculation.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators
open Polynomial

/-- The ordinary barycentric moment `mu_q`. -/
def barycentricMoment {m : ℕ}
    (node weight : Fin m → ℚ) (q : ℕ) : ℚ :=
  ∑ i : Fin m, weight i * node i ^ q

/-- The offset barycentric moment `nu_q`. -/
def barycentricRhoMoment {m : ℕ}
    (node rho weight : Fin m → ℚ) (q : ℕ) : ℚ :=
  ∑ i : Fin m, weight i * rho i * node i ^ q

/-- Vanishing of `mu_0,...,mu_(q-1)`. -/
def LowerMuVanishes (mu : ℕ → ℚ) (q : ℕ) : Prop :=
  ∀ t < q, mu t = 0

/-- Vanishing of `nu_0,...,nu_(q-2)`.  This formulation also handles `q=0`
and `q=1` without a special empty-range convention. -/
def LowerNuVanishes (nu : ℕ → ℚ) (q : ℕ) : Prop :=
  ∀ t, t + 1 < q → nu t = 0

/-- The exact next moment-block coefficient. -/
def momentBlockDelta
    (mu nu : ℕ → ℚ) (q k : ℕ) : ℚ :=
  (mu q + nu (q - 1)) ^ k - 4 * mu q ^ k

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
`c + M_mu + X M_nu + h X M_mu`. -/
noncomputable def normalizedLeftMomentFactor
    (m : ℕ) (c : ℚ) (mu nu : ℕ → ℚ) (h : ℚ) : Polynomial ℚ :=
  C c + momentGeneratingPolynomial m mu +
    X * momentGeneratingPolynomial m nu +
    C h * (X * momentGeneratingPolynomial m mu)

/-- One normalized right factor `M_mu + h X M_mu`. -/
noncomputable def normalizedRightMomentFactor
    (m : ℕ) (mu : ℕ → ℚ) (h : ℚ) : Polynomial ℚ :=
  momentGeneratingPolynomial m mu +
    C h * (X * momentGeneratingPolynomial m mu)

/-- The normalized product-difference block. -/
noncomputable def normalizedMomentBlock
    (m k : ℕ) (c : ℚ) (mu nu : ℕ → ℚ)
    (h : Fin k → ℚ) : Polynomial ℚ :=
  (∏ i : Fin k, normalizedLeftMomentFactor m c mu nu (h i)) -
    C 4 * (∏ i : Fin k, normalizedRightMomentFactor m mu (h i))

/-- Every coefficient below `q` in a normalized left factor vanishes under the
moment-prefix hypotheses. -/
theorem normalizedLeftMomentFactor_coeff_lt
    {m q t : ℕ} {c : ℚ} {mu nu : ℕ → ℚ} {h : ℚ}
    (hq : q ≤ m) (hc : c = 0)
    (hmu : LowerMuVanishes mu q)
    (hnu : LowerNuVanishes nu q)
    (ht : t < q) :
    (normalizedLeftMomentFactor m c mu nu h).coeff t = 0 := by
  subst c
  cases t with
  | zero =>
      have hmu0 : mu 0 = 0 := hmu 0 ht
      simp [normalizedLeftMomentFactor,
        momentGeneratingPolynomial_coeff (a := mu) (by omega), hmu0]
  | succ s =>
      have hmuSucc : mu (s + 1) = 0 := hmu (s + 1) ht
      have hmuPrev : mu s = 0 := hmu s (by omega)
      have hnuPrev : nu s = 0 := hnu s ht
      simp [normalizedLeftMomentFactor,
        momentGeneratingPolynomial_coeff (a := mu) (by omega),
        momentGeneratingPolynomial_coeff (a := nu) (by omega),
        hmuSucc, hmuPrev, hnuPrev]

/-- Every coefficient below `q` in a normalized right factor vanishes. -/
theorem normalizedRightMomentFactor_coeff_lt
    {m q t : ℕ} {mu : ℕ → ℚ} {h : ℚ}
    (hq : q ≤ m)
    (hmu : LowerMuVanishes mu q)
    (ht : t < q) :
    (normalizedRightMomentFactor m mu h).coeff t = 0 := by
  cases t with
  | zero =>
      have hmu0 : mu 0 = 0 := hmu 0 ht
      simp [normalizedRightMomentFactor,
        momentGeneratingPolynomial_coeff (a := mu) (by omega), hmu0]
  | succ s =>
      have hmuSucc : mu (s + 1) = 0 := hmu (s + 1) ht
      have hmuPrev : mu s = 0 := hmu s (by omega)
      simp [normalizedRightMomentFactor,
        momentGeneratingPolynomial_coeff (a := mu) (by omega),
        hmuSucc, hmuPrev]

/-- The order-`q` coefficient of every normalized left factor is
`mu_q + nu_(q-1)`. -/
theorem normalizedLeftMomentFactor_coeff_eq
    {m q : ℕ} {c : ℚ} {mu nu : ℕ → ℚ} {h : ℚ}
    (hq : q ≤ m) (hqpos : 1 ≤ q)
    (hmu : LowerMuVanishes mu q) :
    (normalizedLeftMomentFactor m c mu nu h).coeff q =
      mu q + nu (q - 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hmuPrev : mu s = 0 := hmu s (Nat.lt_succ_self s)
  simp [normalizedLeftMomentFactor,
    momentGeneratingPolynomial_coeff (a := mu) (by omega),
    momentGeneratingPolynomial_coeff (a := nu) (by omega),
    hmuPrev]

/-- The order-`q` coefficient of every normalized right factor is `mu_q`. -/
theorem normalizedRightMomentFactor_coeff_eq
    {m q : ℕ} {mu : ℕ → ℚ} {h : ℚ}
    (hq : q ≤ m) (hqpos : 1 ≤ q)
    (hmu : LowerMuVanishes mu q) :
    (normalizedRightMomentFactor m mu h).coeff q = mu q := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hmuPrev : mu s = 0 := hmu s (Nat.lt_succ_self s)
  simp [normalizedRightMomentFactor,
    momentGeneratingPolynomial_coeff (a := mu) (by omega), hmuPrev]

/-- A product of `k` factors, each divisible by `X^q` with constant quotient
coefficient `a_i`, has coefficient `prod_i a_i` in order `qk`. -/
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

/-- Exact generating-series coefficient identity. -/
theorem normalizedMomentBlock_coeff
    {m k q : ℕ} {c : ℚ} {mu nu : ℕ → ℚ}
    (h : Fin k → ℚ)
    (hq : q ≤ m) (hqpos : 1 ≤ q) (hc : c = 0)
    (hmu : LowerMuVanishes mu q)
    (hnu : LowerNuVanishes nu q) :
    (normalizedMomentBlock m k c mu nu h).coeff (q * k) =
      momentBlockDelta mu nu q k := by
  have hdivLeft : ∀ i : Fin k,
      X ^ q ∣ normalizedLeftMomentFactor m c mu nu (h i) := by
    intro i
    rw [Polynomial.X_pow_dvd_iff]
    intro t ht
    exact normalizedLeftMomentFactor_coeff_lt hq hc hmu hnu ht
  have hdivRight : ∀ i : Fin k,
      X ^ q ∣ normalizedRightMomentFactor m mu (h i) := by
    intro i
    rw [Polynomial.X_pow_dvd_iff]
    intro t ht
    exact normalizedRightMomentFactor_coeff_lt hq hmu ht
  choose L hL using hdivLeft
  choose R hR using hdivRight
  have hLc : ∀ i : Fin k,
      (L i).coeff 0 = mu q + nu (q - 1) := by
    intro i
    have hcoeff := normalizedLeftMomentFactor_coeff_eq
      (c := c) (h := h i) hq hqpos hmu
    rw [hL i, Polynomial.coeff_X_pow_mul'] at hcoeff
    simpa using hcoeff
  have hRc : ∀ i : Fin k, (R i).coeff 0 = mu q := by
    intro i
    have hcoeff := normalizedRightMomentFactor_coeff_eq
      (h := h i) hq hqpos hmu
    rw [hR i, Polynomial.coeff_X_pow_mul'] at hcoeff
    simpa using hcoeff
  have hprodLeft :
      (∏ i : Fin k, normalizedLeftMomentFactor m c mu nu (h i)).coeff
          (q * k) = (mu q + nu (q - 1)) ^ k := by
    rw [coeff_prod_of_common_X_order _ L hL]
    simp [hLc]
  have hprodRight :
      (∏ i : Fin k, normalizedRightMomentFactor m mu (h i)).coeff
          (q * k) = mu q ^ k := by
    rw [coeff_prod_of_common_X_order _ R hR]
    simp [hRc]
  rw [normalizedMomentBlock, coeff_sub, coeff_C_mul,
    hprodLeft, hprodRight]
  rfl

/-- The normalized block has no coefficient below order `qk`. -/
theorem normalizedMomentBlock_coeff_lt
    {m k q t : ℕ} {c : ℚ} {mu nu : ℕ → ℚ}
    (h : Fin k → ℚ)
    (hq : q ≤ m) (hc : c = 0)
    (hmu : LowerMuVanishes mu q)
    (hnu : LowerNuVanishes nu q)
    (ht : t < q * k) :
    (normalizedMomentBlock m k c mu nu h).coeff t = 0 := by
  have hdivLeft : ∀ i : Fin k,
      X ^ q ∣ normalizedLeftMomentFactor m c mu nu (h i) := by
    intro i
    rw [Polynomial.X_pow_dvd_iff]
    intro s hs
    exact normalizedLeftMomentFactor_coeff_lt hq hc hmu hnu hs
  have hdivRight : ∀ i : Fin k,
      X ^ q ∣ normalizedRightMomentFactor m mu (h i) := by
    intro i
    rw [Polynomial.X_pow_dvd_iff]
    intro s hs
    exact normalizedRightMomentFactor_coeff_lt hq hmu hs
  choose L hL using hdivLeft
  choose R hR using hdivRight
  have hprodLeft : X ^ (q * k) ∣
      ∏ i : Fin k, normalizedLeftMomentFactor m c mu nu (h i) := by
    refine ⟨∏ i : Fin k, L i, ?_⟩
    simp_rw [hL]
    rw [Finset.prod_mul_distrib]
    simp [← pow_mul]
  have hprodRight : X ^ (q * k) ∣
      ∏ i : Fin k, normalizedRightMomentFactor m mu (h i) := by
    refine ⟨∏ i : Fin k, R i, ?_⟩
    simp_rw [hR]
    rw [Finset.prod_mul_distrib]
    simp [← pow_mul]
  have hblock : X ^ (q * k) ∣ normalizedMomentBlock m k c mu nu h := by
    rw [normalizedMomentBlock]
    exact dvd_sub hprodLeft (dvd_mul_of_dvd_right hprodRight (C 4))
  exact (Polynomial.X_pow_dvd_iff.mp hblock) t ht

/-- Rational version of the exact cancellation identity. -/
theorem rational_pow_eq_four_mul_pow_zero
    {x y : ℚ} {k : ℕ} (hk : 3 ≤ k)
    (hpow : x ^ k = 4 * y ^ k) : x = 0 ∧ y = 0 := by
  induction x using Rat.divCasesOn with
  | div xn xd hxd _ =>
      induction y using Rat.divCasesOn with
      | div yn yd hyd _ =>
          have hscaled := hpow
          field_simp [hxd, hyd] at hscaled
          have hInt :
              (xn * (yd : ℤ)) ^ k =
                4 * (yn * (xd : ℤ)) ^ k := by
            exact_mod_cast (by
              simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hscaled)
          obtain ⟨hx, hy⟩ := pow_eq_four_mul_pow_zero hk hInt
          have hxn : xn = 0 := by
            rcases mul_eq_zero.mp hx with hxn | hydz
            · exact hxn
            · exact False.elim (hxd (by exact_mod_cast hydz))
          have hyn : yn = 0 := by
            rcases mul_eq_zero.mp hy with hyn | hxdz
            · exact hyn
            · exact False.elim (hyd (by exact_mod_cast hxdz))
          constructor <;> simp [hxn, hyn]

/-- For rational moments and `k >= 3`, the next block cancels exactly when both
new moments vanish. -/
theorem momentBlockDelta_eq_zero_iff
    {mu nu : ℕ → ℚ} {q k : ℕ} (hk : 3 ≤ k) :
    momentBlockDelta mu nu q k = 0 ↔
      mu q = 0 ∧ nu (q - 1) = 0 := by
  constructor
  · intro hzero
    have hp : (mu q + nu (q - 1)) ^ k = 4 * mu q ^ k :=
      sub_eq_zero.mp hzero
    obtain ⟨hsum, hmu⟩ := rational_pow_eq_four_mul_pow_zero hk hp
    exact ⟨hmu, by linarith⟩
  · rintro ⟨hmu, hnu⟩
    simp [momentBlockDelta, hmu, hnu, show k ≠ 0 by omega]

/-- The first nonzero moment pair produces a genuinely nonzero next block. -/
theorem momentBlockDelta_ne_zero_of_first_nonzero
    {mu nu : ℕ → ℚ} {q k : ℕ} (hk : 3 ≤ k)
    (hpair : mu q ≠ 0 ∨ nu (q - 1) ≠ 0) :
    momentBlockDelta mu nu q k ≠ 0 := by
  intro hzero
  exact hpair.elim
    (fun hmu => hmu ((momentBlockDelta_eq_zero_iff hk).mp hzero).1)
    (fun hnu => hnu ((momentBlockDelta_eq_zero_iff hk).mp hzero).2)

/-- At-infinity degree-transfer certificate.  This is the exact interface that
must be supplied when the normalized generating block is attached to a
concrete matching polynomial. -/
structure MomentDegreeTransferCertificate
    (Phi block : Polynomial ℚ) (m k q : ℕ) : Prop where
  degree_of_first_nonzero_block :
    block.coeff (q * k) ≠ 0 → Phi.natDegree = k * (m - q)

/-- Once the at-infinity transfer is certified, the exact block identity gives
`deg Phi = k(m-q)` for the first nonzero moment pair. -/
theorem momentPhi_natDegree
    {m k q : ℕ} {c : ℚ} {mu nu : ℕ → ℚ}
    (h : Fin k → ℚ) (Phi : Polynomial ℚ)
    (hq : q ≤ m) (hqpos : 1 ≤ q) (hc : c = 0)
    (hmu : LowerMuVanishes mu q)
    (hnu : LowerNuVanishes nu q)
    (hk : 3 ≤ k)
    (hpair : mu q ≠ 0 ∨ nu (q - 1) ≠ 0)
    (htransfer : MomentDegreeTransferCertificate Phi
      (normalizedMomentBlock m k c mu nu h) m k q) :
    Phi.natDegree = k * (m - q) := by
  apply htransfer.degree_of_first_nonzero_block
  rw [normalizedMomentBlock_coeff h hq hqpos hc hmu hnu]
  exact momentBlockDelta_ne_zero_of_first_nonzero hk hpair

/-- Arithmetic identity behind division by a square support polynomial. -/
theorem moment_degree_subtract_square
    {m k q : ℕ} (hq : q ≤ m) (hk : 2 ≤ k)
    (hfeasible : q * k ≤ m * (k - 2)) :
    k * (m - q) = 2 * m + (m * (k - 2) - q * k) := by
  omega

/-- If `Phi = W^2 Q`, `deg W = m`, and the first nonzero block gives
`deg Phi = k(m-q)`, then `deg Q = m(k-2)-qk`. -/
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

/-- Vandermonde termination for arbitrary distinct rational nodes. -/
theorem barycentricMoment_vandermonde_termination
    {m : ℕ} {node weight : Fin m → ℚ}
    (hnode : Function.Injective node)
    (hmom : ∀ q < m, barycentricMoment node weight q = 0) :
    weight = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hnode
  intro q
  simpa [barycentricMoment] using hmom q.1 q.2

/-- Consecutive nodes `0,...,m-1` are a concrete Vandermonde instance. -/
theorem consecutive_barycentricMoment_termination
    {m : ℕ} {weight : Fin m → ℚ}
    (hmom : ∀ q < m,
      barycentricMoment (fun i : Fin m => (i.1 : ℚ)) weight q = 0) :
    weight = 0 := by
  apply barycentricMoment_vandermonde_termination
  · intro i j hij
    apply Fin.ext
    exact_mod_cast hij
  · exact hmom

#print axioms normalizedMomentBlock_coeff
#print axioms normalizedMomentBlock_coeff_lt
#print axioms rational_pow_eq_four_mul_pow_zero
#print axioms momentBlockDelta_eq_zero_iff
#print axioms momentBlockDelta_ne_zero_of_first_nonzero
#print axioms momentPhi_natDegree
#print axioms momentQuotient_natDegree
#print axioms barycentricMoment_vandermonde_termination
#print axioms consecutive_barycentricMoment_termination

end Erdos686Variant
end Erdos686
