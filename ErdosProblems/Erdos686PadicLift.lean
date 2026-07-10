/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686QuotientConfinement

/-!
# P-adic lift consequences for Erdős 686

This module records unconditional congruence consequences of an exact shifted
block identity.  The first layer is valid for every block length and every
multiplier.  The second layer localizes an odd prime power at its unique factor
in a block shorter than the prime.
-/

namespace Erdos686
namespace Erdos686Variant

/-- Translating every factor by `d` leaves the block product unchanged modulo
`d`. -/
lemma blockProduct_shift_modEq (k n d : ℕ) :
    blockProduct k (n + d) ≡ blockProduct k n [MOD d] := by
  unfold blockProduct
  apply Nat.ModEq.prod
  intro i hi
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Nat.ModEq.modulus_mul_add (m := d) (a := 1) (b := n + i))

/-- General gap congruence: an exact multiplier-`N` block identity forces the
gap to divide `(N-1)` times the lower block product. -/
theorem gap_dvd_multiplier_sub_one_blockProduct
    {N k n d : ℕ} (hN : 1 ≤ N)
    (heq : blockProduct k (n + d) = N * blockProduct k n) :
    d ∣ (N - 1) * blockProduct k n := by
  have hmod := blockProduct_shift_modEq k n d
  rw [heq] at hmod
  have hle : blockProduct k n ≤ N * blockProduct k n := by
    exact Nat.le_mul_of_pos_left (blockProduct k n) (by omega)
  have hdvd : d ∣ N * blockProduct k n - blockProduct k n :=
    (Nat.modEq_iff_dvd' hle).mp hmod.symm
  simpa [Nat.sub_mul] using hdvd

/-- At multiplier four, the gap divides three times the lower block product. -/
theorem gap_dvd_three_blockProduct
    {k n d : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    d ∣ 3 * blockProduct k n := by
  simpa using gap_dvd_multiplier_sub_one_blockProduct (N := 4) (by norm_num) heq

/-- The block polynomial with the factor indexed by `i` removed. -/
def localBlockCofactor (k i : ℕ) (x : ℤ) : ℤ :=
  ∏ j ∈ (Finset.Icc 1 k).erase i, (x + (j : ℤ))

/-- The signed derivative coefficient at the root `x = -i`. -/
def localBlockCoefficient (k i : ℕ) : ℤ :=
  localBlockCofactor k i (-(i : ℤ))

/-- Absolute value of the local derivative coefficient. -/
def localBlockCoefficientNat (k i : ℕ) : ℕ :=
  (i - 1).factorial * (k - i).factorial

private lemma prod_Icc_one_cast_eq_factorial (t : ℕ) :
    (∏ a ∈ Finset.Icc 1 t, (a : ℤ)) = ((t.factorial : ℕ) : ℤ) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
      push_cast
      ring

private lemma localBlockCoefficient_left_product (i : ℕ) :
    (∏ j ∈ Finset.Icc 1 (i - 1), ((j : ℤ) - (i : ℤ))) =
      (-1 : ℤ) ^ (i - 1) * ((i - 1).factorial : ℕ) := by
  by_cases hi0 : i = 0
  · subst i
    norm_num
  have hi1 : 1 ≤ i := by omega
  have hreflect :
      (∏ j ∈ Finset.Icc 1 (i - 1), ((j : ℤ) - (i : ℤ))) =
        ∏ a ∈ Finset.Icc 1 (i - 1), -(a : ℤ) := by
    refine Finset.prod_bij'
      (fun j _hj => i - j) (fun a _ha => i - a) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      constructor <;> omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      constructor <;> omega
    · intro j hj
      change i - (i - j) = j
      apply tsub_tsub_cancel_of_le
      have := (Finset.mem_Icc.mp hj).2
      omega
    · intro a ha
      change i - (i - a) = a
      apply tsub_tsub_cancel_of_le
      have := (Finset.mem_Icc.mp ha).2
      omega
    · intro j hj
      have hji : j ≤ i := by
        have := (Finset.mem_Icc.mp hj).2
        omega
      rw [Nat.cast_sub hji]
      ring
  rw [hreflect, Finset.prod_neg, Nat.card_Icc,
    prod_Icc_one_cast_eq_factorial]
  simp [hi1]

private lemma localBlockCoefficient_right_product {k i : ℕ} (hik : i ≤ k) :
    (∏ j ∈ Finset.Icc (i + 1) k, ((j : ℤ) - (i : ℤ))) =
      (((k - i).factorial : ℕ) : ℤ) := by
  have hreindex :
      (∏ j ∈ Finset.Icc (i + 1) k, ((j : ℤ) - (i : ℤ))) =
        ∏ a ∈ Finset.Icc 1 (k - i), (a : ℤ) := by
    refine Finset.prod_bij'
      (fun j _hj => j - i) (fun a _ha => i + a) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      constructor <;> omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      constructor <;> omega
    · intro j hj
      change i + (j - i) = j
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel (by
        have := (Finset.mem_Icc.mp hj).1
        omega)
    · intro a ha
      change i + a - i = a
      omega
    · intro j hj
      have hij : i ≤ j := by
        have := (Finset.mem_Icc.mp hj).1
        omega
      rw [Nat.cast_sub hij]
  rw [hreindex, prod_Icc_one_cast_eq_factorial]

/-- Closed form for the signed local derivative coefficient. -/
lemma localBlockCoefficient_eq_sign_mul_nat
    {k i : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    localBlockCoefficient k i =
      (-1 : ℤ) ^ (i - 1) * (localBlockCoefficientNat k i : ℤ) := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have herase :
      (Finset.Icc 1 k).erase i =
        Finset.Icc 1 (i - 1) ∪ Finset.Icc (i + 1) k := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisjoint :
      Disjoint (Finset.Icc 1 (i - 1)) (Finset.Icc (i + 1) k) := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjleft hjright
    simp only [Finset.mem_Icc] at hjleft hjright
    omega
  unfold localBlockCoefficient localBlockCofactor localBlockCoefficientNat
  rw [herase, Finset.prod_union hdisjoint]
  have hleft := localBlockCoefficient_left_product i
  have hright := localBlockCoefficient_right_product hik
  rw [show (∏ x ∈ Finset.Icc 1 (i - 1), (-(i : ℤ) + (x : ℤ))) =
      (-1 : ℤ) ^ (i - 1) * ((i - 1).factorial : ℕ) by
        simpa [sub_eq_add_neg, add_comm] using hleft,
    show (∏ x ∈ Finset.Icc (i + 1) k, (-(i : ℤ) + (x : ℤ))) =
      (((k - i).factorial : ℕ) : ℤ) by
        simpa [sub_eq_add_neg, add_comm] using hright]
  push_cast
  ring

lemma intBlockProduct_eq_factor_mul_localBlockCofactor
    {k i : ℕ} (x : ℤ) (hi : i ∈ Finset.Icc 1 k) :
    intBlockProduct k x =
      (x + (i : ℤ)) * localBlockCofactor k i x := by
  unfold intBlockProduct localBlockCofactor
  exact (Finset.mul_prod_erase (Finset.Icc 1 k) (fun j => x + (j : ℤ)) hi).symm

lemma localBlockCofactor_modEq
    {k i : ℕ} {x y M : ℤ} (hxy : x ≡ y [ZMOD M]) :
    localBlockCofactor k i x ≡ localBlockCofactor k i y [ZMOD M] := by
  unfold localBlockCofactor
  apply Int.ModEq.prod
  intro j hj
  exact hxy.add (Int.ModEq.refl (j : ℤ))

private lemma int_modEq_neg_index_of_dvd_add
    {h n i : ℕ} (hdiv : h ∣ n + i) :
    (n : ℤ) ≡ -(i : ℤ) [ZMOD (h : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  have hcast : (h : ℤ) ∣ ((n + i : ℕ) : ℤ) := by
    exact_mod_cast hdiv
  have hneg := dvd_neg.mpr hcast
  convert hneg using 1
  push_cast
  ring

/-- Raw local quadratic lift.  If `h` divides both the gap and one lower
factor, then modulo `h²` the exact block equation retains only its linear
term at that factor.  No primality or uniqueness hypothesis is needed at this
stage. -/
theorem localBlockCoefficient_mul_three_factor_sub_gap_dvd_sq
    {k n d i h : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hd : h ∣ d)
    (hfactor : h ∣ n + i)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ^ 2 ∣
      localBlockCoefficient k i * (3 * ((n + i : ℕ) : ℤ) - (d : ℤ)) := by
  let C : ℤ := localBlockCoefficient k i
  let L : ℤ := ((n + i : ℕ) : ℤ)
  let U : ℤ := ((n + d + i : ℕ) : ℤ)
  let QL : ℤ := localBlockCofactor k i (n : ℤ)
  let QU : ℤ := localBlockCofactor k i ((n + d : ℕ) : ℤ)
  have hnmod : (n : ℤ) ≡ -(i : ℤ) [ZMOD (h : ℤ)] :=
    int_modEq_neg_index_of_dvd_add hfactor
  have hndfactor : h ∣ n + d + i := by
    have : h ∣ (n + i) + d := dvd_add hfactor hd
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have hnumod : ((n + d : ℕ) : ℤ) ≡ -(i : ℤ) [ZMOD (h : ℤ)] := by
    have := int_modEq_neg_index_of_dvd_add (n := n + d) (i := i) hndfactor
    simpa [Nat.add_assoc] using this
  have hQLmod : QL ≡ C [ZMOD (h : ℤ)] := by
    exact localBlockCofactor_modEq hnmod
  have hQUmod : QU ≡ C [ZMOD (h : ℤ)] := by
    exact localBlockCofactor_modEq hnumod
  have hL : (h : ℤ) ∣ L := by
    dsimp [L]
    exact_mod_cast hfactor
  have hU : (h : ℤ) ∣ U := by
    dsimp [U]
    exact_mod_cast hndfactor
  have hQLerr : (h : ℤ) ∣ QL - C := by
    have := hQLmod.dvd
    simpa [sub_eq_add_neg, add_comm] using (dvd_neg.mpr this)
  have hQUerr : (h : ℤ) ∣ QU - C := by
    have := hQUmod.dvd
    simpa [sub_eq_add_neg, add_comm] using (dvd_neg.mpr this)
  have hLowerSq : (h : ℤ) ^ 2 ∣ L * (QL - C) := by
    simpa [pow_two] using mul_dvd_mul hL hQLerr
  have hUpperSq : (h : ℤ) ^ 2 ∣ U * (QU - C) := by
    simpa [pow_two] using mul_dvd_mul hU hQUerr
  have heqInt :
      intBlockProduct k ((n + d : ℕ) : ℤ) =
        4 * intBlockProduct k (n : ℤ) := by
    rw [intBlockProduct_natCast, intBlockProduct_natCast]
    exact_mod_cast heq
  have heqLocal : U * QU = 4 * L * QL := by
    rw [intBlockProduct_eq_factor_mul_localBlockCofactor
        ((n + d : ℕ) : ℤ) hi,
      intBlockProduct_eq_factor_mul_localBlockCofactor (n : ℤ) hi] at heqInt
    simpa [U, L, QU, QL, Nat.cast_add, mul_assoc] using heqInt
  have hidentity :
      C * (3 * L - (d : ℤ)) = U * (QU - C) - 4 * (L * (QL - C)) := by
    have hUL : U = L + (d : ℤ) := by
      simp [U, L, Nat.cast_add]
      ring
    rw [hUL] at heqLocal ⊢
    calc
      C * (3 * L - (d : ℤ)) =
          -(L + (d : ℤ)) * C + 4 * L * C := by ring
      _ = ((L + (d : ℤ)) * QU - 4 * L * QL) -
            (L + (d : ℤ)) * C + 4 * L * C := by rw [heqLocal]; ring
      _ = (L + (d : ℤ)) * (QU - C) - 4 * (L * (QL - C)) := by ring
  rw [show localBlockCoefficient k i = C by rfl]
  change (h : ℤ) ^ 2 ∣ C * (3 * L - (d : ℤ))
  rw [hidentity]
  exact dvd_sub hUpperSq (dvd_mul_of_dvd_right hLowerSq 4)

/-- Positive-coefficient form of the raw local quadratic lift. -/
theorem localBlockCoefficientNat_mul_three_factor_sub_gap_dvd_sq
    {k n d i h : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hd : h ∣ d)
    (hfactor : h ∣ n + i)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ^ 2 ∣
      (localBlockCoefficientNat k i : ℤ) *
        (3 * ((n + i : ℕ) : ℤ) - (d : ℤ)) := by
  have hsigned :=
    localBlockCoefficient_mul_three_factor_sub_gap_dvd_sq hi hd hfactor heq
  rw [localBlockCoefficient_eq_sign_mul_nat hi] at hsigned
  rcases neg_one_pow_eq_or ℤ (i - 1) with hsign | hsign
  · simpa [hsign, mul_assoc, mul_comm, mul_left_comm] using hsigned
  · have hneg := dvd_neg.mpr hsigned
    simpa [hsign, mul_assoc, mul_comm, mul_left_comm] using hneg

lemma prime_not_dvd_localBlockCoefficientNat
    {p k i : ℕ} (hp : p.Prime) (hkp : k ≤ p)
    (hi : i ∈ Finset.Icc 1 k) :
    ¬ p ∣ localBlockCoefficientNat k i := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  intro hdiv
  rcases hp.dvd_mul.mp hdiv with hleft | hright
  · have hple : p ≤ i - 1 := hp.dvd_factorial.mp hleft
    omega
  · have hple : p ≤ k - i := hp.dvd_factorial.mp hright
    omega

/-- Prime-power cancellation of the local derivative.  The boundary `p = k`
is allowed: every nonzero root difference has absolute value at most `k-1`. -/
theorem primePower_sq_dvd_three_factor_sub_gap
    {p e k n d i : ℕ}
    (hp : p.Prime)
    (hkp : k ≤ p)
    (hi : i ∈ Finset.Icc 1 k)
    (hd : p ^ e ∣ d)
    (hfactor : p ^ e ∣ n + i)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (((p ^ e : ℕ) : ℤ) ^ 2) ∣
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
  have hraw :=
    localBlockCoefficientNat_mul_three_factor_sub_gap_dvd_sq hi hd hfactor heq
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpCoeff : ¬ (p : ℤ) ∣ (localBlockCoefficientNat k i : ℤ) := by
    intro hdiv
    apply prime_not_dvd_localBlockCoefficientNat hp hkp hi
    exact Int.natCast_dvd_natCast.mp hdiv
  have hraw' :
      (p : ℤ) ^ (e * 2) ∣
        (localBlockCoefficientNat k i : ℤ) *
          (3 * ((n + i : ℕ) : ℤ) - (d : ℤ)) := by
    simpa [Nat.cast_pow, ← pow_mul] using hraw
  have hcancel := hpInt.pow_dvd_of_dvd_mul_left (e * 2) hpCoeff hraw'
  simpa [Nat.cast_pow, ← pow_mul] using hcancel

/-- Uniqueness of a prime-supported factor remains valid at the boundary
`p = k`; the interval indices start at one, so two distinct indices differ by
strictly less than `k`. -/
lemma unique_dvd_add_of_mem_Icc_of_le
    {p k a r s : ℕ}
    (hkp : k ≤ p)
    (hr : r ∈ Finset.Icc 1 k)
    (hs : s ∈ Finset.Icc 1 k)
    (hpr : p ∣ a + r)
    (hps : p ∣ a + s) :
    r = s := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · have hpDiff : p ∣ (a + s) - (a + r) := Nat.dvd_sub hps hpr
    have hdiff : (a + s) - (a + r) = s - r := by omega
    rw [hdiff] at hpDiff
    have hpos : 0 < s - r := Nat.sub_pos_of_lt hrs
    have hple : p ≤ s - r := Nat.le_of_dvd hpos hpDiff
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hsk : s ≤ k := (Finset.mem_Icc.mp hs).2
    omega
  · have hpDiff : p ∣ (a + r) - (a + s) := Nat.dvd_sub hpr hps
    have hdiff : (a + r) - (a + s) = r - s := by omega
    rw [hdiff] at hpDiff
    have hpos : 0 < r - s := Nat.sub_pos_of_lt hsr
    have hple : p ≤ r - s := Nat.le_of_dvd hpos hpDiff
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hrk : r ≤ k := (Finset.mem_Icc.mp hr).2
    omega

def localBlockCofactorNat (k i n : ℕ) : ℕ :=
  ∏ j ∈ (Finset.Icc 1 k).erase i, (n + j)

lemma blockProduct_eq_factor_mul_localBlockCofactorNat
    {k i n : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    blockProduct k n = (n + i) * localBlockCofactorNat k i n := by
  unfold blockProduct localBlockCofactorNat
  exact (Finset.mul_prod_erase (Finset.Icc 1 k) (fun j => n + j) hi).symm

/-- A prime power dividing a block shorter than (or equal in length to) its
prime base lies wholly in one unique factor. -/
theorem primePower_dvd_blockProduct_existsUnique
    {p e k n : ℕ}
    (hp : p.Prime)
    (he : 0 < e)
    (hkp : k ≤ p)
    (hpow : p ^ e ∣ blockProduct k n) :
    ∃! i, i ∈ Finset.Icc 1 k ∧ p ^ e ∣ n + i := by
  have hp_dvd_pow : p ∣ p ^ e := by
    simpa using (pow_dvd_pow p (by omega : 1 ≤ e))
  have hpProd : p ∣ blockProduct k n := dvd_trans hp_dvd_pow hpow
  obtain ⟨i, hi, hpi⟩ := (prime_dvd_blockProduct_iff hp).mp hpProd
  have hpCofactor : ¬ p ∣ localBlockCofactorNat k i n := by
    intro hdiv
    obtain ⟨j, hjErase, hpj⟩ :=
      (hp.prime.dvd_finset_prod_iff
        (S := (Finset.Icc 1 k).erase i) (g := fun j => n + j)).mp hdiv
    have hjne : j ≠ i := (Finset.mem_erase.mp hjErase).1
    have hj : j ∈ Finset.Icc 1 k := (Finset.mem_erase.mp hjErase).2
    exact hjne (unique_dvd_add_of_mem_Icc_of_le hkp hj hi hpj hpi)
  have hpowMul : p ^ e ∣ (n + i) * localBlockCofactorNat k i n := by
    rw [← blockProduct_eq_factor_mul_localBlockCofactorNat hi]
    exact hpow
  have hpowFactor : p ^ e ∣ n + i :=
    hp.prime.pow_dvd_of_dvd_mul_right e hpCofactor hpowMul
  refine ⟨i, ⟨hi, hpowFactor⟩, ?_⟩
  intro j hj
  have hpj : p ∣ n + j := dvd_trans hp_dvd_pow hj.2
  exact unique_dvd_add_of_mem_Icc_of_le hkp hj.1 hi hpj hpi

/-- Every prime power of the gap with prime base different from three also
divides the lower block product. -/
theorem primePower_dvd_lower_block_of_dvd_gap
    {p e k n d : ℕ}
    (hp : p.Prime)
    (hp3 : p ≠ 3)
    (hd : p ^ e ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    p ^ e ∣ blockProduct k n := by
  have hpowProd : p ^ e ∣ 3 * blockProduct k n :=
    dvd_trans hd (gap_dvd_three_blockProduct heq)
  have hpNotThree : ¬ p ∣ 3 := by
    intro hdiv
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdiv with hp1 | hp3'
    · exact hp.ne_one hp1
    · exact hp3 hp3'
  exact hp.prime.pow_dvd_of_dvd_mul_left e hpNotThree hpowProd

/-- Global-to-local prime-power lift.  A positive prime power of the gap, with
`p ≥ k ≥ 4`, selects one unique lower factor and forces the clean square
congruence there. -/
theorem gap_primePower_existsUnique_local_sq_lift
    {p e k n d : ℕ}
    (hp : p.Prime)
    (he : 0 < e)
    (hk4 : 4 ≤ k)
    (hkp : k ≤ p)
    (hd : p ^ e ∣ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃! i, i ∈ Finset.Icc 1 k ∧ p ^ e ∣ n + i ∧
      (((p ^ e : ℕ) : ℤ) ^ 2) ∣
        3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
  have hp3 : p ≠ 3 := by omega
  have hblock := primePower_dvd_lower_block_of_dvd_gap hp hp3 hd heq
  obtain ⟨i, hi, huniq⟩ :=
    primePower_dvd_blockProduct_existsUnique hp he hkp hblock
  refine ⟨i, ⟨hi.1, hi.2,
    primePower_sq_dvd_three_factor_sub_gap hp hkp hi.1 hd hi.2 heq⟩, ?_⟩
  intro j hj
  exact huniq j ⟨hj.1, hj.2.1⟩

/-- Remove the two endpoints of a block and shift the remaining block by one. -/
lemma blockProduct_add_two (k n : ℕ) :
    blockProduct (k + 2) n =
      (n + 1) * blockProduct k (n + 1) * (n + k + 2) := by
  rw [show k + 2 = (k + 1) + 1 by omega, blockProduct_succ,
    blockProduct_succ]
  have hpred := blockProduct_pred_mul k (n + 1) (by omega)
  have hshift : n + 1 - 1 = n := by omega
  rw [hshift] at hpred
  have hpred' :
      blockProduct k n * (n + k + 1) =
        (n + 1) * blockProduct k (n + 1) := by
    calc
      blockProduct k n * (n + k + 1) =
          blockProduct k n * (n + 1 + k) := by
            rw [show n + k + 1 = n + 1 + k by omega]
      _ = blockProduct k (n + 1) * (n + 1) := hpred
      _ = (n + 1) * blockProduct k (n + 1) := by ring
  calc
    blockProduct k n * (n + k + 1) * (n + (k + 1) + 1) =
        (n + 1) * blockProduct k (n + 1) * (n + k + 2) := by
          rw [hpred', show n + (k + 1) + 1 = n + k + 2 by omega]

/-- Paired cofactor of an odd block about its middle factor. -/
def centerBlockCofactor (r : ℕ) (z : ℤ) : ℤ :=
  ∏ a ∈ Finset.Icc 1 r, (z ^ 2 - (a : ℤ) ^ 2)

lemma centerBlockCofactor_succ (r : ℕ) (z : ℤ) :
    centerBlockCofactor (r + 1) z =
      centerBlockCofactor r z * (z ^ 2 - ((r + 1 : ℕ) : ℤ) ^ 2) := by
  unfold centerBlockCofactor
  rw [Finset.prod_Icc_succ_top]
  omega

/-- Exact centered factorization of an odd block. -/
lemma odd_blockProduct_center_factorization (r n : ℕ) :
    ((blockProduct (2 * r + 1) n : ℕ) : ℤ) =
      ((n + r + 1 : ℕ) : ℤ) *
        centerBlockCofactor r ((n + r + 1 : ℕ) : ℤ) := by
  induction r generalizing n with
  | zero =>
      simp [blockProduct, centerBlockCofactor, Finset.Icc_self, Finset.prod_singleton]
  | succ r ih =>
      rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega,
        blockProduct_add_two]
      rw [Nat.cast_mul, Nat.cast_mul, ih (n + 1), centerBlockCofactor_succ]
      push_cast
      ring

lemma centerBlockCofactor_modEq_of_sq
    {r : ℕ} {x y M : ℤ} (hxy : x ^ 2 ≡ y ^ 2 [ZMOD M]) :
    centerBlockCofactor r x ≡ centerBlockCofactor r y [ZMOD M] := by
  unfold centerBlockCofactor
  apply Int.ModEq.prod
  intro a ha
  exact hxy.sub (Int.ModEq.refl ((a : ℤ) ^ 2))

lemma centerBlockCofactor_zero (r : ℕ) :
    centerBlockCofactor r 0 =
      (-1 : ℤ) ^ r * ((r.factorial : ℕ) : ℤ) ^ 2 := by
  unfold centerBlockCofactor
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_sub]
  rw [show (∏ a ∈ Finset.Icc 1 r, -((a : ℤ) ^ 2)) =
      (∏ _a ∈ Finset.Icc 1 r, (-1 : ℤ)) *
        ∏ a ∈ Finset.Icc 1 r, ((a : ℤ) ^ 2) by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro a ha
        ring]
  rw [Finset.prod_const, Nat.card_Icc]
  simp only [Nat.add_one_sub_one]
  rw [Finset.prod_pow]
  have hprod := prod_Icc_one_cast_eq_factorial r
  rw [hprod]

/-- Middle-factor cubic lift for an odd block.  Pairing the factors around the
middle eliminates every quadratic Taylor term, so the same exact equation
that gives an `h²` lift at a general factor gives an `h³` lift here. -/
theorem center_factorial_sq_mul_three_factor_sub_gap_dvd_cube
    {r n d h : ℕ}
    (hd : h ∣ d)
    (hcenter : h ∣ n + r + 1)
    (heq : blockProduct (2 * r + 1) (n + d) =
      4 * blockProduct (2 * r + 1) n) :
    (h : ℤ) ^ 3 ∣
      ((r.factorial : ℕ) : ℤ) ^ 2 *
        (3 * ((n + r + 1 : ℕ) : ℤ) - (d : ℤ)) := by
  let C : ℤ := centerBlockCofactor r 0
  let L : ℤ := ((n + r + 1 : ℕ) : ℤ)
  let U : ℤ := ((n + d + r + 1 : ℕ) : ℤ)
  let QL : ℤ := centerBlockCofactor r L
  let QU : ℤ := centerBlockCofactor r U
  have hUpperCenter : h ∣ n + d + r + 1 := by
    have : h ∣ (n + r + 1) + d := dvd_add hcenter hd
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have hL : (h : ℤ) ∣ L := by
    dsimp [L]
    exact_mod_cast hcenter
  have hU : (h : ℤ) ∣ U := by
    dsimp [U]
    exact_mod_cast hUpperCenter
  have hLsq : (h : ℤ) ^ 2 ∣ L ^ 2 :=
    pow_dvd_pow_of_dvd hL 2
  have hUsq : (h : ℤ) ^ 2 ∣ U ^ 2 :=
    pow_dvd_pow_of_dvd hU 2
  have hQLmod : QL ≡ C [ZMOD (h : ℤ) ^ 2] := by
    exact centerBlockCofactor_modEq_of_sq hLsq.modEq_zero_int
  have hQUmod : QU ≡ C [ZMOD (h : ℤ) ^ 2] := by
    exact centerBlockCofactor_modEq_of_sq hUsq.modEq_zero_int
  have hQLerr : (h : ℤ) ^ 2 ∣ QL - C := by
    have := hQLmod.dvd
    simpa [sub_eq_add_neg, add_comm] using (dvd_neg.mpr this)
  have hQUerr : (h : ℤ) ^ 2 ∣ QU - C := by
    have := hQUmod.dvd
    simpa [sub_eq_add_neg, add_comm] using (dvd_neg.mpr this)
  have hLowerCube : (h : ℤ) ^ 3 ∣ L * (QL - C) := by
    simpa [pow_succ, pow_two, mul_assoc, mul_comm, mul_left_comm] using
      mul_dvd_mul hL hQLerr
  have hUpperCube : (h : ℤ) ^ 3 ∣ U * (QU - C) := by
    simpa [pow_succ, pow_two, mul_assoc, mul_comm, mul_left_comm] using
      mul_dvd_mul hU hQUerr
  have heqInt :
      ((blockProduct (2 * r + 1) (n + d) : ℕ) : ℤ) =
        4 * ((blockProduct (2 * r + 1) n : ℕ) : ℤ) := by
    exact_mod_cast heq
  rw [odd_blockProduct_center_factorization,
    odd_blockProduct_center_factorization] at heqInt
  have heqLocal : U * QU = 4 * L * QL := by
    simpa [U, L, QU, QL, Nat.cast_add, mul_assoc] using heqInt
  have hUL : U = L + (d : ℤ) := by
    simp [U, L, Nat.cast_add]
    ring
  have hidentity :
      C * (3 * L - (d : ℤ)) = U * (QU - C) - 4 * (L * (QL - C)) := by
    rw [hUL] at heqLocal ⊢
    calc
      C * (3 * L - (d : ℤ)) =
          -(L + (d : ℤ)) * C + 4 * L * C := by ring
      _ = ((L + (d : ℤ)) * QU - 4 * L * QL) -
            (L + (d : ℤ)) * C + 4 * L * C := by rw [heqLocal]; ring
      _ = (L + (d : ℤ)) * (QU - C) - 4 * (L * (QL - C)) := by ring
  have hSigned : (h : ℤ) ^ 3 ∣ C * (3 * L - (d : ℤ)) := by
    rw [hidentity]
    exact dvd_sub hUpperCube (dvd_mul_of_dvd_right hLowerCube 4)
  rw [show C = (-1 : ℤ) ^ r * ((r.factorial : ℕ) : ℤ) ^ 2 by
    exact centerBlockCofactor_zero r] at hSigned
  change (h : ℤ) ^ 3 ∣
    ((r.factorial : ℕ) : ℤ) ^ 2 * (3 * L - (d : ℤ))
  rcases neg_one_pow_eq_or ℤ r with hsign | hsign
  · simpa [hsign, mul_assoc, mul_comm, mul_left_comm] using hSigned
  · have hneg := dvd_neg.mpr hSigned
    simpa [hsign, mul_assoc, mul_comm, mul_left_comm] using hneg

/-- Prime-power cancellation of the middle-factor coefficient. -/
theorem primePower_cube_dvd_three_center_sub_gap
    {p e r n d : ℕ}
    (hp : p.Prime)
    (hkp : 2 * r + 1 ≤ p)
    (hd : p ^ e ∣ d)
    (hcenter : p ^ e ∣ n + r + 1)
    (heq : blockProduct (2 * r + 1) (n + d) =
      4 * blockProduct (2 * r + 1) n) :
    (((p ^ e : ℕ) : ℤ) ^ 3) ∣
      3 * ((n + r + 1 : ℕ) : ℤ) - (d : ℤ) := by
  have hraw :=
    center_factorial_sq_mul_three_factor_sub_gap_dvd_cube hd hcenter heq
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpFact : ¬ p ∣ r.factorial := by
    rw [hp.dvd_factorial]
    omega
  have hpCoeffNat : ¬ p ∣ r.factorial ^ 2 := by
    intro hdiv
    exact hpFact (hp.dvd_of_dvd_pow hdiv)
  have hpCoeff : ¬ (p : ℤ) ∣ (((r.factorial : ℕ) : ℤ) ^ 2) := by
    intro hdiv
    apply hpCoeffNat
    exact Int.natCast_dvd_natCast.mp (by simpa using hdiv)
  have hraw' :
      (p : ℤ) ^ (e * 3) ∣
        (((r.factorial : ℕ) : ℤ) ^ 2) *
          (3 * ((n + r + 1 : ℕ) : ℤ) - (d : ℤ)) := by
    simpa [Nat.cast_pow, ← pow_mul] using hraw
  have hcancel := hpInt.pow_dvd_of_dvd_mul_left (e * 3) hpCoeff hraw'
  simpa [Nat.cast_pow, ← pow_mul] using hcancel

private lemma local_lift_pow_lt_of_base_bound
    {q t C A k n d i : ℕ}
    (hk5 : 5 ≤ k)
    (hkd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hlift : (q : ℤ) ^ t ∣
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ)) :
    q ^ t < A * d := by
  have hgap := twice_gap_lt_n_of_four_solution hk5 hkd heq
  have hdlt : d < 3 * (n + i) := by omega
  let X : ℕ := 3 * (n + i) - d
  have hXpos : 0 < X := by
    dsimp [X]
    omega
  have hcast : (X : ℤ) =
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) := by
    dsimp [X]
    rw [Int.ofNat_sub (by omega : d ≤ 3 * (n + i))]
    push_cast
    ring
  have hdivCast : (((q ^ t : ℕ) : ℤ)) ∣ (X : ℤ) := by
    rw [hcast]
    simpa [Nat.cast_pow] using hlift
  have hdivNat : q ^ t ∣ X := Int.natCast_dvd_natCast.mp hdivCast
  have hqleX : q ^ t ≤ X := Nat.le_of_dvd hXpos hdivNat
  have hi_d : i ≤ d := le_trans (Finset.mem_Icc.mp hi).2 hkd
  have hnCd : n < C * d := by omega
  have h3n : 3 * n < 3 * (C * d) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 3)).mpr hnCd
  have h3i : 3 * i ≤ 3 * d := Nat.mul_le_mul_left 3 hi_d
  have hsum : 3 * (n + i) < (3 * C + 3) * d := by
    calc
      3 * (n + i) = 3 * n + 3 * i := by ring
      _ ≤ 3 * n + 3 * d := Nat.add_le_add_left h3i (3 * n)
      _ < 3 * (C * d) + 3 * d := Nat.add_lt_add_right h3n (3 * d)
      _ = (3 * C + 3) * d := by ring
  have hsumA : 3 * (n + i) < (A + 1) * d := by
    simpa [hA] using hsum
  have hXd : X + d = 3 * (n + i) := by
    dsimp [X]
    omega
  have hAd : A * d + d = (A + 1) * d := by ring
  have hXupper : X < A * d := by omega
  exact lt_of_le_of_lt hqleX hXupper

/-- Quantified odd-block package: each large prime power of the gap lands at
one factor, gives a square-size bound there, and gains a cubic-size bound if
that factor is the center. -/
theorem gap_primePower_existsUnique_odd_local_bounds
    {p e r n d C A : ℕ}
    (hp : p.Prime)
    (he : 0 < e)
    (hr2 : 2 ≤ r)
    (hkp : 2 * r + 1 ≤ p)
    (hkd : 2 * r + 1 ≤ d)
    (hd : p ^ e ∣ d)
    (heq : blockProduct (2 * r + 1) (n + d) =
      4 * blockProduct (2 * r + 1) n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2) :
    ∃! i, i ∈ Finset.Icc 1 (2 * r + 1) ∧ p ^ e ∣ n + i ∧
      (p ^ e) ^ 2 < A * d ∧
      (i = r + 1 → (p ^ e) ^ 3 < A * d) := by
  obtain ⟨i, hi, huniq⟩ := gap_primePower_existsUnique_local_sq_lift
    hp he (by omega : 4 ≤ 2 * r + 1) hkp hd heq
  have hsquare : (p ^ e) ^ 2 < A * d :=
    local_lift_pow_lt_of_base_bound (by omega : 5 ≤ 2 * r + 1)
      hkd hi.1 heq hbase hA hi.2.2
  have hcenterBound : i = r + 1 → (p ^ e) ^ 3 < A * d := by
    intro hicenter
    subst i
    have hcubic := primePower_cube_dvd_three_center_sub_gap
      hp hkp hd hi.2.1 heq
    exact local_lift_pow_lt_of_base_bound (by omega : 5 ≤ 2 * r + 1)
      hkd hi.1 heq hbase hA hcubic
  refine ⟨i, ⟨hi.1, hi.2.1, hsquare, hcenterBound⟩, ?_⟩
  intro j hj
  apply huniq j
  exact ⟨hj.1, hj.2.1,
    primePower_sq_dvd_three_factor_sub_gap hp hkp hj.1 hd hj.2.1 heq⟩

theorem gap_primePower_k5_local_bounds
    {p e n d : ℕ} (hp : p.Prime) (he : 0 < e)
    (hkp : 5 ≤ p) (hkd : 5 ≤ d) (hd : p ^ e ∣ d)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    ∃! i, i ∈ Finset.Icc 1 5 ∧ p ^ e ∣ n + i ∧
      (p ^ e) ^ 2 < 14 * d ∧ (i = 3 → (p ^ e) ^ 3 < 14 * d) := by
  have hbase := row_base_upper_k5 (ratio_window_four_nat heq).2
  exact gap_primePower_existsUnique_odd_local_bounds
    (r := 2) (C := 4) (A := 14)
    hp he (by norm_num) hkp hkd hd heq hbase (by norm_num)

theorem gap_primePower_k7_local_bounds
    {p e n d : ℕ} (hp : p.Prime) (he : 0 < e)
    (hkp : 7 ≤ p) (hkd : 7 ≤ d) (hd : p ^ e ∣ d)
    (heq : blockProduct 7 (n + d) = 4 * blockProduct 7 n) :
    ∃! i, i ∈ Finset.Icc 1 7 ∧ p ^ e ∣ n + i ∧
      (p ^ e) ^ 2 < 17 * d ∧ (i = 4 → (p ^ e) ^ 3 < 17 * d) := by
  have hbase := row_base_upper_k7 (ratio_window_four_nat heq).2
  exact gap_primePower_existsUnique_odd_local_bounds
    (r := 3) (C := 5) (A := 17)
    hp he (by norm_num) hkp hkd hd heq hbase (by norm_num)

theorem gap_primePower_k9_local_bounds
    {p e n d : ℕ} (hp : p.Prime) (he : 0 < e)
    (hkp : 9 ≤ p) (hkd : 9 ≤ d) (hd : p ^ e ∣ d)
    (heq : blockProduct 9 (n + d) = 4 * blockProduct 9 n) :
    ∃! i, i ∈ Finset.Icc 1 9 ∧ p ^ e ∣ n + i ∧
      (p ^ e) ^ 2 < 23 * d ∧ (i = 5 → (p ^ e) ^ 3 < 23 * d) := by
  have hbase := row_base_upper_k9 (ratio_window_four_nat heq).2
  exact gap_primePower_existsUnique_odd_local_bounds
    (r := 4) (C := 7) (A := 23)
    hp he (by norm_num) hkp hkd hd heq hbase (by norm_num)

theorem gap_primePower_k11_local_bounds
    {p e n d : ℕ} (hp : p.Prime) (he : 0 < e)
    (hkp : 11 ≤ p) (hkd : 11 ≤ d) (hd : p ^ e ∣ d)
    (heq : blockProduct 11 (n + d) = 4 * blockProduct 11 n) :
    ∃! i, i ∈ Finset.Icc 1 11 ∧ p ^ e ∣ n + i ∧
      (p ^ e) ^ 2 < 26 * d ∧ (i = 6 → (p ^ e) ^ 3 < 26 * d) := by
  have hbase := row_base_upper_k11 (ratio_window_four_nat heq).2
  exact gap_primePower_existsUnique_odd_local_bounds
    (r := 5) (C := 8) (A := 26)
    hp he (by norm_num) hkp hkd hd heq hbase (by norm_num)

theorem gap_primePower_k13_local_bounds
    {p e n d : ℕ} (hp : p.Prime) (he : 0 < e)
    (hkp : 13 ≤ p) (hkd : 13 ≤ d) (hd : p ^ e ∣ d)
    (heq : blockProduct 13 (n + d) = 4 * blockProduct 13 n) :
    ∃! i, i ∈ Finset.Icc 1 13 ∧ p ^ e ∣ n + i ∧
      (p ^ e) ^ 2 < 29 * d ∧ (i = 7 → (p ^ e) ^ 3 < 29 * d) := by
  have hbase := row_base_upper_k13 (ratio_window_four_nat heq).2
  exact gap_primePower_existsUnique_odd_local_bounds
    (r := 6) (C := 9) (A := 29)
    hp he (by norm_num) hkp hkd hd heq hbase (by norm_num)

theorem gap_primePower_k15_local_bounds
    {p e n d : ℕ} (hp : p.Prime) (he : 0 < e)
    (hkp : 15 ≤ p) (hkd : 15 ≤ d) (hd : p ^ e ∣ d)
    (heq : blockProduct 15 (n + d) = 4 * blockProduct 15 n) :
    ∃! i, i ∈ Finset.Icc 1 15 ∧ p ^ e ∣ n + i ∧
      (p ^ e) ^ 2 < 35 * d ∧ (i = 8 → (p ^ e) ^ 3 < 35 * d) := by
  have hbase := row_base_upper_k15 (ratio_window_four_nat heq).2
  exact gap_primePower_existsUnique_odd_local_bounds
    (r := 7) (C := 11) (A := 35)
    hp he (by norm_num) hkp hkd hd heq hbase (by norm_num)

end Erdos686Variant
end Erdos686
