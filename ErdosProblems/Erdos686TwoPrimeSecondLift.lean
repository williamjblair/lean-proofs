/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686TwoPrimeGap

/-!
# Second-order local lifts for the two-large-prime tail of Erdős 686

The local cofactor about the factor `n+i` has an exact expansion
`Q_i(z)=C_i+D_i*z+z^2*R_i(z)`.  Retaining the linear coefficient modulo the
third power of a localized gap component gives a new fixed divisibility.  The
signs are kept in `ℤ` throughout.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- Constant coefficient of a finite product of affine factors. -/
def finsetAffineConstant {α : Type*} (s : Finset α) (f : α → ℤ) : ℤ :=
  ∏ x ∈ s, f x

/-- Linear coefficient of a finite product of affine factors. -/
def finsetAffineLinear {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ) : ℤ :=
  ∑ x ∈ s, ∏ y ∈ s.erase x, f y

lemma finsetAffineConstant_insert {α : Type*} [DecidableEq α]
    {a : α} {s : Finset α} (f : α → ℤ) (ha : a ∉ s) :
    finsetAffineConstant (insert a s) f =
      f a * finsetAffineConstant s f := by
  simp [finsetAffineConstant, ha]

lemma finsetAffineLinear_insert {α : Type*} [DecidableEq α]
    {a : α} {s : Finset α} (f : α → ℤ) (ha : a ∉ s) :
    finsetAffineLinear (insert a s) f =
      finsetAffineConstant s f + f a * finsetAffineLinear s f := by
  simp only [finsetAffineLinear, finsetAffineConstant, Finset.sum_insert, ha,
    not_false_eq_true, Finset.erase_insert, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.erase_insert_of_ne]
  · simp [ha]
  · intro hax
    subst x
    exact ha hx

/-- Exact second-order remainder formula for a finite product. -/
theorem sq_dvd_finset_affine_prod_sub_constant_sub_linear
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℤ) (z : ℤ) :
    z ^ 2 ∣
      (∏ x ∈ s, (z + f x)) - finsetAffineConstant s f -
        finsetAffineLinear s f * z := by
  induction s using Finset.induction_on with
  | empty =>
      simp [finsetAffineConstant, finsetAffineLinear]
  | @insert a s ha ih =>
      rcases ih with ⟨R, hR⟩
      refine ⟨(z + f a) * R + finsetAffineLinear s f, ?_⟩
      rw [finsetAffineConstant_insert f ha, finsetAffineLinear_insert f ha]
      simp only [Finset.prod_insert, ha, not_false_eq_true]
      calc
        (z + f a) * (∏ x ∈ s, (z + f x)) -
            f a * finsetAffineConstant s f -
            (finsetAffineConstant s f + f a * finsetAffineLinear s f) * z =
            (z + f a) *
                ((∏ x ∈ s, (z + f x)) - finsetAffineConstant s f -
                  finsetAffineLinear s f * z) +
              finsetAffineLinear s f * z ^ 2 := by ring
        _ = (z + f a) * (z ^ 2 * R) +
              finsetAffineLinear s f * z ^ 2 := by rw [hR]
        _ = z ^ 2 * ((z + f a) * R + finsetAffineLinear s f) := by ring

/-- The local cofactor in coordinates centered at its omitted factor. -/
def localOffsetCofactor (k i : ℕ) (z : ℤ) : ℤ :=
  ∏ j ∈ (Finset.Icc 1 k).erase i, (z + (j : ℤ) - (i : ℤ))

/-- Signed constant coefficient `C_i`. -/
def localSecondConstant (k i : ℕ) : ℤ :=
  finsetAffineConstant ((Finset.Icc 1 k).erase i)
    (fun j => (j : ℤ) - (i : ℤ))

/-- Signed linear coefficient `D_i`. -/
def localSecondLinear (k i : ℕ) : ℤ :=
  finsetAffineLinear ((Finset.Icc 1 k).erase i)
    (fun j => (j : ℤ) - (i : ℤ))

lemma localSecondConstant_eq_localBlockCoefficient (k i : ℕ) :
    localSecondConstant k i = localBlockCoefficient k i := by
  unfold localSecondConstant finsetAffineConstant localBlockCoefficient
    localBlockCofactor
  apply Finset.prod_congr rfl
  intro j hj
  ring

lemma localOffsetCofactor_eq_localBlockCofactor
    {k i n : ℕ} :
    localOffsetCofactor k i ((n + i : ℕ) : ℤ) =
      localBlockCofactor k i (n : ℤ) := by
  unfold localOffsetCofactor localBlockCofactor
  apply Finset.prod_congr rfl
  intro j hj
  push_cast
  ring

theorem localOffsetCofactor_second_order (k i : ℕ) (z : ℤ) :
    z ^ 2 ∣ localOffsetCofactor k i z - localSecondConstant k i -
      localSecondLinear k i * z := by
  simpa [localOffsetCofactor, localSecondConstant, localSecondLinear,
    finsetAffineConstant, finsetAffineLinear, sub_eq_add_neg, add_assoc] using
    sq_dvd_finset_affine_prod_sub_constant_sub_linear
      ((Finset.Icc 1 k).erase i) (fun j => (j : ℤ) - (i : ℤ)) z

/-- Pure integer algebra behind the second local lift. -/
theorem second_order_local_algebra
    {H L M A C D QL QU X : ℤ}
    (hH : H ≠ 0)
    (hL : L = H * X)
    (hres : 3 * L - H * M = A * H ^ 2)
    (heq : (L + H * M) * QU = 4 * L * QL)
    (hQL : H ^ 2 ∣ QL - C - D * L)
    (hQU : H ^ 2 ∣ QU - C - D * (L + H * M)) :
    H ∣ 3 * C * A - 4 * D * M ^ 2 := by
  let EL : ℤ := QL - C - D * L
  let EU : ℤ := QU - C - D * (L + H * M)
  let T : ℤ := -C * A + D * ((X + M) ^ 2 - 4 * X ^ 2)
  have hLdiv : H ∣ L := by
    exact ⟨X, hL⟩
  have hUdiv : H ∣ L + H * M := by
    exact dvd_add hLdiv (dvd_mul_right H M)
  have hEL : H ^ 2 ∣ EL := by simpa [EL] using hQL
  have hEU : H ^ 2 ∣ EU := by simpa [EU] using hQU
  have hLEL : H ^ 3 ∣ L * EL := by
    have hmul := mul_dvd_mul hLdiv hEL
    convert hmul using 1
    ring
  have hUEU : H ^ 3 ∣ (L + H * M) * EU := by
    have hmul := mul_dvd_mul hUdiv hEU
    convert hmul using 1
    ring
  have hbase : H ^ 3 ∣
      (L + H * M) * (C + D * (L + H * M)) -
        4 * L * (C + D * L) := by
    have hid :
        (L + H * M) * (C + D * (L + H * M)) -
            4 * L * (C + D * L) =
          4 * (L * EL) - (L + H * M) * EU := by
      calc
        (L + H * M) * (C + D * (L + H * M)) -
            4 * L * (C + D * L) =
            ((L + H * M) * QU - 4 * L * QL) +
              (4 * (L * (QL - C - D * L)) -
                (L + H * M) * (QU - C - D * (L + H * M))) := by ring
        _ = 4 * (L * EL) - (L + H * M) * EU := by
          rw [heq]
          simp [EL, EU]
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_right hLEL 4) hUEU
  have hbaseT : H ^ 3 ∣ H ^ 2 * T := by
    have hEq :
        (L + H * M) * (C + D * (L + H * M)) -
            4 * L * (C + D * L) = H ^ 2 * T := by
      dsimp [T]
      rw [hL]
      have hres' : 3 * (H * X) - H * M = A * H ^ 2 := by
        simpa [hL] using hres
      calc
        (H * X + H * M) * (C + D * (H * X + H * M)) -
            4 * (H * X) * (C + D * (H * X)) =
            -C * (3 * (H * X) - H * M) +
              H ^ 2 * D * ((X + M) ^ 2 - 4 * X ^ 2) := by ring
        _ = -C * (A * H ^ 2) +
              H ^ 2 * D * ((X + M) ^ 2 - 4 * X ^ 2) := by rw [hres']
        _ = H ^ 2 *
              (-C * A + D * ((X + M) ^ 2 - 4 * X ^ 2)) := by ring
    rw [← hEq]
    exact hbase
  have hT : H ∣ T := by
    rcases hbaseT with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    calc
      H ^ 2 * T = H ^ 3 * q := hq
      _ = H ^ 2 * (H * q) := by ring
  have hrEq : 3 * X - M = A * H := by
    apply mul_left_cancel₀ hH
    calc
      H * (3 * X - M) = 3 * L - H * M := by rw [hL]; ring
      _ = A * H ^ 2 := hres
      _ = H * (A * H) := by ring
  have hr : H ∣ 3 * X - M := ⟨A, by simpa [mul_comm] using hrEq⟩
  have hrSq : H ∣ (3 * X - M) ^ 2 := by
    simpa [pow_two] using dvd_mul_of_dvd_left hr (3 * X - M)
  have hdiv : H ∣ (-3 * T - D * (3 * X - M) ^ 2) :=
    dvd_sub (dvd_mul_of_dvd_right hT (-3))
      (dvd_mul_of_dvd_right hrSq D)
  convert hdiv using 1
  dsimp [T]
  ring

/-- Second-order local lift for an exact natural gap quotient `d=h*m`.

The residual identity is stated in `ℤ`, so no truncated natural subtraction is
hidden in the interface. -/
theorem second_order_local_lift
    {k n d i h m a : ℕ}
    (hi : i ∈ Finset.Icc 1 k)
    (hh : 0 < h)
    (hd : d = h * m)
    (hfactor : h ∣ n + i)
    (hres : 3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
      (a : ℤ) * (h : ℤ) ^ 2)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (h : ℤ) ∣
      3 * localSecondConstant k i * (a : ℤ) -
        4 * localSecondLinear k i * (m : ℤ) ^ 2 := by
  rcases hfactor with ⟨x, hx⟩
  let H : ℤ := (h : ℤ)
  let L : ℤ := ((n + i : ℕ) : ℤ)
  let M : ℤ := (m : ℤ)
  let A : ℤ := (a : ℤ)
  let C : ℤ := localSecondConstant k i
  let D : ℤ := localSecondLinear k i
  let X : ℤ := (x : ℤ)
  let QL : ℤ := localBlockCofactor k i (n : ℤ)
  let QU : ℤ := localBlockCofactor k i ((n + d : ℕ) : ℤ)
  have hH : H ≠ 0 := by
    dsimp [H]
    exact_mod_cast (Nat.ne_of_gt hh)
  have hL : L = H * X := by
    dsimp [L, H, X]
    exact_mod_cast hx
  have hdCast : (d : ℤ) = H * M := by
    dsimp [H, M]
    exact_mod_cast hd
  have hres' : 3 * L - H * M = A * H ^ 2 := by
    simpa [L, H, M, A, hdCast] using hres
  have heqInt :
      intBlockProduct k ((n + d : ℕ) : ℤ) =
        4 * intBlockProduct k (n : ℤ) := by
    rw [intBlockProduct_natCast, intBlockProduct_natCast]
    exact_mod_cast heq
  have heqLocal : (L + H * M) * QU = 4 * L * QL := by
    rw [intBlockProduct_eq_factor_mul_localBlockCofactor
        ((n + d : ℕ) : ℤ) hi,
      intBlockProduct_eq_factor_mul_localBlockCofactor (n : ℤ) hi] at heqInt
    dsimp [L, H, M, QL, QU]
    push_cast at heqInt ⊢
    rw [hd] at heqInt ⊢
    push_cast at heqInt ⊢
    convert heqInt using 1 <;> ring
  have hHL : H ∣ L := ⟨X, hL⟩
  have hHU : H ∣ L + H * M := dvd_add hHL (dvd_mul_right H M)
  have hHsqLsq : H ^ 2 ∣ L ^ 2 := by
    simpa [pow_two] using mul_dvd_mul hHL hHL
  have hHsqUsq : H ^ 2 ∣ (L + H * M) ^ 2 := by
    simpa [pow_two] using mul_dvd_mul hHU hHU
  have hQLexp : L ^ 2 ∣ QL - C - D * L := by
    have h := localOffsetCofactor_second_order k i L
    have hrel : localOffsetCofactor k i L = QL := by
      dsimp [L, QL]
      exact localOffsetCofactor_eq_localBlockCofactor
    simpa [hrel, C, D] using h
  have hQUexp : (L + H * M) ^ 2 ∣
      QU - C - D * (L + H * M) := by
    have h := localOffsetCofactor_second_order k i (L + H * M)
    have hU : L + H * M = ((n + d + i : ℕ) : ℤ) := by
      dsimp [L, H, M]
      rw [hd]
      push_cast
      ring
    have hrel : localOffsetCofactor k i (L + H * M) = QU := by
      rw [hU]
      dsimp [QU]
      have hlocal :=
        (localOffsetCofactor_eq_localBlockCofactor (k := k) (i := i)
          (n := n + d))
      exact hlocal
    simpa [hrel, C, D] using h
  have hQL' : H ^ 2 ∣ QL - C - D * L := dvd_trans hHsqLsq hQLexp
  have hQU' : H ^ 2 ∣ QU - C - D * (L + H * M) :=
    dvd_trans hHsqUsq hQUexp
  simpa [H, M, A, C, D] using
    second_order_local_algebra hH hL hres' heqLocal hQL' hQU'

/-- The two second lifts and the signed Pell equation produce fixed
coefficient obstruction divisibilities. -/
theorem second_obstruction_divisibilities
    {P Q a b Cᵢ Dᵢ Cⱼ Dⱼ delta : ℤ}
    (hP : P ∣ 3 * Cᵢ * a - 4 * Dᵢ * Q ^ 2)
    (hQ : Q ∣ 3 * Cⱼ * b - 4 * Dⱼ * P ^ 2)
    (hPell : a * P ^ 2 - b * Q ^ 2 = 3 * delta) :
    P ∣ 3 * (Cᵢ * a * b + 4 * Dᵢ * delta) ∧
      Q ∣ 3 * (Cⱼ * a * b - 4 * Dⱼ * delta) := by
  constructor
  · have hmul : P ∣ b * (3 * Cᵢ * a - 4 * Dᵢ * Q ^ 2) :=
      dvd_mul_of_dvd_right hP b
    have hpow : P ∣ 4 * Dᵢ * a * P ^ 2 := by
      exact dvd_mul_of_dvd_right (dvd_pow_self P (by norm_num)) (4 * Dᵢ * a)
    have hadd := dvd_add hmul hpow
    have hid :
        b * (3 * Cᵢ * a - 4 * Dᵢ * Q ^ 2) + 4 * Dᵢ * a * P ^ 2 =
          3 * (Cᵢ * a * b + 4 * Dᵢ * delta) := by
      calc
        b * (3 * Cᵢ * a - 4 * Dᵢ * Q ^ 2) + 4 * Dᵢ * a * P ^ 2 =
            3 * Cᵢ * a * b + 4 * Dᵢ * (a * P ^ 2 - b * Q ^ 2) := by ring
        _ = 3 * Cᵢ * a * b + 4 * Dᵢ * (3 * delta) := by rw [hPell]
        _ = 3 * (Cᵢ * a * b + 4 * Dᵢ * delta) := by ring
    rw [hid] at hadd
    exact hadd
  · have hmul : Q ∣ a * (3 * Cⱼ * b - 4 * Dⱼ * P ^ 2) :=
      dvd_mul_of_dvd_right hQ a
    have hpow : Q ∣ 4 * Dⱼ * b * Q ^ 2 := by
      exact dvd_mul_of_dvd_right (dvd_pow_self Q (by norm_num)) (4 * Dⱼ * b)
    have hadd := dvd_add hmul hpow
    have hid :
        a * (3 * Cⱼ * b - 4 * Dⱼ * P ^ 2) + 4 * Dⱼ * b * Q ^ 2 =
          3 * (Cⱼ * a * b - 4 * Dⱼ * delta) := by
      calc
        a * (3 * Cⱼ * b - 4 * Dⱼ * P ^ 2) + 4 * Dⱼ * b * Q ^ 2 =
            3 * Cⱼ * a * b - 4 * Dⱼ * (a * P ^ 2 - b * Q ^ 2) := by ring
        _ = 3 * Cⱼ * a * b - 4 * Dⱼ * (3 * delta) := by rw [hPell]
        _ = 3 * (Cⱼ * a * b - 4 * Dⱼ * delta) := by ring
    rw [hid] at hadd
    exact hadd

/-- Fixed left obstruction integer, including the harmless factor `3`. -/
def secondObstructionLeft (k i j t : ℕ) : ℤ :=
  3 * (localSecondConstant k i * (t : ℤ) +
    4 * localSecondLinear k i * ((i : ℤ) - (j : ℤ)))

/-- Fixed right obstruction integer, including the harmless factor `3`. -/
def secondObstructionRight (k i j t : ℕ) : ℤ :=
  3 * (localSecondConstant k j * (t : ℤ) -
    4 * localSecondLinear k j * ((i : ℤ) - (j : ℤ)))

/-- A deliberately loose exact bound that remains far below `10^120` after
the Pell ratio estimate is applied. -/
def secondObstructionBound : ℕ := 10 ^ 20

/-- If the two Pell components divide a bounded non-simultaneously-zero
obstruction pair, the ratio inequalities bound their product. -/
theorem component_product_lt_cutoff_of_second_obstructions
    {P Q a b A : ℕ} {L R : ℤ}
    (hPpos : 0 < P)
    (hQpos : 0 < Q)
    (hapos : 0 < a)
    (hbpos : 0 < b)
    (hA35 : A ≤ 35)
    (haRatio : a * P < A * Q)
    (hbRatio : b * Q < A * P)
    (hPdiv : (P : ℤ) ∣ L)
    (hQdiv : (Q : ℤ) ∣ R)
    (hLbound : Int.natAbs L < secondObstructionBound)
    (hRbound : Int.natAbs R < secondObstructionBound)
    (hnonzero : L ≠ 0 ∨ R ≠ 0) :
    P * Q < 10 ^ 120 := by
  have hBpos : 0 < secondObstructionBound := by
    norm_num [secondObstructionBound]
  have hApos : 0 < A := by
    have hAQpos : 0 < A * Q :=
      lt_trans (Nat.mul_pos hapos hPpos) haRatio
    exact pos_of_mul_pos_left hAQpos (Nat.zero_le Q)
  have hABound : A * secondObstructionBound ^ 2 < 10 ^ 120 := by
    calc
      A * secondObstructionBound ^ 2 ≤
          35 * secondObstructionBound ^ 2 :=
        Nat.mul_le_mul_right _ hA35
      _ < 10 ^ 120 := by norm_num [secondObstructionBound]
  rcases hnonzero with hLne | hRne
  · have hPleAbs : P ≤ Int.natAbs L := by
      simpa using Int.natAbs_le_of_dvd_ne_zero hPdiv hLne
    have hPB : P < secondObstructionBound := lt_of_le_of_lt hPleAbs hLbound
    have hQbQ : Q ≤ b * Q := by nlinarith
    have hQAP : Q < A * P := lt_of_le_of_lt hQbQ hbRatio
    have hQAB : Q < A * secondObstructionBound := by
      exact lt_trans hQAP (Nat.mul_lt_mul_of_pos_left hPB hApos)
    have hprod : P * Q < A * secondObstructionBound ^ 2 := by
      calc
        P * Q < secondObstructionBound * Q :=
          Nat.mul_lt_mul_of_pos_right hPB hQpos
        _ < secondObstructionBound * (A * secondObstructionBound) :=
          Nat.mul_lt_mul_of_pos_left hQAB hBpos
        _ = A * secondObstructionBound ^ 2 := by ring
    exact lt_trans hprod hABound
  · have hQleAbs : Q ≤ Int.natAbs R := by
      simpa using Int.natAbs_le_of_dvd_ne_zero hQdiv hRne
    have hQB : Q < secondObstructionBound := lt_of_le_of_lt hQleAbs hRbound
    have hPaP : P ≤ a * P := by nlinarith
    have hPAQ : P < A * Q := lt_of_le_of_lt hPaP haRatio
    have hPAB : P < A * secondObstructionBound := by
      exact lt_trans hPAQ (Nat.mul_lt_mul_of_pos_left hQB hApos)
    have hprod : P * Q < A * secondObstructionBound ^ 2 := by
      calc
        P * Q < (A * secondObstructionBound) * Q :=
          Nat.mul_lt_mul_of_pos_right hPAB hQpos
        _ < (A * secondObstructionBound) * secondObstructionBound :=
          Nat.mul_lt_mul_of_pos_left hQB (Nat.mul_pos hApos hBpos)
        _ = A * secondObstructionBound ^ 2 := by ring
    exact lt_trans hprod hABound

/-- Kernel-reduced signed coefficient table for the six admissible odd rows. -/
def secondCoefficientTable : ℕ → ℕ → ℤ × ℤ
  | 5, 1 => (24, 50)
  | 5, 2 => (-6, -5)
  | 5, 3 => (4, 0)
  | 5, 4 => (-6, 5)
  | 5, 5 => (24, -50)
  | 7, 1 => (720, 1764)
  | 7, 2 => (-120, -154)
  | 7, 3 => (48, 28)
  | 7, 4 => (-36, 0)
  | 7, 5 => (48, -28)
  | 7, 6 => (-120, 154)
  | 7, 7 => (720, -1764)
  | 9, 1 => (40320, 109584)
  | 9, 2 => (-5040, -8028)
  | 9, 3 => (1440, 1368)
  | 9, 4 => (-720, -324)
  | 9, 5 => (576, 0)
  | 9, 6 => (-720, 324)
  | 9, 7 => (1440, -1368)
  | 9, 8 => (-5040, 8028)
  | 9, 9 => (40320, -109584)
  | 11, 1 => (3628800, 10628640)
  | 11, 2 => (-362880, -663696)
  | 11, 3 => (80640, 98208)
  | 11, 4 => (-30240, -22968)
  | 11, 5 => (17280, 6336)
  | 11, 6 => (-14400, 0)
  | 11, 7 => (17280, -6336)
  | 11, 8 => (-30240, 22968)
  | 11, 9 => (80640, -98208)
  | 11, 10 => (-362880, 663696)
  | 11, 11 => (3628800, -10628640)
  | 13, 1 => (479001600, 1486442880)
  | 13, 2 => (-39916800, -80627040)
  | 13, 3 => (7257600, 10370880)
  | 13, 4 => (-2177280, -2167776)
  | 13, 5 => (967680, 614016)
  | 13, 6 => (-604800, -187200)
  | 13, 7 => (518400, 0)
  | 13, 8 => (-604800, 187200)
  | 13, 9 => (967680, -614016)
  | 13, 10 => (-2177280, 2167776)
  | 13, 11 => (7257600, -10370880)
  | 13, 12 => (-39916800, 80627040)
  | 13, 13 => (479001600, -1486442880)
  | 15, 1 => (87178291200, 283465647360)
  | 15, 2 => (-6227020800, -13575738240)
  | 15, 3 => (958003200, 1535880960)
  | 15, 4 => (-239500800, -284178240)
  | 15, 5 => (87091200, 73647360)
  | 15, 6 => (-43545600, -23760000)
  | 15, 7 => (29030400, 7776000)
  | 15, 8 => (-25401600, 0)
  | 15, 9 => (29030400, -7776000)
  | 15, 10 => (-43545600, 23760000)
  | 15, 11 => (87091200, -73647360)
  | 15, 12 => (-239500800, 284178240)
  | 15, 13 => (958003200, -1535880960)
  | 15, 14 => (-6227020800, 13575738240)
  | 15, 15 => (87178291200, -283465647360)
  | _, _ => (0, 0)

/-- The explicit coefficient table agrees with the finite-product definitions.
The proof is ordinary kernel reduction (`decide`), not `native_decide`. -/
theorem localSecondCoefficients_eq_table
    {k i : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k) :
    (localSecondConstant k i, localSecondLinear k i) =
      secondCoefficientTable k i := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [Finset.mem_Icc] at hi <;>
    rcases hi with ⟨hi1, hik⟩ <;>
    interval_cases i <;> decide

lemma localSecondConstant_eq_table
    {k i : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k) :
    localSecondConstant k i = (secondCoefficientTable k i).1 := by
  have h := congrArg Prod.fst (localSecondCoefficients_eq_table hk hi)
  simpa using h

lemma localSecondLinear_eq_table
    {k i : ℕ}
    (hk : k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15)
    (hi : i ∈ Finset.Icc 1 k) :
    localSecondLinear k i = (secondCoefficientTable k i).2 := by
  have h := congrArg Prod.snd (localSecondCoefficients_eq_table hk hi)
  simpa using h

/-- Exact finite certificate for the `k=5`, `A=14` row. -/
theorem second_obstruction_certificate_5
    {i j t : ℕ}
    (hi : i ∈ Finset.Icc 1 5)
    (hj : j ∈ Finset.Icc 1 5)
    (hij : i ≠ j)
    (hic : i ≠ 3)
    (hjc : j ≠ 3)
    (ht : 0 < t)
    (htA : t < 14 ^ 2) :
    Int.natAbs (secondObstructionLeft 5 i j t) < secondObstructionBound ∧
      Int.natAbs (secondObstructionRight 5 i j t) < secondObstructionBound ∧
      (secondObstructionLeft 5 i j t ≠ 0 ∨
        secondObstructionRight 5 i j t ≠ 0) := by
  unfold secondObstructionLeft secondObstructionRight
  rw [localSecondConstant_eq_table (by omega) hi,
    localSecondLinear_eq_table (by omega) hi,
    localSecondConstant_eq_table (by omega) hj,
    localSecondLinear_eq_table (by omega) hj]
  rw [Finset.mem_Icc] at hi hj
  rcases hi with ⟨hi1, hi5⟩
  rcases hj with ⟨hj1, hj5⟩
  interval_cases i <;> interval_cases j <;>
    norm_num [secondCoefficientTable, secondObstructionBound] at * <;> omega


/-- Exact finite certificate for the `k=7`, `A≤17` row. -/
theorem second_obstruction_certificate_7
    {i j t : ℕ}
    (hi : i ∈ Finset.Icc 1 7)
    (hj : j ∈ Finset.Icc 1 7)
    (hij : i ≠ j)
    (hic : i ≠ 4)
    (hjc : j ≠ 4)
    (ht : 0 < t)
    (htA : t < 17 ^ 2) :
    Int.natAbs (secondObstructionLeft 7 i j t) < secondObstructionBound ∧
      Int.natAbs (secondObstructionRight 7 i j t) < secondObstructionBound ∧
      (secondObstructionLeft 7 i j t ≠ 0 ∨
        secondObstructionRight 7 i j t ≠ 0) := by
  unfold secondObstructionLeft secondObstructionRight
  rw [localSecondConstant_eq_table (by omega) hi,
    localSecondLinear_eq_table (by omega) hi,
    localSecondConstant_eq_table (by omega) hj,
    localSecondLinear_eq_table (by omega) hj]
  rw [Finset.mem_Icc] at hi hj
  rcases hi with ⟨hi1, hik⟩
  rcases hj with ⟨hj1, hjk⟩
  interval_cases i <;> interval_cases j <;>
    norm_num [secondCoefficientTable, secondObstructionBound] at * <;> omega

/-- Exact finite certificate for the `k=9`, `A≤23` row. -/
theorem second_obstruction_certificate_9
    {i j t : ℕ}
    (hi : i ∈ Finset.Icc 1 9)
    (hj : j ∈ Finset.Icc 1 9)
    (hij : i ≠ j)
    (hic : i ≠ 5)
    (hjc : j ≠ 5)
    (ht : 0 < t)
    (htA : t < 23 ^ 2) :
    Int.natAbs (secondObstructionLeft 9 i j t) < secondObstructionBound ∧
      Int.natAbs (secondObstructionRight 9 i j t) < secondObstructionBound ∧
      (secondObstructionLeft 9 i j t ≠ 0 ∨
        secondObstructionRight 9 i j t ≠ 0) := by
  unfold secondObstructionLeft secondObstructionRight
  rw [localSecondConstant_eq_table (by omega) hi,
    localSecondLinear_eq_table (by omega) hi,
    localSecondConstant_eq_table (by omega) hj,
    localSecondLinear_eq_table (by omega) hj]
  rw [Finset.mem_Icc] at hi hj
  rcases hi with ⟨hi1, hik⟩
  rcases hj with ⟨hj1, hjk⟩
  interval_cases i <;> interval_cases j <;>
    norm_num [secondCoefficientTable, secondObstructionBound] at * <;> omega

set_option maxHeartbeats 1000000 in
-- The explicit `11^2` index split exceeds the default elaboration budget.
/-- Exact finite certificate for the `k=11`, `A≤26` row. -/
theorem second_obstruction_certificate_11
    {i j t : ℕ}
    (hi : i ∈ Finset.Icc 1 11)
    (hj : j ∈ Finset.Icc 1 11)
    (hij : i ≠ j)
    (hic : i ≠ 6)
    (hjc : j ≠ 6)
    (ht : 0 < t)
    (htA : t < 26 ^ 2) :
    Int.natAbs (secondObstructionLeft 11 i j t) < secondObstructionBound ∧
      Int.natAbs (secondObstructionRight 11 i j t) < secondObstructionBound ∧
      (secondObstructionLeft 11 i j t ≠ 0 ∨
        secondObstructionRight 11 i j t ≠ 0) := by
  unfold secondObstructionLeft secondObstructionRight
  rw [localSecondConstant_eq_table (by omega) hi,
    localSecondLinear_eq_table (by omega) hi,
    localSecondConstant_eq_table (by omega) hj,
    localSecondLinear_eq_table (by omega) hj]
  rw [Finset.mem_Icc] at hi hj
  rcases hi with ⟨hi1, hik⟩
  rcases hj with ⟨hj1, hjk⟩
  interval_cases i <;> interval_cases j <;>
    norm_num [secondCoefficientTable, secondObstructionBound] at * <;> omega

set_option maxHeartbeats 1400000 in
-- The explicit `13^2` index split exceeds the default elaboration budget.
/-- Exact finite certificate for the `k=13`, `A≤29` row. -/
theorem second_obstruction_certificate_13
    {i j t : ℕ}
    (hi : i ∈ Finset.Icc 1 13)
    (hj : j ∈ Finset.Icc 1 13)
    (hij : i ≠ j)
    (hic : i ≠ 7)
    (hjc : j ≠ 7)
    (ht : 0 < t)
    (htA : t < 29 ^ 2) :
    Int.natAbs (secondObstructionLeft 13 i j t) < secondObstructionBound ∧
      Int.natAbs (secondObstructionRight 13 i j t) < secondObstructionBound ∧
      (secondObstructionLeft 13 i j t ≠ 0 ∨
        secondObstructionRight 13 i j t ≠ 0) := by
  unfold secondObstructionLeft secondObstructionRight
  rw [localSecondConstant_eq_table (by omega) hi,
    localSecondLinear_eq_table (by omega) hi,
    localSecondConstant_eq_table (by omega) hj,
    localSecondLinear_eq_table (by omega) hj]
  rw [Finset.mem_Icc] at hi hj
  rcases hi with ⟨hi1, hik⟩
  rcases hj with ⟨hj1, hjk⟩
  interval_cases i <;> interval_cases j <;>
    norm_num [secondCoefficientTable, secondObstructionBound] at * <;> omega

set_option maxHeartbeats 2000000 in
-- The explicit `15^2` index split exceeds the default elaboration budget.
/-- Exact finite certificate for the `k=15`, `A≤35` row. -/
theorem second_obstruction_certificate_15
    {i j t : ℕ}
    (hi : i ∈ Finset.Icc 1 15)
    (hj : j ∈ Finset.Icc 1 15)
    (hij : i ≠ j)
    (hic : i ≠ 8)
    (hjc : j ≠ 8)
    (ht : 0 < t)
    (htA : t < 35 ^ 2) :
    Int.natAbs (secondObstructionLeft 15 i j t) < secondObstructionBound ∧
      Int.natAbs (secondObstructionRight 15 i j t) < secondObstructionBound ∧
      (secondObstructionLeft 15 i j t ≠ 0 ∨
        secondObstructionRight 15 i j t ≠ 0) := by
  unfold secondObstructionLeft secondObstructionRight
  rw [localSecondConstant_eq_table (by omega) hi,
    localSecondLinear_eq_table (by omega) hi,
    localSecondConstant_eq_table (by omega) hj,
    localSecondLinear_eq_table (by omega) hj]
  rw [Finset.mem_Icc] at hi hj
  rcases hi with ⟨hi1, hik⟩
  rcases hj with ⟨hj1, hjk⟩
  interval_cases i <;> interval_cases j <;>
    norm_num [secondCoefficientTable, secondObstructionBound] at * <;> omega

/-- Complete closure of the exact two-large-prime tail in the six admissible
odd rows.  The only size input is the row-specific confinement bound on
`A = 3*C+2`; all local lifts, Pell identities, obstruction bounds, and the
final `10^120` contradiction are proved here. -/
theorem two_large_prime_support_below_cutoff_of_second_lift
    {p q e f r n d C A : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hpq : p ≠ q)
    (he : 0 < e)
    (hf : 0 < f)
    (hr2 : 2 ≤ r)
    (hpk : 2 * r + 1 ≤ p)
    (hqk : 2 * r + 1 ≤ q)
    (hgap : d = p ^ e * q ^ f)
    (heq : blockProduct (2 * r + 1) (n + d) =
      4 * blockProduct (2 * r + 1) n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hrow :
      (r = 2 ∧ A ≤ 14) ∨
      (r = 3 ∧ A ≤ 17) ∨
      (r = 4 ∧ A ≤ 23) ∨
      (r = 5 ∧ A ≤ 26) ∨
      (r = 6 ∧ A ≤ 29) ∨
      (r = 7 ∧ A ≤ 35)) :
    d < 10 ^ 120 := by
  have hpPowPos : 0 < p ^ e := pow_pos hp.pos _
  have hqPowPos : 0 < q ^ f := pow_pos hq.pos _
  have hdpos : 0 < d := by
    rw [hgap]
    exact Nat.mul_pos hpPowPos hqPowPos
  have hpLePow : p ≤ p ^ e := by
    simpa using Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ e)
  have hkd : 2 * r + 1 ≤ d := by
    calc
      2 * r + 1 ≤ p := hpk
      _ ≤ p ^ e := hpLePow
      _ ≤ p ^ e * q ^ f := Nat.le_mul_of_pos_right _ hqPowPos
      _ = d := hgap.symm
  have hA35 : A ≤ 35 := by
    rcases hrow with ⟨rfl, hAr⟩ | ⟨rfl, hAr⟩ | ⟨rfl, hAr⟩ |
      ⟨rfl, hAr⟩ | ⟨rfl, hAr⟩ | ⟨rfl, hAr⟩ <;> omega
  have hAk : A < (2 * r + 1) ^ 2 := by
    rcases hrow with ⟨rfl, hAr⟩ | ⟨rfl, hAr⟩ | ⟨rfl, hAr⟩ |
      ⟨rfl, hAr⟩ | ⟨rfl, hAr⟩ | ⟨rfl, hAr⟩ <;> norm_num at hAr ⊢ <;> omega
  by_contra hnot
  have hlarge : 10 ^ 120 ≤ d := Nat.le_of_not_gt hnot
  obtain ⟨i, j, a, b, hi, hj, hij, hapos, hbpos, haeq, hbeq,
      haRatio, hbRatio, hab, hPell, hpCenter, hqCenter⟩ :=
    two_large_prime_support_bounded_pell hp hq hpq he hf hr2 hpk hqk
      hkd hgap heq hbase hA hAk
  have hA5Small : A ^ 5 < 10 ^ 120 := by
    calc
      A ^ 5 ≤ 35 ^ 5 := Nat.pow_le_pow_left hA35 5
      _ < 10 ^ 120 := by norm_num
  have hic : i ≠ r + 1 := by
    intro hic'
    have hdsmall := (hpCenter hic').2
    omega
  have hjc : j ≠ r + 1 := by
    intro hjc'
    have hdsmall := (hqCenter hjc').2
    omega
  have hpDvdD : p ^ e ∣ d := by
    rw [hgap]
    exact dvd_mul_right _ _
  have hqDvdD : q ^ f ∣ d := by
    rw [hgap]
    exact dvd_mul_left _ _
  have hXiPos : 0 < localResidual n d i := by
    rw [haeq]
    positivity
  have hXjPos : 0 < localResidual n d j := by
    rw [hbeq]
    positivity
  have hpDvdXi : p ^ e ∣ localResidual n d i := by
    rw [haeq]
    refine ⟨a * p ^ e, ?_⟩
    ring
  have hqDvdXj : q ^ f ∣ localResidual n d j := by
    rw [hbeq]
    refine ⟨b * q ^ f, ?_⟩
    ring
  have hXiAdd : localResidual n d i + d = 3 * (n + i) := by
    unfold localResidual at hXiPos ⊢
    omega
  have hXjAdd : localResidual n d j + d = 3 * (n + j) := by
    unfold localResidual at hXjPos ⊢
    omega
  have hpDvdThree : p ^ e ∣ 3 * (n + i) := by
    rw [← hXiAdd]
    exact dvd_add hpDvdXi hpDvdD
  have hqDvdThree : q ^ f ∣ 3 * (n + j) := by
    rw [← hXjAdd]
    exact dvd_add hqDvdXj hqDvdD
  have hpNotDvdThree : ¬p ∣ 3 := by
    intro hp3
    have hpLe3 : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp3
    omega
  have hqNotDvdThree : ¬q ∣ 3 := by
    intro hq3
    have hqLe3 : q ≤ 3 := Nat.le_of_dvd (by norm_num) hq3
    omega
  have hpFactor : p ^ e ∣ n + i :=
    (hp.coprime_pow_of_not_dvd (m := e) hpNotDvdThree).symm.dvd_of_dvd_mul_left
      hpDvdThree
  have hqFactor : q ^ f ∣ n + j :=
    (hq.coprime_pow_of_not_dvd (m := f) hqNotDvdThree).symm.dvd_of_dvd_mul_left
      hqDvdThree
  have hdi : d ≤ 3 * (n + i) := by
    unfold localResidual at hXiPos
    omega
  have hdj : d ≤ 3 * (n + j) := by
    unfold localResidual at hXjPos
    omega
  have hresI : 3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
      (a : ℤ) * (p ^ e : ℕ) ^ 2 := by
    calc
      3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
          ((3 * (n + i) - d : ℕ) : ℤ) := by
            rw [Int.ofNat_sub hdi]
            push_cast
            ring
      _ = (localResidual n d i : ℤ) := by rfl
      _ = (a * (p ^ e) ^ 2 : ℕ) := by rw [haeq]
      _ = (a : ℤ) * (p ^ e : ℕ) ^ 2 := by push_cast; ring
  have hresJ : 3 * ((n + j : ℕ) : ℤ) - (d : ℤ) =
      (b : ℤ) * (q ^ f : ℕ) ^ 2 := by
    calc
      3 * ((n + j : ℕ) : ℤ) - (d : ℤ) =
          ((3 * (n + j) - d : ℕ) : ℤ) := by
            rw [Int.ofNat_sub hdj]
            push_cast
            ring
      _ = (localResidual n d j : ℤ) := by rfl
      _ = (b * (q ^ f) ^ 2 : ℕ) := by rw [hbeq]
      _ = (b : ℤ) * (q ^ f : ℕ) ^ 2 := by push_cast; ring
  have hpLocal := second_order_local_lift hi hpPowPos hgap hpFactor hresI heq
  have hqLocal := second_order_local_lift hj hqPowPos
    (by simpa [mul_comm] using hgap) hqFactor hresJ heq
  have hPell' :
      (a : ℤ) * (p ^ e : ℕ) ^ 2 - (b : ℤ) * (q ^ f : ℕ) ^ 2 =
        3 * ((i : ℤ) - (j : ℤ)) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using hPell
  have hobs := second_obstruction_divisibilities hpLocal hqLocal hPell'
  have hpObs : (p ^ e : ℤ) ∣
      secondObstructionLeft (2 * r + 1) i j (a * b) := by
    simpa [secondObstructionLeft, mul_assoc] using hobs.1
  have hqObs : (q ^ f : ℤ) ∣
      secondObstructionRight (2 * r + 1) i j (a * b) := by
    simpa [secondObstructionRight, mul_assoc] using hobs.2
  have htpos : 0 < a * b := Nat.mul_pos hapos hbpos
  have hcert :
      Int.natAbs (secondObstructionLeft (2 * r + 1) i j (a * b)) <
          secondObstructionBound ∧
        Int.natAbs (secondObstructionRight (2 * r + 1) i j (a * b)) <
          secondObstructionBound ∧
        (secondObstructionLeft (2 * r + 1) i j (a * b) ≠ 0 ∨
          secondObstructionRight (2 * r + 1) i j (a * b) ≠ 0) := by
    rcases hrow with h2 | h3 | h4 | h5 | h6 | h7
    · rcases h2 with ⟨rfl, hAr⟩
      have ht : a * b < 14 ^ 2 :=
        lt_of_lt_of_le hab (Nat.pow_le_pow_left hAr 2)
      simpa using second_obstruction_certificate_5
        (by simpa using hi) (by simpa using hj) hij
        (by simpa using hic) (by simpa using hjc) htpos ht
    · rcases h3 with ⟨rfl, hAr⟩
      have ht : a * b < 17 ^ 2 :=
        lt_of_lt_of_le hab (Nat.pow_le_pow_left hAr 2)
      simpa using second_obstruction_certificate_7
        (by simpa using hi) (by simpa using hj) hij
        (by simpa using hic) (by simpa using hjc) htpos ht
    · rcases h4 with ⟨rfl, hAr⟩
      have ht : a * b < 23 ^ 2 :=
        lt_of_lt_of_le hab (Nat.pow_le_pow_left hAr 2)
      simpa using second_obstruction_certificate_9
        (by simpa using hi) (by simpa using hj) hij
        (by simpa using hic) (by simpa using hjc) htpos ht
    · rcases h5 with ⟨rfl, hAr⟩
      have ht : a * b < 26 ^ 2 :=
        lt_of_lt_of_le hab (Nat.pow_le_pow_left hAr 2)
      simpa using second_obstruction_certificate_11
        (by simpa using hi) (by simpa using hj) hij
        (by simpa using hic) (by simpa using hjc) htpos ht
    · rcases h6 with ⟨rfl, hAr⟩
      have ht : a * b < 29 ^ 2 :=
        lt_of_lt_of_le hab (Nat.pow_le_pow_left hAr 2)
      simpa using second_obstruction_certificate_13
        (by simpa using hi) (by simpa using hj) hij
        (by simpa using hic) (by simpa using hjc) htpos ht
    · rcases h7 with ⟨rfl, hAr⟩
      have ht : a * b < 35 ^ 2 :=
        lt_of_lt_of_le hab (Nat.pow_le_pow_left hAr 2)
      simpa using second_obstruction_certificate_15
        (by simpa using hi) (by simpa using hj) hij
        (by simpa using hic) (by simpa using hjc) htpos ht
  have hprod := component_product_lt_cutoff_of_second_obstructions
    hpPowPos hqPowPos hapos hbpos hA35 haRatio hbRatio hpObs hqObs
      hcert.1 hcert.2.1 hcert.2.2
  apply hnot
  simpa [hgap] using hprod


/-- Row `k=5` wrapper for the clean two-large-prime closure. -/
theorem two_large_prime_support_k5_below_cutoff
    {p q e f n d C A : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hpq : p ≠ q)
    (he : 0 < e)
    (hf : 0 < f)
    (hpk : 5 ≤ p)
    (hqk : 5 ≤ q)
    (hgap : d = p ^ e * q ^ f)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hArow : A ≤ 14) :
    d < 10 ^ 120 := by
  simpa using two_large_prime_support_below_cutoff_of_second_lift
    (r := 2) hp hq hpq he hf (by norm_num) hpk hqk hgap heq hbase hA
      (Or.inl ⟨rfl, hArow⟩)

/-- Row `k=7` wrapper for the clean two-large-prime closure. -/
theorem two_large_prime_support_k7_below_cutoff
    {p q e f n d C A : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hpq : p ≠ q)
    (he : 0 < e)
    (hf : 0 < f)
    (hpk : 7 ≤ p)
    (hqk : 7 ≤ q)
    (hgap : d = p ^ e * q ^ f)
    (heq : blockProduct 7 (n + d) = 4 * blockProduct 7 n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hArow : A ≤ 17) :
    d < 10 ^ 120 := by
  simpa using two_large_prime_support_below_cutoff_of_second_lift
    (r := 3) hp hq hpq he hf (by norm_num) hpk hqk hgap heq hbase hA
      (Or.inr (Or.inl ⟨rfl, hArow⟩))

/-- Row `k=9` wrapper for the clean two-large-prime closure. -/
theorem two_large_prime_support_k9_below_cutoff
    {p q e f n d C A : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hpq : p ≠ q)
    (he : 0 < e)
    (hf : 0 < f)
    (hpk : 9 ≤ p)
    (hqk : 9 ≤ q)
    (hgap : d = p ^ e * q ^ f)
    (heq : blockProduct 9 (n + d) = 4 * blockProduct 9 n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hArow : A ≤ 23) :
    d < 10 ^ 120 := by
  simpa using two_large_prime_support_below_cutoff_of_second_lift
    (r := 4) hp hq hpq he hf (by norm_num) hpk hqk hgap heq hbase hA
      (Or.inr (Or.inr (Or.inl ⟨rfl, hArow⟩)))

/-- Row `k=11` wrapper for the clean two-large-prime closure. -/
theorem two_large_prime_support_k11_below_cutoff
    {p q e f n d C A : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hpq : p ≠ q)
    (he : 0 < e)
    (hf : 0 < f)
    (hpk : 11 ≤ p)
    (hqk : 11 ≤ q)
    (hgap : d = p ^ e * q ^ f)
    (heq : blockProduct 11 (n + d) = 4 * blockProduct 11 n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hArow : A ≤ 26) :
    d < 10 ^ 120 := by
  simpa using two_large_prime_support_below_cutoff_of_second_lift
    (r := 5) hp hq hpq he hf (by norm_num) hpk hqk hgap heq hbase hA
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hArow⟩))))

/-- Row `k=13` wrapper for the clean two-large-prime closure. -/
theorem two_large_prime_support_k13_below_cutoff
    {p q e f n d C A : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hpq : p ≠ q)
    (he : 0 < e)
    (hf : 0 < f)
    (hpk : 13 ≤ p)
    (hqk : 13 ≤ q)
    (hgap : d = p ^ e * q ^ f)
    (heq : blockProduct 13 (n + d) = 4 * blockProduct 13 n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hArow : A ≤ 29) :
    d < 10 ^ 120 := by
  simpa using two_large_prime_support_below_cutoff_of_second_lift
    (r := 6) hp hq hpq he hf (by norm_num) hpk hqk hgap heq hbase hA
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hArow⟩)))))

/-- Row `k=15` wrapper for the clean two-large-prime closure. -/
theorem two_large_prime_support_k15_below_cutoff
    {p q e f n d C A : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hpq : p ≠ q)
    (he : 0 < e)
    (hf : 0 < f)
    (hpk : 15 ≤ p)
    (hqk : 15 ≤ q)
    (hgap : d = p ^ e * q ^ f)
    (heq : blockProduct 15 (n + d) = 4 * blockProduct 15 n)
    (hbase : n + 1 < C * d)
    (hA : A = 3 * C + 2)
    (hArow : A ≤ 35) :
    d < 10 ^ 120 := by
  simpa using two_large_prime_support_below_cutoff_of_second_lift
    (r := 7) hp hq hpq he hf (by norm_num) hpk hqk hgap heq hbase hA
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hArow⟩)))))

end Erdos686Variant
end Erdos686
