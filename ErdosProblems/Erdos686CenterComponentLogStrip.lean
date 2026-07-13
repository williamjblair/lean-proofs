/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ReflectedAlignmentSquareLift
import ErdosProblems.Erdos686MatchingCompression
import ErdosProblems.Erdos686CenteredRatioWindowSharp
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Factorization

/-!
# Erdős 686: reflected-center and logarithmic-strip restrictions

This module audits the genuinely new parts of a proposed uniform even-row
argument.  It deliberately reuses the already banked reflected square lift
and one-factorial matching compression rather than restating them.
-/

namespace Erdos686
namespace Erdos686Variant

/-! ## Even centered products -/

/-- The paired quadratic form of a centered even block. -/
def evenCenteredQuadraticProduct (r : ℕ) (T : ℤ) : ℤ :=
  ∏ j ∈ Finset.range r, (T ^ 2 - (2 * (j : ℤ) + 1) ^ 2)

lemma centeredBlockProduct_two_mul_eq_evenCenteredQuadraticProduct
    (r : ℕ) (T : ℤ) :
    centeredBlockProduct (2 * r) T = evenCenteredQuadraticProduct r T := by
  let lo : Finset ℕ := Finset.Icc 1 r
  let hi : Finset ℕ := Finset.Icc (r + 1) (2 * r)
  have hsplit : Finset.Icc 1 (2 * r) = lo ∪ hi := by
    ext i
    simp only [lo, hi, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint lo hi := by
    rw [Finset.disjoint_left]
    intro i hlo hhi
    simp only [lo, Finset.mem_Icc] at hlo
    simp only [hi, Finset.mem_Icc] at hhi
    omega
  have hloProd :
      (∏ i ∈ lo, (T + (2 * (i : ℤ) - (2 * r : ℤ) - 1))) =
        ∏ j ∈ Finset.range r, (T - (2 * (j : ℤ) + 1)) := by
    refine Finset.prod_bij (fun i _ => r - i) ?_ ?_ ?_ ?_
    · intro i hiMem
      simp only [lo, Finset.mem_Icc] at hiMem
      simp only [Finset.mem_range]
      omega
    · intro i₁ hi₁ i₂ hi₂ he
      simp only [lo, Finset.mem_Icc] at hi₁ hi₂
      change r - i₁ = r - i₂ at he
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      refine ⟨r - j, ?_, ?_⟩
      · simp only [lo, Finset.mem_Icc]
        omega
      · change r - (r - j) = j
        omega
    · intro i hiMem
      simp only [lo, Finset.mem_Icc] at hiMem
      change T + (2 * (i : ℤ) - 2 * (r : ℤ) - 1) =
        T - (2 * ((r - i : ℕ) : ℤ) + 1)
      rw [Nat.cast_sub hiMem.2]
      ring
  have hhiProd :
      (∏ i ∈ hi, (T + (2 * (i : ℤ) - (2 * r : ℤ) - 1))) =
        ∏ j ∈ Finset.range r, (T + (2 * (j : ℤ) + 1)) := by
    refine Finset.prod_bij (fun i _ => i - (r + 1)) ?_ ?_ ?_ ?_
    · intro i hiMem
      simp only [hi, Finset.mem_Icc] at hiMem
      simp only [Finset.mem_range]
      omega
    · intro i₁ hi₁ i₂ hi₂ he
      simp only [hi, Finset.mem_Icc] at hi₁ hi₂
      change i₁ - (r + 1) = i₂ - (r + 1) at he
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      refine ⟨r + 1 + j, ?_, ?_⟩
      · simp only [hi, Finset.mem_Icc]
        omega
      · change (r + 1 + j) - (r + 1) = j
        omega
    · intro i hiMem
      simp only [hi, Finset.mem_Icc] at hiMem
      change T + (2 * (i : ℤ) - 2 * (r : ℤ) - 1) =
        T + (2 * ((i - (r + 1) : ℕ) : ℤ) + 1)
      rw [Nat.cast_sub hiMem.1]
      push_cast
      ring
  unfold centeredBlockProduct
  rw [hsplit, Finset.prod_union hdisj]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [hloProd, hhiProd]
  unfold evenCenteredQuadraticProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  ring

lemma oddLinearProduct_eq_doubleFactorial (r : ℕ) :
    (∏ j ∈ Finset.range r, (2 * j + 1)) = (2 * r - 1).doubleFactorial := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.prod_range_succ, ih]
      cases r with
      | zero => norm_num
      | succ s =>
          rw [show 2 * (s + 1 + 1) - 1 = (2 * s + 1) + 2 by omega,
            Nat.doubleFactorial_add_two]
          rw [show 2 * (s + 1) - 1 = 2 * s + 1 by omega]
          ring

lemma evenCenteredQuadraticProduct_zero (r : ℕ) :
    evenCenteredQuadraticProduct r 0 =
      (-1 : ℤ) ^ r * (((2 * r - 1).doubleFactorial : ℕ) : ℤ) ^ 2 := by
  unfold evenCenteredQuadraticProduct
  calc
    (∏ j ∈ Finset.range r,
        ((0 : ℤ) ^ 2 - (2 * (j : ℤ) + 1) ^ 2)) =
        ∏ j ∈ Finset.range r,
          ((-1 : ℤ) * ((2 * j + 1 : ℕ) : ℤ) ^ 2) := by
      apply Finset.prod_congr rfl
      intro j hj
      push_cast
      ring
    _ = (∏ _j ∈ Finset.range r, (-1 : ℤ)) *
        ∏ j ∈ Finset.range r, (((2 * j + 1 : ℕ) : ℤ) ^ 2) := by
      rw [← Finset.prod_mul_distrib]
    _ = (-1 : ℤ) ^ r *
        (∏ j ∈ Finset.range r, (((2 * j + 1 : ℕ) : ℤ))) ^ 2 := by
      rw [Finset.prod_const, Finset.card_range, Finset.prod_pow]
    _ = (-1 : ℤ) ^ r * (((2 * r - 1).doubleFactorial : ℕ) : ℤ) ^ 2 := by
      rw [← Nat.cast_prod, oddLinearProduct_eq_doubleFactorial]

/-- An even centered block differs from its constant term by a multiple of
the square of every divisor of its centered argument. -/
lemma evenCenteredQuadraticProduct_mod_sq
    {g : ℕ} {r : ℕ} {T : ℤ} (hg : (g : ℤ) ∣ T) :
    (g : ℤ) ^ 2 ∣
      evenCenteredQuadraticProduct r T - evenCenteredQuadraticProduct r 0 := by
  have hgSq : (g : ℤ) ^ 2 ∣ T ^ 2 := by
    simpa [pow_two] using mul_dvd_mul hg hg
  have hmod : evenCenteredQuadraticProduct r T ≡
      evenCenteredQuadraticProduct r 0 [ZMOD (g : ℤ) ^ 2] := by
    unfold evenCenteredQuadraticProduct
    apply Int.ModEq.prod
    intro j hj
    rw [Int.modEq_iff_dvd]
    convert dvd_neg.mpr hgSq using 1
    ring
  have hneg := dvd_neg.mpr hmod.dvd
  convert hneg using 1
  ring

/-- The exact centered equation for an even block. -/
lemma evenCenteredQuadraticProduct_eq_four
    {r n d : ℕ}
    (heq : blockProduct (2 * r) (n + d) = 4 * blockProduct (2 * r) n) :
    evenCenteredQuadraticProduct r
        (2 * ((n + d : ℕ) : ℤ) + ((2 * r : ℕ) : ℤ) + 1) =
      4 * evenCenteredQuadraticProduct r
        (2 * (n : ℤ) + ((2 * r : ℕ) : ℤ) + 1) := by
  have heqInt :
      (blockProduct (2 * r) (n + d) : ℤ) =
        4 * (blockProduct (2 * r) n : ℤ) := by
    exact_mod_cast heq
  rw [← centeredBlockProduct_two_mul_eq_evenCenteredQuadraticProduct,
    ← centeredBlockProduct_two_mul_eq_evenCenteredQuadraticProduct,
    centeredBlockProduct_center, centeredBlockProduct_center]
  rw [heqInt]
  ring

private lemma dvd_doubleFactorial_of_sq_dvd_three_sq
    {g O : ℕ} (hO : O ≠ 0) (hg : g ^ 2 ∣ 3 * O ^ 2) : g ∣ O := by
  have hgne : g ≠ 0 := by
    intro h
    subst g
    simpa [hO] using hg
  have hg0 : g ^ 2 ≠ 0 := pow_ne_zero 2 hgne
  have hO0 : 3 * O ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hO)
  apply (Nat.factorization_le_iff_dvd hgne hO).mp
  intro p
  by_cases hp : p.Prime
  · have hfac := ((Nat.factorization_le_iff_dvd hg0 hO0).mpr hg) p
    rw [Nat.factorization_pow,
      Nat.factorization_mul (by norm_num) (pow_ne_zero 2 hO),
      Nat.factorization_pow] at hfac
    change 2 * g.factorization p ≤
      (3 : ℕ).factorization p + 2 * O.factorization p at hfac
    have hthree : (3 : ℕ).factorization p ≤ 1 := by
      by_cases hpeq : p = 3
      · subst p
        norm_num [Nat.Prime.factorization_self Nat.prime_three]
      · have hnot : ¬ p ∣ 3 := by
          simpa [Nat.prime_dvd_prime_iff_eq hp Nat.prime_three] using hpeq
        simp [Nat.factorization_eq_zero_of_not_dvd hnot]
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-! ## The centered gcd restriction -/

/-- Every target-range solution in an even row has centered gcd supported
inside the odd double factorial. -/
theorem gcd_gap_reflectionCenter_dvd_oddDoubleFactorial
    {r n d : ℕ} (hr : 1 ≤ r)
    (heq : blockProduct (2 * r) (n + d) = 4 * blockProduct (2 * r) n) :
    Nat.gcd d (2 * n + d + 2 * r + 1) ∣ (2 * r - 1).doubleFactorial := by
  let g : ℕ := Nat.gcd d (2 * n + d + 2 * r + 1)
  let v : ℕ := 2 * n + 2 * r + 1
  let w : ℕ := v + 2 * d
  let O : ℕ := (2 * r - 1).doubleFactorial
  have hgd : g ∣ d := by
    exact Nat.gcd_dvd_left d (2 * n + d + 2 * r + 1)
  have hgH : g ∣ 2 * n + d + 2 * r + 1 := by
    exact Nat.gcd_dvd_right d (2 * n + d + 2 * r + 1)
  have hdleH : d ≤ 2 * n + d + 2 * r + 1 := by omega
  have hgv : g ∣ v := by
    have hsub := Nat.dvd_sub hgH hgd
    convert hsub using 1
    dsimp [v]
    omega
  have hgw : g ∣ w := by
    dsimp [w]
    exact dvd_add hgv (dvd_mul_of_dvd_right hgd 2)
  have hgvInt : (g : ℤ) ∣ (v : ℤ) := by exact_mod_cast hgv
  have hgwInt : (g : ℤ) ∣ (w : ℤ) := by exact_mod_cast hgw
  have hvmod := evenCenteredQuadraticProduct_mod_sq (r := r) hgvInt
  have hwmod := evenCenteredQuadraticProduct_mod_sq (r := r) hgwInt
  have hcenter := evenCenteredQuadraticProduct_eq_four (r := r) heq
  have hvArg :
      2 * (n : ℤ) + ((2 * r : ℕ) : ℤ) + 1 = (v : ℤ) := by
    dsimp [v]
  have hwArg :
      2 * (((n + d : ℕ) : ℤ)) + ((2 * r : ℕ) : ℤ) + 1 = (w : ℤ) := by
    dsimp [w, v]
    ring
  rw [hvArg, hwArg] at hcenter
  let C : ℤ := evenCenteredQuadraticProduct r 0
  have hcomb : (g : ℤ) ^ 2 ∣ 3 * C := by
    have hraw := dvd_sub hwmod (dvd_mul_of_dvd_right hvmod 4)
    convert hraw using 1
    dsimp [C]
    rw [hcenter]
    ring
  have hC : C = (-1 : ℤ) ^ r * (O : ℤ) ^ 2 := by
    dsimp [C, O]
    exact evenCenteredQuadraticProduct_zero r
  rw [hC] at hcomb
  have hnatInt : (g : ℤ) ^ 2 ∣ (3 * O ^ 2 : ℕ) := by
    rcases neg_one_pow_eq_or ℤ r with hs | hs
    · simpa [hs] using hcomb
    · have hneg := dvd_neg.mpr hcomb
      simpa [hs] using hneg
  have hnat : g ^ 2 ∣ 3 * O ^ 2 := by exact_mod_cast hnatInt
  simpa [g, O] using dvd_doubleFactorial_of_sq_dvd_three_sq
    (Nat.ne_of_gt (Nat.doubleFactorial_pos _)) hnat

/-- In an even exact solution, a prime at least the row length cannot divide
both the gap and the reflection center.  Thus large gap support and large
reflection-center support are disjoint, including the boundary `p=k`. -/
theorem prime_ge_row_dvd_gap_not_dvd_reflectionCenter
    {r n d p : ℕ} (hr : 1 ≤ r) (hp : p.Prime) (hkp : 2 * r ≤ p)
    (hpd : p ∣ d)
    (heq : blockProduct (2 * r) (n + d) = 4 * blockProduct (2 * r) n) :
    ¬ p ∣ 2 * n + d + 2 * r + 1 := by
  intro hpH
  have hpg : p ∣ Nat.gcd d (2 * n + d + 2 * r + 1) :=
    Nat.dvd_gcd hpd hpH
  have hgO := gcd_gap_reflectionCenter_dvd_oddDoubleFactorial hr heq
  have hpO : p ∣ (2 * r - 1).doubleFactorial := dvd_trans hpg hgO
  have hOfac : (2 * r - 1).doubleFactorial ∣ (2 * r - 1).factorial := by
    rw [show 2 * r - 1 = (2 * r - 2) + 1 by omega,
      Nat.factorial_eq_mul_doubleFactorial]
    exact dvd_mul_right _ _
  have hpfac : p ∣ (2 * r - 1).factorial := dvd_trans hpO hOfac
  have hple : p ≤ 2 * r - 1 := (hp.dvd_factorial).mp hpfac
  omega

/-! ## An elementary initial-lcm bound -/

/-- `lcm(1,...,N)`, indexed without a zero factor. -/
def initialLcm (N : ℕ) : ℕ :=
  (Finset.range N).lcm (fun j => j + 1)

lemma initialLcm_ne_zero (N : ℕ) : initialLcm N ≠ 0 := by
  intro hzero
  unfold initialLcm at hzero
  rw [Finset.lcm_eq_zero_iff] at hzero
  rcases hzero with ⟨j, hj, hz⟩
  omega

lemma term_dvd_initialLcm {x N : ℕ} (hx : 1 ≤ x) (hxN : x ≤ N) :
    x ∣ initialLcm N := by
  unfold initialLcm
  have hj : x - 1 ∈ Finset.range N := by
    simp only [Finset.mem_range]
    omega
  have hdvd := Finset.dvd_lcm (f := fun j : ℕ => j + 1) hj
  rw [show x = (x - 1) + 1 by omega]
  exact hdvd

private lemma prime_dvd_half_binomial
    {N m p e : ℕ} (hp : p.Prime) (hm : m ≤ N) (he : 1 ≤ e)
    (hmq : m < p ^ e) (hrq : N - m < p ^ e) (hqN : p ^ e ≤ N) :
    p ∣ N.choose m := by
  have hN0 : N ≠ 0 := by
    have hqpos : 0 < p ^ e := pow_pos hp.pos _
    omega
  have heLog : e ≤ Nat.log p N :=
    Nat.le_log_of_pow_le hp.one_lt hqN
  have hlog : Nat.log p N < Nat.log p N + 1 := by omega
  have hfac := Nat.factorization_choose hp hm hlog
  have hmem : e ∈ Finset.Ico 1 (Nat.log p N + 1) := by
    simp only [Finset.mem_Ico]
    omega
  have hcarry : p ^ e ≤ m % p ^ e + (N - m) % p ^ e := by
    rw [Nat.mod_eq_of_lt hmq, Nat.mod_eq_of_lt hrq]
    omega
  have hcardPos : 0 <
      ({i ∈ Finset.Ico 1 (Nat.log p N + 1) |
        p ^ i ≤ m % p ^ i + (N - m) % p ^ i} : Finset ℕ).card := by
    rw [Finset.card_pos]
    exact ⟨e, Finset.mem_filter.mpr ⟨hmem, hcarry⟩⟩
  have hfacPos : 0 < (N.choose m).factorization p := by
    rw [hfac]
    exact hcardPos
  exact (hp.dvd_iff_one_le_factorization (Nat.choose_ne_zero hm)).mpr hfacPos

lemma initialLcm_dvd_half_binomial_bound
    {N : ℕ} (hN : 2 ≤ N) :
    initialLcm N ∣
      initialLcm (N / 2) * ((N + 1) * N.choose (N / 2)) := by
  let m : ℕ := N / 2
  let R : ℕ := (N + 1) * N.choose m
  have hmN : m ≤ N := by
    dsimp [m]
    exact Nat.div_le_self N 2
  have hmpos : 1 ≤ m := by
    dsimp [m]
    omega
  have hchoose0 : N.choose m ≠ 0 := Nat.choose_ne_zero hmN
  have hR0 : R ≠ 0 := by
    exact mul_ne_zero (by omega) hchoose0
  have hL0 : initialLcm m ≠ 0 := initialLcm_ne_zero m
  have hrhs0 : initialLcm m * R ≠ 0 := mul_ne_zero hL0 hR0
  have hdecomp : N % 2 + 2 * m = N := by
    simpa [m] using Nat.mod_add_div N 2
  have hmodlt : N % 2 < 2 := Nat.mod_lt N (by norm_num)
  have hhalfLo : m ≤ N - m := by omega
  have hhalfHi : N - m ≤ m + 1 := by omega
  unfold initialLcm
  apply Finset.lcm_dvd
  intro j hj
  simp only [Finset.mem_range] at hj
  let x : ℕ := j + 1
  have hx0 : x ≠ 0 := by dsimp [x]; omega
  have hxN : x ≤ N := by dsimp [x]; omega
  apply (Nat.factorization_le_iff_dvd hx0 hrhs0).mp
  intro p
  by_cases hp : p.Prime
  · let e : ℕ := x.factorization p
    have hpowX : p ^ e ∣ x := by
      exact (hp.pow_dvd_iff_le_factorization hx0).mpr le_rfl
    have hpowPos : 0 < p ^ e := pow_pos hp.pos _
    have hpowLeX : p ^ e ≤ x := Nat.le_of_dvd (by omega) hpowX
    have hpowLeN : p ^ e ≤ N := le_trans hpowLeX hxN
    by_cases hsmall : p ^ e ≤ m
    · have hpowL : p ^ e ∣ initialLcm m :=
        term_dvd_initialLcm (by omega) hsmall
      have hpowRhs : p ^ e ∣ initialLcm m * R := dvd_mul_of_dvd_left hpowL R
      exact (hp.pow_dvd_iff_le_factorization hrhs0).mp hpowRhs
    · have hepos : 1 ≤ e := by
        by_contra he0
        have : e = 0 := by omega
        apply hsmall
        simpa [this] using hmpos
      let ep : ℕ := e - 1
      have hep : ep + 1 = e := by dsimp [ep]; omega
      have hpowEq : p ^ e = p ^ ep * p := by
        rw [← hep, pow_succ]
      have hprevLe : p ^ ep ≤ m := by
        have hp2 : 2 ≤ p := hp.two_le
        have htwo : 2 * p ^ ep ≤ p ^ e := by
          rw [hpowEq]
          simpa [mul_comm] using Nat.mul_le_mul_left (p ^ ep) hp2
        by_contra hnot
        have hm1 : m + 1 ≤ p ^ ep := by omega
        omega
      have hprevDvd : p ^ ep ∣ initialLcm m :=
        term_dvd_initialLcm (pow_pos hp.pos _) hprevLe
      have hpExtra : p ∣ R := by
        have hpPow : p ∣ p ^ e := by
          simpa using pow_dvd_pow p hepos
        by_cases hqR : p ^ e ≤ N - m
        · have hqEq : p ^ e = m + 1 := by omega
          have hrEq : N - m = m + 1 := by omega
          have hN1 : N + 1 = 2 * (p ^ e) := by omega
          dsimp [R]
          apply dvd_mul_of_dvd_left
          rw [hN1]
          exact dvd_mul_of_dvd_right hpPow 2
        · have hpChoose : p ∣ N.choose m :=
            prime_dvd_half_binomial hp hmN hepos (by omega) (by omega) hpowLeN
          dsimp [R]
          exact dvd_mul_of_dvd_right hpChoose (N + 1)
      have hpowRhs : p ^ e ∣ initialLcm m * R := by
        rw [hpowEq]
        exact mul_dvd_mul hprevDvd hpExtra
      exact (hp.pow_dvd_iff_le_factorization hrhs0).mp hpowRhs
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Sharp half-interval recurrence.  If `m` is the larger half of
`{1,...,N}`, no exceptional `(N+1)` factor is needed. -/
lemma initialLcm_dvd_base_mul_choose
    {N m : ℕ} (hmpos : 1 ≤ m) (hmN : m ≤ N)
    (hother : N - m ≤ m) (hdouble : N ≤ 2 * m) :
    initialLcm N ∣ initialLcm m * N.choose m := by
  have hchoose0 : N.choose m ≠ 0 := Nat.choose_ne_zero hmN
  have hL0 : initialLcm m ≠ 0 := initialLcm_ne_zero m
  have hrhs0 : initialLcm m * N.choose m ≠ 0 :=
    mul_ne_zero hL0 hchoose0
  unfold initialLcm
  apply Finset.lcm_dvd
  intro j hj
  simp only [Finset.mem_range] at hj
  let x : ℕ := j + 1
  have hx0 : x ≠ 0 := by dsimp [x]; omega
  have hxN : x ≤ N := by dsimp [x]; omega
  apply (Nat.factorization_le_iff_dvd hx0 hrhs0).mp
  intro p
  by_cases hp : p.Prime
  · let e : ℕ := x.factorization p
    have hpowX : p ^ e ∣ x :=
      (hp.pow_dvd_iff_le_factorization hx0).mpr le_rfl
    have hpowLeX : p ^ e ≤ x := Nat.le_of_dvd (by omega) hpowX
    have hpowLeN : p ^ e ≤ N := le_trans hpowLeX hxN
    by_cases hsmall : p ^ e ≤ m
    · have hpowL : p ^ e ∣ initialLcm m :=
        term_dvd_initialLcm (pow_pos hp.pos _) hsmall
      exact (hp.pow_dvd_iff_le_factorization hrhs0).mp
        (dvd_mul_of_dvd_left hpowL (N.choose m))
    · have hepos : 1 ≤ e := by
        by_contra he0
        have heq0 : e = 0 := by omega
        apply hsmall
        simpa [heq0] using hmpos
      let ep : ℕ := e - 1
      have hep : ep + 1 = e := by dsimp [ep]; omega
      have hpowEq : p ^ e = p ^ ep * p := by rw [← hep, pow_succ]
      have hprevLe : p ^ ep ≤ m := by
        have htwo : 2 * p ^ ep ≤ p ^ e := by
          rw [hpowEq]
          simpa [mul_comm] using Nat.mul_le_mul_left (p ^ ep) hp.two_le
        by_contra hnot
        have hm1 : m + 1 ≤ p ^ ep := by omega
        omega
      have hprevDvd : p ^ ep ∣ initialLcm m :=
        term_dvd_initialLcm (pow_pos hp.pos _) hprevLe
      have hpChoose : p ∣ N.choose m :=
        prime_dvd_half_binomial hp hmN hepos (by omega)
          (lt_of_le_of_lt hother (by omega)) hpowLeN
      have hpowRhs : p ^ e ∣ initialLcm m * N.choose m := by
        rw [hpowEq]
        exact mul_dvd_mul hprevDvd hpChoose
      exact (hp.pow_dvd_iff_le_factorization hrhs0).mp hpowRhs
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma twice_succ_le_two_pow {m : ℕ} (hm : 3 ≤ m) :
    2 * m + 2 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      calc
        2 * (m + 1) + 2 ≤ 2 * (2 * m + 2) := by omega
        _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

/-- Elementary exponential bound for the initial lcm.  The proof uses the
exact half-binomial recurrence above, `choose N (N/2) ≤ 2^N`, and no
prime enumeration. -/
theorem initialLcm_le_eight_pow (N : ℕ) : initialLcm N ≤ 8 ^ N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      by_cases hsmall : N < 6
      · interval_cases N <;> decide
      · have hN : 6 ≤ N := by omega
        let m : ℕ := N / 2
        have hmLt : m < N := by
          dsimp [m]
          exact Nat.div_lt_self (by omega) (by norm_num)
        have hm3 : 3 ≤ m := by
          dsimp [m]
          omega
        have hih : initialLcm m ≤ 8 ^ m := ih m hmLt
        have hmN : m ≤ N := le_of_lt hmLt
        have hchoose : N.choose m ≤ 2 ^ N := Nat.choose_le_two_pow N m
        have hrecDvd := initialLcm_dvd_half_binomial_bound (N := N) (by omega)
        have hrecPos :
            0 < initialLcm m * ((N + 1) * N.choose m) := by
          exact mul_pos (Nat.pos_of_ne_zero (initialLcm_ne_zero m))
            (mul_pos (by omega) (Nat.choose_pos hmN))
        have hrec : initialLcm N ≤
            initialLcm m * ((N + 1) * N.choose m) :=
          Nat.le_of_dvd hrecPos hrecDvd
        have hdecomp : N % 2 + 2 * m = N := by
          simpa [m] using Nat.mod_add_div N 2
        have hmodlt : N % 2 < 2 := Nat.mod_lt N (by norm_num)
        have hNsucc : N + 1 ≤ 2 ^ m := by
          exact le_trans (by omega) (twice_succ_le_two_pow hm3)
        have htwoM : 2 * m ≤ N := by
          have := Nat.div_mul_le_self N 2
          simpa [m, mul_comm] using this
        calc
          initialLcm N
              ≤ initialLcm m * ((N + 1) * N.choose m) := hrec
          _ ≤ 8 ^ m * ((N + 1) * 2 ^ N) := by
            exact Nat.mul_le_mul hih (Nat.mul_le_mul_left (N + 1) hchoose)
          _ ≤ 8 ^ m * (2 ^ m * 2 ^ N) := by
            exact Nat.mul_le_mul_left (8 ^ m)
              (Nat.mul_le_mul_right (2 ^ N) hNsucc)
          _ = 2 ^ (4 * m + N) := by
            rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul,
              ← pow_add, ← pow_add]
            congr 1
            omega
          _ ≤ 2 ^ (3 * N) := by
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 8 ^ N := by
            rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]

/-- Sharp elementary binomial bound for the initial lcm. -/
theorem initialLcm_le_four_pow (N : ℕ) : initialLcm N ≤ 4 ^ N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      by_cases hsmall : N < 2
      · interval_cases N <;> decide
      · have hN : 2 ≤ N := by omega
        rcases Nat.even_or_odd N with hEven | hOdd
        · obtain ⟨u, hu⟩ := hEven
          have hform : N = 2 * u := by omega
          have huPos : 1 ≤ u := by omega
          have huLt : u < N := by omega
          have hrecDvd : initialLcm N ∣ initialLcm u * N.choose u := by
            apply initialLcm_dvd_base_mul_choose huPos (by omega)
            · omega
            · omega
          have hrec : initialLcm N ≤ initialLcm u * N.choose u :=
            Nat.le_of_dvd
              (mul_pos (Nat.pos_of_ne_zero (initialLcm_ne_zero u))
                (Nat.choose_pos (by omega))) hrecDvd
          have hchoose : N.choose u ≤ 4 ^ u := by
            have hraw := Nat.choose_le_two_pow N u
            rw [hform] at hraw
            rw [hform]
            calc
              (2 * u).choose u ≤ 2 ^ (2 * u) := hraw
              _ = 4 ^ u := by
                rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          calc
            initialLcm N ≤ initialLcm u * N.choose u := hrec
            _ ≤ 4 ^ u * 4 ^ u := Nat.mul_le_mul (ih u huLt) hchoose
            _ = 4 ^ N := by rw [← pow_add]; congr 1 <;> omega
        · obtain ⟨u, hu⟩ := hOdd
          have hform : N = 2 * u + 1 := by omega
          have huPos : 1 ≤ u := by omega
          let m : ℕ := u + 1
          have hmPos : 1 ≤ m := by dsimp [m]; omega
          have hmLt : m < N := by dsimp [m]; omega
          have hmN : m ≤ N := le_of_lt hmLt
          have hrecDvd : initialLcm N ∣ initialLcm m * N.choose m := by
            apply initialLcm_dvd_base_mul_choose hmPos hmN
            · dsimp [m]
              omega
            · dsimp [m]
              omega
          have hrec : initialLcm N ≤ initialLcm m * N.choose m :=
            Nat.le_of_dvd
              (mul_pos (Nat.pos_of_ne_zero (initialLcm_ne_zero m))
                (Nat.choose_pos hmN)) hrecDvd
          have hchoose : N.choose m ≤ 4 ^ u := by
            have hraw := Nat.choose_succ_le_two_pow (2 * u) m
            rw [hform]
            calc
              (2 * u + 1).choose m ≤ 2 ^ (2 * u) := by simpa using hraw
              _ = 4 ^ u := by
                rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          calc
            initialLcm N ≤ initialLcm m * N.choose m := hrec
            _ ≤ 4 ^ m * 4 ^ u := Nat.mul_le_mul (ih m hmLt) hchoose
            _ = 4 ^ N := by
              rw [← pow_add]
              congr 1
              dsimp [m]
              omega

/-! ## Consecutive-interval lcm compression -/

/-- The lcm of the `m` consecutive positive integers beginning at `a`. -/
def intervalLcm (a m : ℕ) : ℕ :=
  (Finset.range m).lcm (fun t => a + t)

lemma intervalLcm_ne_zero {a m : ℕ} (ha : 1 ≤ a) :
    intervalLcm a m ≠ 0 := by
  intro hzero
  unfold intervalLcm at hzero
  rw [Finset.lcm_eq_zero_iff] at hzero
  rcases hzero with ⟨t, ht, hterm⟩
  omega

/-- Every term of a positive interval divides its binomial quotient times
`lcm(1,...,m)`.  The proof is Kummer's carry formula: every prime power in
the term above `m` forces a carry in `choose (a+m-1) m`. -/
lemma interval_term_dvd_choose_mul_initialLcm
    {a m t : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) (ht : t < m) :
    a + t ∣ (a + m - 1).choose m * initialLcm m := by
  have hx0 : a + t ≠ 0 := by omega
  have hN : m ≤ a + m - 1 := by omega
  have hchoose0 : (a + m - 1).choose m ≠ 0 := Nat.choose_ne_zero hN
  have hrhs0 : (a + m - 1).choose m * initialLcm m ≠ 0 :=
    mul_ne_zero hchoose0 (initialLcm_ne_zero m)
  apply (Nat.factorization_le_iff_dvd hx0 hrhs0).mp
  intro p
  by_cases hp : p.Prime
  · let e : ℕ := (a + t).factorization p
    let ell : ℕ := Nat.log p m
    have hpellDvd : p ^ ell ∣ initialLcm m := by
      apply term_dvd_initialLcm (pow_pos hp.pos _)
      dsimp [ell]
      exact Nat.pow_log_le_self p (by omega)
    have hellL : ell ≤ (initialLcm m).factorization p :=
      (hp.pow_dvd_iff_le_factorization (initialLcm_ne_zero m)).mp hpellDvd
    have heBound : e ≤ ell + ((a + m - 1).choose m).factorization p := by
      by_cases heSmall : e ≤ ell
      · omega
      · let carries : Finset ℕ :=
          {j ∈ Finset.Ico 1 (Nat.log p (a + m - 1) + 1) |
            p ^ j ≤ m % p ^ j + ((a + m - 1) - m) % p ^ j}
        have hsubset : Finset.Ioc ell e ⊆ carries := by
          intro j hj
          simp only [Finset.mem_Ioc] at hj
          have hjpos : 1 ≤ j := by omega
          have hjle : j ≤ e := hj.2
          have hqDvd : p ^ j ∣ a + t :=
            (hp.pow_dvd_iff_le_factorization hx0).mpr hjle
          have hqPos : 0 < p ^ j := pow_pos hp.pos _
          have hqLeX : p ^ j ≤ a + t := Nat.le_of_dvd (by omega) hqDvd
          have hqLeN : p ^ j ≤ a + m - 1 := by omega
          have hjLog : j ≤ Nat.log p (a + m - 1) :=
            Nat.le_log_of_pow_le hp.one_lt hqLeN
          have hmLtq : m < p ^ j := by
            have hmBase : m < p ^ (ell + 1) := by
              dsimp [ell]
              simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hp.one_lt m
            exact lt_of_lt_of_le hmBase
              (Nat.pow_le_pow_right hp.one_lt.le (by omega))
          have ht1Ltq : t + 1 < p ^ j := by omega
          have hnotDvd : ¬ p ^ j ∣ t + 1 := by
            exact Nat.not_dvd_of_pos_of_lt (by omega) ht1Ltq
          have hcarrySmall :
              p ^ j ≤ (t + 1) % p ^ j + (a - 1) % p ^ j := by
            apply Nat.le_mod_add_mod_of_dvd_add_of_not_dvd
            · convert hqDvd using 1 <;> omega
            · exact hnotDvd
          have hcarry :
              p ^ j ≤ m % p ^ j + ((a + m - 1) - m) % p ^ j := by
            rw [Nat.mod_eq_of_lt ht1Ltq] at hcarrySmall
            rw [Nat.mod_eq_of_lt hmLtq]
            have hsub : (a + m - 1) - m = a - 1 := by omega
            rw [hsub]
            omega
          simp only [carries, Finset.mem_filter, Finset.mem_Ico]
          exact ⟨⟨hjpos, by omega⟩, hcarry⟩
        have hcard : e - ell ≤ carries.card := by
          simpa using Finset.card_le_card hsubset
        have hfacChoose :
            ((a + m - 1).choose m).factorization p = carries.card := by
          dsimp [carries]
          exact Nat.factorization_choose hp hN (by omega)
        rw [hfacChoose]
        omega
    rw [Nat.factorization_mul hchoose0 (initialLcm_ne_zero m),
      Finsupp.coe_add, Pi.add_apply]
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Lcm form of the interval compression. -/
lemma intervalLcm_dvd_choose_mul_initialLcm
    {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    intervalLcm a m ∣ (a + m - 1).choose m * initialLcm m := by
  unfold intervalLcm
  apply Finset.lcm_dvd
  intro t ht
  exact interval_term_dvd_choose_mul_initialLcm ha hm
    (Finset.mem_range.mp ht)

/-- Exact interval theorem: factorial times the interval lcm divides the
interval product times the initial lcm. -/
theorem factorial_mul_intervalLcm_dvd_ascFactorial_mul_initialLcm
    {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    m.factorial * intervalLcm a m ∣
      a.ascFactorial m * initialLcm m := by
  have hdvd := intervalLcm_dvd_choose_mul_initialLcm ha hm
  have hmul := mul_dvd_mul_left m.factorial hdvd
  rw [Nat.ascFactorial_eq_factorial_mul_choose']
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

lemma centeredDiffProduct_eq_ascFactorial
    {k d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d) :
    centeredDiffProduct k d =
      (d - (k - 1)).ascFactorial (2 * k - 1) := by
  have hset : Finset.Icc 0 (2 * k - 2) = Finset.range (2 * k - 1) := by
    ext h
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  unfold centeredDiffProduct
  rw [hset, Nat.ascFactorial_eq_prod_range]
  apply Finset.prod_congr rfl
  intro h hh
  omega

lemma centeredDiffLcm_eq_intervalLcm
    {k d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d) :
    centeredDiffLcm k d = intervalLcm (d - (k - 1)) (2 * k - 1) := by
  have hset : Finset.Icc 0 (2 * k - 2) = Finset.range (2 * k - 1) := by
    ext h
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  unfold centeredDiffLcm intervalLcm
  apply Finset.lcm_congr hset
  intro h hh
  omega

/-- Centered specialization of the exact interval theorem. -/
theorem factorial_mul_centeredDiffLcm_dvd_centeredDiffProduct_mul_initialLcm
    {k d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d) :
    (2 * k - 1).factorial * centeredDiffLcm k d ∣
      centeredDiffProduct k d * initialLcm (2 * k - 1) := by
  rw [centeredDiffLcm_eq_intervalLcm hk hd,
    centeredDiffProduct_eq_ascFactorial hk hd]
  exact factorial_mul_intervalLcm_dvd_ascFactorial_mul_initialLcm
    (by omega) (by omega)

lemma centeredDiffProduct_succ
    {k d : ℕ} (hk : 1 ≤ k) (hd : k + 1 ≤ d) :
    centeredDiffProduct (k + 1) d =
      (d - k) * centeredDiffProduct k d * (d + k) := by
  rw [centeredDiffProduct_eq_ascFactorial (by omega) hd,
    centeredDiffProduct_eq_ascFactorial hk (by omega)]
  let a : ℕ := d - k
  have hnewstart : d - (k + 1 - 1) = a := by dsimp [a]
  have ha : a + 1 = d - (k - 1) := by dsimp [a]; omega
  have hlen : 2 * (k + 1) - 1 = 1 + ((2 * k - 1) + 1) := by omega
  rw [hnewstart, ← ha]
  rw [hlen, ← Nat.ascFactorial_mul_ascFactorial]
  simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.mul_one]
  have hfirst : a + 0 = d - k := by dsimp [a]
  have hlast : a + 1 + (2 * k - 1) = d + k := by dsimp [a]; omega
  rw [hfirst, hlast]
  ring

lemma centered_pair_lt_gap_sq {k d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d) :
    (d - k) * (d + k) < d ^ 2 := by
  nlinarith [Nat.sub_add_cancel hd]

/-- A symmetric interval product never exceeds the corresponding constant
product at its center. -/
lemma centeredDiffProduct_le_gap_pow
    {k d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d) :
    centeredDiffProduct k d ≤ d ^ (2 * k - 1) := by
  induction k using Nat.case_strong_induction_on with
  | hz => omega
  | hi k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp [centeredDiffProduct]
      · have hkpos : 1 ≤ k := by omega
        have hd' : k ≤ d := by omega
        rw [centeredDiffProduct_succ hkpos (by omega)]
        have hpair : (d - k) * (d + k) ≤ d ^ 2 :=
          le_of_lt (centered_pair_lt_gap_sq hkpos hd')
        have hinner := ih k (by omega) hkpos hd'
        calc
          (d - k) * centeredDiffProduct k d * (d + k) =
              ((d - k) * (d + k)) * centeredDiffProduct k d := by ring
          _ ≤ d ^ 2 * d ^ (2 * k - 1) := Nat.mul_le_mul hpair hinner
          _ = d ^ (2 * (k + 1) - 1) := by
            rw [← pow_add]
            congr 1
            omega

/-- For at least three centered factors the preceding bound is strict. -/
lemma centeredDiffProduct_lt_gap_pow
    {k d : ℕ} (hk : 2 ≤ k) (hd : k ≤ d) :
    centeredDiffProduct k d < d ^ (2 * k - 1) := by
  let r : ℕ := k - 1
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hkform : k = r + 1 := by dsimp [r]; omega
  have hrd : r ≤ d := by omega
  rw [hkform, centeredDiffProduct_succ hr (by omega)]
  have hpair := centered_pair_lt_gap_sq hr hrd
  have hinner := centeredDiffProduct_le_gap_pow hr hrd
  have hinnerPos : 0 < centeredDiffProduct r d :=
    centeredDiffProduct_pos hr hrd
  calc
    (d - r) * centeredDiffProduct r d * (d + r) =
        ((d - r) * (d + r)) * centeredDiffProduct r d := by ring
    _ < d ^ 2 * centeredDiffProduct r d :=
      Nat.mul_lt_mul_of_pos_right hpair hinnerPos
    _ ≤ d ^ 2 * d ^ (2 * r - 1) := Nat.mul_le_mul_left _ hinner
    _ = d ^ (2 * (r + 1) - 1) := by
      rw [← pow_add]
      congr 1
      omega

/-! ## Paired lower bounds for the factorial tail -/

lemma even_factorialTail_eq_pairProduct (r : ℕ) :
    (2 * r).ascFactorial (2 * r) =
      ∏ i ∈ Finset.range r,
        ((2 * r + i) * (4 * r - 1 - i)) := by
  rw [Nat.ascFactorial_eq_prod_range]
  have hsplit : Finset.range (2 * r) =
      Finset.range r ∪ Finset.Ico r (2 * r) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range r) (Finset.Ico r (2 * r)) := by
    rw [Finset.disjoint_left]
    intro i hlo hhi
    simp only [Finset.mem_range] at hlo
    simp only [Finset.mem_Ico] at hhi
    omega
  rw [hsplit, Finset.prod_union hdisj]
  have hhigh :
      (∏ j ∈ Finset.Ico r (2 * r), (2 * r + j)) =
        ∏ i ∈ Finset.range r, (4 * r - 1 - i) := by
    refine Finset.prod_bij (fun j _ => 2 * r - 1 - j) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_range]
      omega
    · intro j₁ hj₁ j₂ hj₂ he
      simp only [Finset.mem_Ico] at hj₁ hj₂
      change 2 * r - 1 - j₁ = 2 * r - 1 - j₂ at he
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      refine ⟨2 * r - 1 - i, ?_, ?_⟩
      · simp only [Finset.mem_Ico]
        omega
      · change 2 * r - 1 - (2 * r - 1 - i) = i
        omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      change 2 * r + j = 4 * r - 1 - (2 * r - 1 - j)
      omega
  rw [hhigh, ← Finset.prod_mul_distrib]

lemma odd_factorialTail_eq_middle_mul_pairProduct (r : ℕ) :
    (2 * r + 1).ascFactorial (2 * r + 1) =
      (3 * r + 1) *
        ∏ i ∈ Finset.range r,
          ((2 * r + 1 + i) * (4 * r + 1 - i)) := by
  rw [Nat.ascFactorial_eq_prod_range]
  have hsplit : Finset.range (2 * r + 1) =
      (Finset.range r ∪ {r}) ∪ Finset.Ioc r (2 * r) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_Ioc]
    omega
  have hdisjLow : Disjoint (Finset.range r) ({r} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro i hi hir
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_singleton] at hir
    omega
  have hdisj : Disjoint (Finset.range r ∪ {r}) (Finset.Ioc r (2 * r)) := by
    rw [Finset.disjoint_left]
    intro i hi hhi
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at hi
    simp only [Finset.mem_Ioc] at hhi
    omega
  rw [hsplit, Finset.prod_union hdisj, Finset.prod_union hdisjLow]
  simp only [Finset.prod_singleton]
  have hhigh :
      (∏ j ∈ Finset.Ioc r (2 * r), (2 * r + 1 + j)) =
        ∏ i ∈ Finset.range r, (4 * r + 1 - i) := by
    refine Finset.prod_bij (fun j _ => 2 * r - j) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ioc] at hj
      simp only [Finset.mem_range]
      omega
    · intro j₁ hj₁ j₂ hj₂ he
      simp only [Finset.mem_Ioc] at hj₁ hj₂
      change 2 * r - j₁ = 2 * r - j₂ at he
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      refine ⟨2 * r - i, ?_, ?_⟩
      · simp only [Finset.mem_Ioc]
        omega
      · change 2 * r - (2 * r - i) = i
        omega
    · intro j hj
      simp only [Finset.mem_Ioc] at hj
      change 2 * r + 1 + j = 4 * r + 1 - (2 * r - j)
      omega
  rw [hhigh]
  calc
    (∏ x ∈ Finset.range r, (2 * r + 1 + x)) * (2 * r + 1 + r) *
          ∏ i ∈ Finset.range r, (4 * r + 1 - i) =
        (3 * r + 1) *
          ((∏ x ∈ Finset.range r, (2 * r + 1 + x)) *
            ∏ i ∈ Finset.range r, (4 * r + 1 - i)) := by
      ring
    _ = (3 * r + 1) *
        ∏ i ∈ Finset.range r,
          ((2 * r + 1 + i) * (4 * r + 1 - i)) := by
      rw [Finset.prod_mul_distrib]

lemma factorialTail_pair_term_lower
    {k r i : ℕ} (hk : 1 ≤ k) (hi : i < r) (hr : 2 * r ≤ k) :
    k * (2 * k - 1) ≤ (k + i) * (2 * k - 1 - i) := by
  have hiK : i ≤ k - 1 := by omega
  let q : ℕ := k - 1 - i
  have hiq : i + q = k - 1 := by dsimp [q]; omega
  have htail : 2 * k - 1 - i = k + q := by dsimp [q]; omega
  rw [htail]
  have hbase : 2 * k - 1 = k + (k - 1) := by omega
  have heq : (k + i) * (k + q) =
      k * (2 * k - 1) + i * q := by
    rw [hbase, ← hiq]
    ring
  rw [heq]
  exact Nat.le_add_right _ _

lemma factorialTail_pairProduct_lower
    {k r : ℕ} (hk : 1 ≤ k) (hr : 2 * r ≤ k) :
    (k * (2 * k - 1)) ^ r ≤
      ∏ i ∈ Finset.range r, ((k + i) * (2 * k - 1 - i)) := by
  calc
    (k * (2 * k - 1)) ^ r =
        ∏ _i ∈ Finset.range r, (k * (2 * k - 1)) := by
      simp [Finset.prod_const]
    _ ≤ ∏ i ∈ Finset.range r, ((k + i) * (2 * k - 1 - i)) := by
      apply Finset.prod_le_prod'
      intro i hi
      exact factorialTail_pair_term_lower hk (Finset.mem_range.mp hi) hr

lemma even_factorialTail_pair_lower (r : ℕ) (hr : 1 ≤ r) :
    ((2 * r) * (2 * (2 * r) - 1)) ^ r ≤
      (2 * r).ascFactorial (2 * r) := by
  rw [even_factorialTail_eq_pairProduct]
  have hnorm : 2 * (2 * r) - 1 = 4 * r - 1 := by omega
  simpa only [hnorm] using
    (factorialTail_pairProduct_lower (k := 2 * r) (r := r)
      (by omega) (by omega))

lemma odd_factorialTail_pair_lower (r : ℕ) :
    (2 * r + 1) *
        (((2 * r + 1) * (2 * (2 * r + 1) - 1)) ^ r) ≤
      (2 * r + 1).ascFactorial (2 * r + 1) := by
  rw [odd_factorialTail_eq_middle_mul_pairProduct]
  apply Nat.mul_le_mul
  · omega
  · have hnorm : 2 * (2 * r + 1) - 1 = 4 * r + 1 := by omega
    simpa only [hnorm] using
      (factorialTail_pairProduct_lower (k := 2 * r + 1) (r := r)
        (by omega) (by omega))

lemma centeredDiffLcm_dvd_initialLcm
    {k d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d) :
    centeredDiffLcm k d ∣ initialLcm (d + k - 1) := by
  unfold centeredDiffLcm
  apply Finset.lcm_dvd
  intro h hh
  simp only [Finset.mem_Icc] at hh
  apply term_dvd_initialLcm
  · omega
  · omega

lemma centeredDiffLcm_le_eight_pow
    {k d : ℕ} (hk : 1 ≤ k) (hd : k ≤ d) :
    centeredDiffLcm k d ≤ 8 ^ (d + k - 1) := by
  have hdvd := centeredDiffLcm_dvd_initialLcm hk hd
  exact le_trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (initialLcm_ne_zero _)) hdvd)
    (initialLcm_le_eight_pow _)

/-! ## A quadratic gap strip -/

/-- The interval theorem and `Λ(m) ≤ 4^m` give a sharp product bound for
the centered lcm. -/
theorem factorial_mul_centeredDiffLcm_lt_four_mul_gap_pow
    {k d : ℕ} (hk : 2 ≤ k) (hd : k ≤ d) :
    (2 * k - 1).factorial * centeredDiffLcm k d <
      (4 * d) ^ (2 * k - 1) := by
  have hdvd :=
    factorial_mul_centeredDiffLcm_dvd_centeredDiffProduct_mul_initialLcm
      (k := k) (d := d) (by omega) hd
  have hrhsPos :
      0 < centeredDiffProduct k d * initialLcm (2 * k - 1) :=
    mul_pos (centeredDiffProduct_pos (by omega) hd)
      (Nat.pos_of_ne_zero (initialLcm_ne_zero _))
  have hdivLe :
      (2 * k - 1).factorial * centeredDiffLcm k d ≤
        centeredDiffProduct k d * initialLcm (2 * k - 1) :=
    Nat.le_of_dvd hrhsPos hdvd
  have hprod := centeredDiffProduct_lt_gap_pow hk hd
  have hlcm := initialLcm_le_four_pow (2 * k - 1)
  calc
    (2 * k - 1).factorial * centeredDiffLcm k d ≤
        centeredDiffProduct k d * initialLcm (2 * k - 1) := hdivLe
    _ < d ^ (2 * k - 1) * initialLcm (2 * k - 1) :=
      Nat.mul_lt_mul_of_pos_right hprod
        (Nat.pos_of_ne_zero (initialLcm_ne_zero _))
    _ ≤ d ^ (2 * k - 1) * 4 ^ (2 * k - 1) :=
      Nat.mul_le_mul_left _ hlcm
    _ = (4 * d) ^ (2 * k - 1) := by rw [Nat.mul_pow]; ring

/-- Combined with the banked one-factorial matching compression, every
solution has this exact factorial-scaled upper bound. -/
theorem factorial_mul_blockProduct_lt_factorial_mul_four_gap_pow_of_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (2 * k - 1).factorial * blockProduct k n <
      (k - 1).factorial * (4 * d) ^ (2 * k - 1) := by
  have hdvd := blockProduct_dvd_factorial_mul_centeredDiffLcm_four
    (k := k) (n := n) (d := d) (by omega) hd heq
  have hLpos : 0 < centeredDiffLcm k d :=
    Nat.pos_of_ne_zero (centeredDiffLcm_ne_zero (by omega) hd)
  have hblockLe : blockProduct k n ≤
      (k - 1).factorial * centeredDiffLcm k d :=
    Nat.le_of_dvd (mul_pos (Nat.factorial_pos _) hLpos) hdvd
  have hinterval := factorial_mul_centeredDiffLcm_lt_four_mul_gap_pow
    (k := k) (d := d) (by omega) hd
  calc
    (2 * k - 1).factorial * blockProduct k n ≤
        (2 * k - 1).factorial *
          ((k - 1).factorial * centeredDiffLcm k d) :=
      Nat.mul_le_mul_left _ hblockLe
    _ = (k - 1).factorial *
        ((2 * k - 1).factorial * centeredDiffLcm k d) := by ring
    _ < (k - 1).factorial * (4 * d) ^ (2 * k - 1) :=
      Nat.mul_lt_mul_of_pos_left hinterval (Nat.factorial_pos _)

lemma thirteen_mul_row_gap_lt_twenty_mul_start_of_four_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    13 * k * d < 20 * n := by
  have hsharp : 1218443 * k * d < 1853952 * n :=
    maximal_sharp_bracket_ratio_of_four_solution hk hd heq
  nlinarith

/-- Product form of the coarse exact ratio `13*k*d < 20*n`. -/
theorem thirteen_row_gap_pow_lt_twenty_pow_mul_blockProduct_of_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (13 * k * d) ^ k < 20 ^ k * blockProduct k n := by
  have hratio := thirteen_mul_row_gap_lt_twenty_mul_start_of_four_solution
    hk hd heq
  have hterm : ∀ i ∈ Finset.Icc 1 k,
      13 * k * d < 20 * (n + i) := by
    intro i hi
    omega
  have hprod :
      (∏ _i ∈ Finset.Icc 1 k, (13 * k * d)) <
        ∏ i ∈ Finset.Icc 1 k, 20 * (n + i) := by
    apply Finset.prod_lt_prod
    · intro i hi
      exact mul_pos (mul_pos (by norm_num) (by omega)) (by omega)
    · intro i hi
      exact le_of_lt (hterm i hi)
    · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩,
        hterm 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)⟩
  have hcard : (Finset.Icc 1 k).card = k := by
    rw [Nat.card_Icc]
    omega
  simpa [blockProduct, Finset.prod_const, hcard,
    Finset.prod_mul_distrib] using hprod

/-- Necessary inequality obtained by putting the ratio lower bound and the
interval-lcm upper bound on the same scale. -/
theorem factorial_scaled_ratio_lt_interval_bound_of_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    (2 * k - 1).factorial * (13 * k * d) ^ k <
      20 ^ k * ((k - 1).factorial * (4 * d) ^ (2 * k - 1)) := by
  have hlower :=
    thirteen_row_gap_pow_lt_twenty_pow_mul_blockProduct_of_solution hk hd heq
  have hupper :=
    factorial_mul_blockProduct_lt_factorial_mul_four_gap_pow_of_solution
      hk hd heq
  calc
    (2 * k - 1).factorial * (13 * k * d) ^ k <
        (2 * k - 1).factorial * (20 ^ k * blockProduct k n) :=
      Nat.mul_lt_mul_of_pos_left hlower (Nat.factorial_pos _)
    _ = 20 ^ k * ((2 * k - 1).factorial * blockProduct k n) := by ring
    _ < 20 ^ k *
        ((k - 1).factorial * (4 * d) ^ (2 * k - 1)) :=
      Nat.mul_lt_mul_of_pos_left hupper (pow_pos (by norm_num) _)

/-- One paired factorial-tail unit pays for two ratio factors and four
interval factors under `18*d ≤ k^2`.  This is the exact-arithmetic core of
the quadratic strip. -/
lemma quadratic_pair_unit_bound
    {k d : ℕ} (hk : 16 ≤ k) (hstrip : 18 * d ≤ k ^ 2) :
    20 ^ 2 * (4 * d) ^ 4 ≤
      (k * (2 * k - 1)) * (13 * k * d) ^ 2 := by
  have hsquare := Nat.pow_le_pow_left hstrip 2
  have hsquare' : 324 * d ^ 2 ≤ k ^ 4 := by
    calc
      324 * d ^ 2 = (18 * d) ^ 2 := by ring
      _ ≤ (k ^ 2) ^ 2 := hsquare
      _ = k ^ 4 := by ring
  have htwok : 2 * k - 1 + 1 = 2 * k := by omega
  have hcoeff : 102400 * k ≤ (324 * 169) * (2 * k - 1) := by
    nlinarith
  have hcross :
      324 * (102400 * d ^ 2) ≤
        324 * (169 * k ^ 3 * (2 * k - 1)) := by
    calc
      324 * (102400 * d ^ 2) = 102400 * (324 * d ^ 2) := by ring
      _ ≤ 102400 * k ^ 4 := Nat.mul_le_mul_left _ hsquare'
      _ = (102400 * k) * k ^ 3 := by ring
      _ ≤ ((324 * 169) * (2 * k - 1)) * k ^ 3 :=
        Nat.mul_le_mul_right _ hcoeff
      _ = 324 * (169 * k ^ 3 * (2 * k - 1)) := by ring
  have hcore : 102400 * d ^ 2 ≤ 169 * k ^ 3 * (2 * k - 1) :=
    Nat.le_of_mul_le_mul_left hcross (by norm_num)
  have hcoreD := Nat.mul_le_mul_right (d ^ 2) hcore
  calc
    20 ^ 2 * (4 * d) ^ 4 = (102400 * d ^ 2) * d ^ 2 := by ring
    _ ≤ (169 * k ^ 3 * (2 * k - 1)) * d ^ 2 := hcoreD
    _ = (k * (2 * k - 1)) * (13 * k * d) ^ 2 := by ring

/-- Parity-free factorial-tail certificate.  Even rows pair all tail terms;
odd rows use the same pairs and retain one unpaired term at least `k`. -/
lemma quadratic_strip_factorialTail_certificate
    {k d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hstrip : 18 * d ≤ k ^ 2) :
    20 ^ k * (4 * d) ^ (2 * k - 1) ≤
      k.ascFactorial k * (13 * k * d) ^ k := by
  have hunit := quadratic_pair_unit_bound hk hstrip
  rcases Nat.even_or_odd k with hEven | hOdd
  · obtain ⟨r, hrEq⟩ := hEven
    have hform : k = 2 * r := by omega
    have hr : 1 ≤ r := by omega
    have hunitPow := Nat.pow_le_pow_left hunit r
    have htail := even_factorialTail_pair_lower r hr
    have hpad : (4 * d) ^ (4 * r - 1) ≤ (4 * d) ^ (4 * r) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have heven :
        20 ^ (2 * r) * (4 * d) ^ (4 * r - 1) ≤
          (2 * r).ascFactorial (2 * r) *
            (13 * (2 * r) * d) ^ (2 * r) := by
      calc
        20 ^ (2 * r) * (4 * d) ^ (4 * r - 1) ≤
            20 ^ (2 * r) * (4 * d) ^ (4 * r) :=
          Nat.mul_le_mul_left _ hpad
        _ = (20 ^ 2 * (4 * d) ^ 4) ^ r := by
          simp only [mul_pow, pow_mul]
        _ ≤ ((2 * r) * (2 * (2 * r) - 1) *
            (13 * (2 * r) * d) ^ 2) ^ r := by
          simpa only [hform] using hunitPow
        _ = (((2 * r) * (2 * (2 * r) - 1)) ^ r) *
            (13 * (2 * r) * d) ^ (2 * r) := by
          simp only [mul_pow, pow_mul]
        _ ≤ (2 * r).ascFactorial (2 * r) *
            (13 * (2 * r) * d) ^ (2 * r) :=
          Nat.mul_le_mul_right _ htail
    simpa only [hform, show 2 * (2 * r) - 1 = 4 * r - 1 by omega]
      using heven
  · obtain ⟨r, hrEq⟩ := hOdd
    have hform : k = 2 * r + 1 := by omega
    have hunitPow := Nat.pow_le_pow_left hunit r
    have htail := odd_factorialTail_pair_lower r
    have hcoeff : 80 ≤ 13 * k ^ 2 := by nlinarith
    have hleftover : 20 * (4 * d) ≤ k * (13 * k * d) := by
      have hmul := Nat.mul_le_mul_right d hcoeff
      nlinarith
    have hodd :
        20 ^ (2 * r + 1) * (4 * d) ^ (4 * r + 1) ≤
          (2 * r + 1).ascFactorial (2 * r + 1) *
            (13 * (2 * r + 1) * d) ^ (2 * r + 1) := by
      calc
        20 ^ (2 * r + 1) * (4 * d) ^ (4 * r + 1) =
            (20 * (4 * d)) * (20 ^ 2 * (4 * d) ^ 4) ^ r := by
          simp only [pow_add, pow_mul, mul_pow, pow_one]
          ring
        _ ≤ ((2 * r + 1) * (13 * (2 * r + 1) * d)) *
            (((2 * r + 1) * (2 * (2 * r + 1) - 1) *
              (13 * (2 * r + 1) * d) ^ 2) ^ r) := by
          apply Nat.mul_le_mul
          · simpa only [hform] using hleftover
          · simpa only [hform] using hunitPow
        _ = ((2 * r + 1) *
              (((2 * r + 1) * (2 * (2 * r + 1) - 1)) ^ r)) *
            (13 * (2 * r + 1) * d) ^ (2 * r + 1) := by
          simp only [mul_pow, pow_mul, pow_add, pow_one]
          ring
        _ ≤ (2 * r + 1).ascFactorial (2 * r + 1) *
            (13 * (2 * r + 1) * d) ^ (2 * r + 1) :=
          Nat.mul_le_mul_right _ htail
    simpa only [hform, show 2 * (2 * r + 1) - 1 = 4 * r + 1 by omega]
      using hodd

lemma factorial_mul_factorialTail {k : ℕ} (hk : 1 ≤ k) :
    (k - 1).factorial * k.ascFactorial k = (2 * k - 1).factorial := by
  have h := Nat.factorial_mul_ascFactorial (k - 1) k
  have hstart : k - 1 + 1 = k := by omega
  have hend : k - 1 + k = 2 * k - 1 := by omega
  rw [hstart, hend] at h
  exact h

/-- Exact cross-multiplied certificate contradicting the necessary solution
inequality throughout the quadratic strip. -/
theorem quadratic_strip_certificate
    {k d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hstrip : 18 * d ≤ k ^ 2) :
    20 ^ k * ((k - 1).factorial * (4 * d) ^ (2 * k - 1)) ≤
      (2 * k - 1).factorial * (13 * k * d) ^ k := by
  have htail := quadratic_strip_factorialTail_certificate hk hd hstrip
  have hmul := Nat.mul_le_mul_left (k - 1).factorial htail
  calc
    20 ^ k * ((k - 1).factorial * (4 * d) ^ (2 * k - 1)) =
        (k - 1).factorial *
          (20 ^ k * (4 * d) ^ (2 * k - 1)) := by ring
    _ ≤ (k - 1).factorial *
        (k.ascFactorial k * (13 * k * d) ^ k) := hmul
    _ = (2 * k - 1).factorial * (13 * k * d) ^ k := by
      rw [← mul_assoc, factorial_mul_factorialTail (by omega)]

/-- Uniform all-parity quadratic strip.  The condition is nonempty from
`k=18` onward (for example its first boundary point is `k=d=18`). -/
theorem no_four_solution_of_quadratic_strip
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (hstrip : 18 * d ≤ k ^ 2) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  have hnecessary := factorial_scaled_ratio_lt_interval_bound_of_solution
    hk hd heq
  have hcertificate := quadratic_strip_certificate hk hd hstrip
  exact (Nat.not_lt_of_ge hcertificate) hnecessary

/-! ## Necessary size inequality and the logarithmic strip -/

/-- Every large-row solution satisfies the exact exponential lcm
obstruction used by the strip theorem. -/
theorem gap_pow_size_lt_eight_pow_of_four_solution
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    k * d ^ k < 2 ^ k * 8 ^ (d + k - 1) := by
  have hratio : 1218443 * k * d < 1853952 * n :=
    maximal_sharp_bracket_ratio_of_four_solution hk hd heq
  have hkd2n : k * d < 2 * n := by
    nlinarith
  have hterm : ∀ i ∈ Finset.Icc 1 k, k * d < 2 * (n + i) := by
    intro i hi
    omega
  have hprodLt :
      (∏ _i ∈ Finset.Icc 1 k, k * d) <
        ∏ i ∈ Finset.Icc 1 k, 2 * (n + i) := by
    apply Finset.prod_lt_prod
    · intro i hi
      exact mul_pos (by omega) (by omega)
    · intro i hi
      exact le_of_lt (hterm i hi)
    · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩,
        hterm 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)⟩
  have hcard : (Finset.Icc 1 k).card = k := by
    rw [Nat.card_Icc]
    omega
  have hblockLt : (k * d) ^ k < 2 ^ k * blockProduct k n := by
    simpa [blockProduct, Finset.prod_const, hcard,
      Finset.prod_mul_distrib] using hprodLt
  have hdvd := blockProduct_dvd_factorial_mul_centeredDiffLcm_four
    (k := k) (n := n) (d := d) (by omega) hd heq
  have hclcm0 : 0 < centeredDiffLcm k d :=
    Nat.pos_of_ne_zero (centeredDiffLcm_ne_zero (by omega) hd)
  have hblockLe : blockProduct k n ≤
      (k - 1).factorial * centeredDiffLcm k d :=
    Nat.le_of_dvd (mul_pos (Nat.factorial_pos _) hclcm0) hdvd
  have hfac : (k - 1).factorial ≤ k ^ (k - 1) := by
    exact le_trans (Nat.factorial_le_pow (k - 1))
      (Nat.pow_le_pow_left (by omega : k - 1 ≤ k) (k - 1))
  have hlcm : centeredDiffLcm k d ≤ 8 ^ (d + k - 1) :=
    centeredDiffLcm_le_eight_pow (by omega) hd
  have hupper : blockProduct k n ≤ k ^ (k - 1) * 8 ^ (d + k - 1) :=
    le_trans hblockLe (Nat.mul_le_mul hfac hlcm)
  have hkpow : k ^ k = k ^ (k - 1) * k := by
    calc
      k ^ k = k ^ ((k - 1) + 1) := by congr 1; omega
      _ = k ^ (k - 1) * k := by rw [pow_succ]
  have hscaled :
      k ^ (k - 1) * (k * d ^ k) <
        k ^ (k - 1) * (2 ^ k * 8 ^ (d + k - 1)) := by
    calc
      k ^ (k - 1) * (k * d ^ k) = (k * d) ^ k := by
        rw [Nat.mul_pow, hkpow]
        ring
      _ < 2 ^ k * blockProduct k n := hblockLt
      _ ≤ 2 ^ k * (k ^ (k - 1) * 8 ^ (d + k - 1)) :=
        Nat.mul_le_mul_left (2 ^ k) hupper
      _ = k ^ (k - 1) * (2 ^ k * 8 ^ (d + k - 1)) := by ring
  exact (Nat.mul_lt_mul_left (pow_pos (by omega : 0 < k) _)).mp hscaled

/-- A stronger direct logarithmic strip.  Asymptotically it reaches
`d ≤ k*(floor(log₂ k)-4)/3`, nearly twice the proposed `/6` range. -/
theorem no_four_solution_of_extended_logarithmic_strip
    {k n d : ℕ} (hk : 256 ≤ k) (hd : k ≤ d)
    (hstrip : 3 * d ≤ k * (Nat.log 2 k - 4)) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  let ell : ℕ := Nat.log 2 k
  have hk0 : k ≠ 0 := by omega
  have hell : 8 ≤ ell := by
    dsimp [ell]
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num
    exact hk
  have hpell : 2 ^ ell ≤ k := by
    dsimp [ell]
    exact Nat.pow_log_le_self 2 hk0
  have hstrip' : 3 * d ≤ k * (ell - 4) := by
    simpa [ell] using hstrip
  have hexp : k + 3 * (d + k - 1) ≤ ell * (k + 1) := by
    calc
      k + 3 * (d + k - 1) ≤ 4 * k + 3 * d := by omega
      _ ≤ 4 * k + k * (ell - 4) := Nat.add_le_add_left hstrip' _
      _ = k * ell := by
        calc
          4 * k + k * (ell - 4) = k * (4 + (ell - 4)) := by ring
          _ = k * ell := by congr 1; omega
      _ ≤ ell * (k + 1) := by nlinarith
  have hcert : 2 ^ k * 8 ^ (d + k - 1) ≤ k * d ^ k := by
    calc
      2 ^ k * 8 ^ (d + k - 1) =
          2 ^ (k + 3 * (d + k - 1)) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add]
      _ ≤ 2 ^ (ell * (k + 1)) :=
        Nat.pow_le_pow_right (by norm_num) hexp
      _ = (2 ^ ell) ^ (k + 1) := by rw [pow_mul]
      _ ≤ k ^ (k + 1) := Nat.pow_le_pow_left hpell (k + 1)
      _ = k * k ^ k := by rw [pow_succ]; ring
      _ ≤ k * d ^ k :=
        Nat.mul_le_mul_left k (Nat.pow_le_pow_left hd k)
  intro heq
  have hnecessary := gap_pow_size_lt_eight_pow_of_four_solution
    (k := k) (n := n) (d := d) (by omega) hd heq
  exact (Nat.not_lt_of_ge hcert) hnecessary

/-- Uniform logarithmic strip, strengthened to all row parities.  The direct
endpoint estimate only uses `d ≤ k*floor(log₂ k)/6` and `d ≥ k`; no
monotonicity argument or floor lower bound is needed. -/
theorem no_four_solution_of_logarithmic_strip
    {k n d : ℕ} (hk : 256 ≤ k) (hd : k ≤ d)
    (hstrip : d ≤ (k * Nat.log 2 k) / 6) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  let ell : ℕ := Nat.log 2 k
  have hk0 : k ≠ 0 := by omega
  have hell : 8 ≤ ell := by
    dsimp [ell]
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num
    exact hk
  have hpell : 2 ^ ell ≤ k := by
    dsimp [ell]
    exact Nat.pow_log_le_self 2 hk0
  have h6d : 6 * d ≤ k * ell := by
    have hdiv := Nat.div_mul_le_self (k * ell) 6
    dsimp [ell] at hstrip ⊢
    omega
  have hexp : k + 3 * (d + k - 1) ≤ ell * (k + 1) := by
    calc
      k + 3 * (d + k - 1) ≤ 4 * k + 3 * d := by omega
      _ ≤ ell * (k + 1) := by nlinarith
  have hcert : 2 ^ k * 8 ^ (d + k - 1) ≤ k * d ^ k := by
    calc
      2 ^ k * 8 ^ (d + k - 1) =
          2 ^ (k + 3 * (d + k - 1)) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add]
      _ ≤ 2 ^ (ell * (k + 1)) :=
        Nat.pow_le_pow_right (by norm_num) hexp
      _ = (2 ^ ell) ^ (k + 1) := by rw [pow_mul]
      _ ≤ k ^ (k + 1) := Nat.pow_le_pow_left hpell (k + 1)
      _ = k * k ^ k := by rw [pow_succ]; ring
      _ ≤ k * d ^ k :=
        Nat.mul_le_mul_left k (Nat.pow_le_pow_left hd k)
  intro heq
  have hnecessary := gap_pow_size_lt_eight_pow_of_four_solution
    (k := k) (n := n) (d := d) (by omega) hd heq
  exact (Nat.not_lt_of_ge hcert) hnecessary

/-! ## A sharp reflected-center component bound -/

/-- In an even row the already-banked reflected square lift has positive
absolute value `H + 3(n+i)`, where `H = 2n+d+k+1`.  Reflection also gives
`2(n+i) < H`, so the complete large-prime component satisfies the sharper
uniform inequality `2*q^2 < 5*H`.

This improves the proposed constant `8*q^2 < 23*H` and does not need the
large-row ratio window. -/
theorem even_large_prime_reflection_center_power_two_sq_lt_five_center
    {p k n d : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hkp : k < p)
    (hpS : p ∣ 2 * n + d + k + 1) (hkeven : Even k)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    2 * (p ^ (2 * n + d + k + 1).factorization p) ^ 2 <
      5 * (2 * n + d + k + 1) := by
  obtain ⟨i, hi, hlift⟩ :=
    exists_large_prime_reflection_center_square_lift_four
      hp hk hd hkp hpS heq
  let q : ℕ := p ^ (2 * n + d + k + 1).factorization p
  let A : ℕ := n + i
  let B : ℕ := n + d + (k + 1 - i)
  let H : ℕ := 2 * n + d + k + 1
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hpredOdd : Odd (k - 1) :=
    Nat.Even.sub_odd (by omega : 1 ≤ k) hkeven (by norm_num)
  have hsign : (-1 : ℤ) ^ (k - 1) = -1 := Odd.neg_one_pow hpredOdd
  have hlift' : (q : ℤ) ^ 2 ∣ -((B + 4 * A : ℕ) : ℤ) := by
    rw [hsign] at hlift
    dsimp [q, A, B] at hlift ⊢
    convert hlift using 1
    ring
  have hliftPos : (q : ℤ) ^ 2 ∣ ((B + 4 * A : ℕ) : ℤ) :=
    dvd_neg.mp hlift'
  have hliftNat : q ^ 2 ∣ B + 4 * A := by
    exact_mod_cast hliftPos
  have hRpos : 0 < B + 4 * A := by
    dsimp [A, B]
    omega
  have hqle : q ^ 2 ≤ B + 4 * A := Nat.le_of_dvd hRpos hliftNat
  have hAB : A + B = H := by
    dsimp [A, B, H]
    omega
  have hAltB : A < B := by
    dsimp [A, B]
    omega
  have hRlt : 2 * (B + 4 * A) < 5 * H := by
    omega
  simpa [q, H] using lt_of_le_of_lt (Nat.mul_le_mul_left 2 hqle) hRlt

/-- Dominant-component obstruction in its cleanest form. -/
theorem no_four_solution_of_even_dominant_reflection_center_component
    {p k n d : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hkp : k < p)
    (hpS : p ∣ 2 * n + d + k + 1) (hkeven : Even k)
    (hdom : 5 * (2 * n + d + k + 1) ≤
      2 * (p ^ (2 * n + d + k + 1).factorization p) ^ 2) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  exact (Nat.not_lt_of_ge hdom)
    (even_large_prime_reflection_center_power_two_sq_lt_five_center
      hp hk hd hkp hpS hkeven heq)

/-- Cofactor form of the sharp dominant-component obstruction.  Here `q` is
the complete `p`-primary component of the reflection center. -/
theorem no_four_solution_of_even_reflection_center_cofactor
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hkp : k < p)
    (hpS : p ∣ 2 * n + d + k + 1) (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (hdom : 5 * a ≤ 2 * p ^ (2 * n + d + k + 1).factorization p) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  let q := p ^ (2 * n + d + k + 1).factorization p
  apply no_four_solution_of_even_dominant_reflection_center_component
    hp hk hd hkp hpS hkeven
  calc
    5 * (2 * n + d + k + 1) = (5 * a) * q := by rw [hfactor]; ring
    _ ≤ (2 * q) * q := Nat.mul_le_mul_right q hdom
    _ = 2 * q ^ 2 := by ring

/-- The proposed `23*a ≤ 8*q` obstruction is a strict weakening of the
sharp `5*a ≤ 2*q` cofactor condition. -/
theorem no_four_solution_of_even_reflection_center_twentyThree_eight
    {p k n d a : ℕ}
    (hp : p.Prime) (hk : 16 ≤ k) (hd : k ≤ d) (hkp : k < p)
    (hpS : p ∣ 2 * n + d + k + 1) (hkeven : Even k)
    (hfactor : 2 * n + d + k + 1 =
      a * p ^ (2 * n + d + k + 1).factorization p)
    (hdom : 23 * a ≤ 8 * p ^ (2 * n + d + k + 1).factorization p) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  apply no_four_solution_of_even_reflection_center_cofactor
    hp hk hd hkp hpS hkeven hfactor
  omega

#print axioms gcd_gap_reflectionCenter_dvd_oddDoubleFactorial
#print axioms prime_ge_row_dvd_gap_not_dvd_reflectionCenter
#print axioms initialLcm_le_eight_pow
#print axioms initialLcm_le_four_pow
#print axioms factorial_mul_intervalLcm_dvd_ascFactorial_mul_initialLcm
#print axioms factorial_mul_centeredDiffLcm_dvd_centeredDiffProduct_mul_initialLcm
#print axioms factorial_mul_centeredDiffLcm_lt_four_mul_gap_pow
#print axioms quadratic_strip_certificate
#print axioms no_four_solution_of_quadratic_strip
#print axioms gap_pow_size_lt_eight_pow_of_four_solution
#print axioms no_four_solution_of_extended_logarithmic_strip
#print axioms no_four_solution_of_logarithmic_strip
#print axioms even_large_prime_reflection_center_power_two_sq_lt_five_center
#print axioms no_four_solution_of_even_dominant_reflection_center_component
#print axioms no_four_solution_of_even_reflection_center_cofactor
#print axioms no_four_solution_of_even_reflection_center_twentyThree_eight

end Erdos686Variant
end Erdos686
