/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.NormalizedMatching
import ErdosProblems.Erdos686.Core.CanonicalOwnerMatrix
import ErdosProblems.Erdos686.Core.OsculationTaylor

/-!
# Erdős 686: full-mass normalization with one global factorial loss

The high-prime normalized matching theorem cancels its whole factorial
prefactor because a large-prime owner is coprime to `(k-1)!`.  For a general
canonical owner the exact surviving modulus is instead

`P^2 / gcd(P^2,q)`.

This file proves that cancellation without any primality assumption.  More
importantly, over a pairwise-coprime family of canonical owners, the local
gcd losses are pairwise coprime and their product divides a *single* common
coefficient bound `L`.  Thus the complete owner square mass divides `L`
times the product of the normalized local forms.  There is no factor
`L^|S|`, and no omission of the small-prime owners.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

/-- The part of an owner square which survives cancellation of a possibly
nonunit local coefficient. -/
def reducedOwnerSquare (P q : ℕ) : ℕ :=
  P ^ 2 / Nat.gcd (P ^ 2) q

/-- The complementary loss in the nonunit normalization. -/
def ownerNormalizationLoss (P q : ℕ) : ℕ :=
  Nat.gcd (P ^ 2) q

/-- Exact nonunit cancellation over `ℤ`.  No inverse modulo `P^2` is used:
after removing the common gcd, ordinary Euclid cancellation applies. -/
theorem reducedOwnerSquare_dvd_of_square_dvd_coefficient_mul
    {P q : ℕ} {F : ℤ}
    (hP : 0 < P)
    (hweighted : (((P ^ 2 : ℕ) : ℤ)) ∣ (q : ℤ) * F) :
    ((reducedOwnerSquare P q : ℕ) : ℤ) ∣ F := by
  let g := Nat.gcd (P ^ 2) q
  let A := P ^ 2 / g
  let B := q / g
  have hP2 : 0 < P ^ 2 := pow_pos hP 2
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q hP2
  have hgP : g ∣ P ^ 2 := Nat.gcd_dvd_left _ _
  have hgq : g ∣ q := Nat.gcd_dvd_right _ _
  have hPA : g * A = P ^ 2 := by
    exact Nat.mul_div_cancel' hgP
  have hqB : g * B = q := by
    exact Nat.mul_div_cancel' hgq
  have hcopNat : A.Coprime B :=
    Nat.coprime_div_gcd_div_gcd hg
  have hcop : IsCoprime (A : ℤ) (B : ℤ) := hcopNat.isCoprime
  obtain ⟨z, hz⟩ := hweighted
  have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  have hqBZ : (g : ℤ) * (B : ℤ) = (q : ℤ) := by
    exact_mod_cast hqB
  have hPAZ : (g : ℤ) * (A : ℤ) = ((P ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast hPA
  have hcancel : (B : ℤ) * F = (A : ℤ) * z := by
    apply mul_left_cancel₀ hgZ
    calc
      (g : ℤ) * ((B : ℤ) * F) = (q : ℤ) * F := by
        rw [← mul_assoc, hqBZ]
      _ = ((P ^ 2 : ℕ) : ℤ) * z := hz
      _ = (g : ℤ) * ((A : ℤ) * z) := by
        rw [← mul_assoc, hPAZ]
  change (A : ℤ) ∣ F
  apply hcop.dvd_of_dvd_mul_left
  exact ⟨z, hcancel⟩

/-- The reduced and lost factors reconstruct the complete owner square. -/
theorem ownerNormalizationLoss_mul_reducedOwnerSquare
    {P q : ℕ} :
    ownerNormalizationLoss P q * reducedOwnerSquare P q = P ^ 2 := by
  unfold ownerNormalizationLoss reducedOwnerSquare
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left (P ^ 2) q)

/-- A local normalization loss divides every common coefficient bound which
is divisible by the local prefactor. -/
theorem ownerNormalizationLoss_dvd
    {P q L : ℕ} (hq : q ∣ L) :
    ownerNormalizationLoss P q ∣ L :=
  dvd_trans (Nat.gcd_dvd_right (P ^ 2) q) hq

/-- Losses belonging to coprime owners remain coprime, independently of the
local coefficients. -/
theorem ownerNormalizationLoss_coprime
    {P Q q r : ℕ} (hPQ : P.Coprime Q) :
    (ownerNormalizationLoss P q).Coprime
      (ownerNormalizationLoss Q r) := by
  apply Nat.Coprime.of_dvd
      (Nat.gcd_dvd_left (P ^ 2) q)
      (Nat.gcd_dvd_left (Q ^ 2) r)
  exact hPQ.pow 2 2

/-- Across pairwise-coprime owners, all nonunit-normalization losses consume
only one copy of the common coefficient bound. -/
theorem ownerNormalizationLoss_product_dvd_common_bound
    {ι : Type*}
    (S : Finset ι) (P q : ι → ℕ) (L : ℕ)
    (hpair : (S : Set ι).Pairwise (Function.onFun Nat.Coprime P))
    (hq : ∀ e ∈ S, q e ∣ L) :
    (∏ e ∈ S, ownerNormalizationLoss (P e) (q e)) ∣ L := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert e S he ih =>
      rw [Finset.prod_insert he]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · apply Nat.Coprime.prod_right
        intro f hf
        apply ownerNormalizationLoss_coprime
        exact hpair (by simp) (by simp [hf])
          (Ne.symm (ne_of_mem_of_not_mem hf he))
      · exact ownerNormalizationLoss_dvd (hq e (by simp))
      · apply ih
        · intro f hf g hg hfg
          exact hpair (by simp [hf]) (by simp [hg]) hfg
        · intro f hf
          exact hq f (by simp [hf])

/-- Exact reconstruction of the full owner-square product from the products
of the local loss and reduced-modulus factors. -/
theorem ownerSquareProduct_eq_loss_mul_reduced
    {ι : Type*}
    (S : Finset ι) (P q : ι → ℕ) :
    (∏ e ∈ S, P e) ^ 2 =
      (∏ e ∈ S, ownerNormalizationLoss (P e) (q e)) *
        (∏ e ∈ S, reducedOwnerSquare (P e) (q e)) := by
  classical
  rw [← Finset.prod_pow]
  calc
    (∏ e ∈ S, P e ^ 2) =
        ∏ e ∈ S,
          (ownerNormalizationLoss (P e) (q e) *
            reducedOwnerSquare (P e) (q e)) := by
      apply Finset.prod_congr rfl
      intro e he
      exact (ownerNormalizationLoss_mul_reducedOwnerSquare
        (P := P e) (q := q e)).symm
    _ = (∏ e ∈ S, ownerNormalizationLoss (P e) (q e)) *
        (∏ e ∈ S, reducedOwnerSquare (P e) (q e)) := by
      simp only [Finset.prod_mul_distrib]

/-- Full-mass global normalization theorem.  Every local weighted square
congruence may have a nonunit coefficient `q e`, but if all `q e` divide one
common `L`, the square of the *complete* owner product divides `L` times the
product of the normalized forms. -/
theorem full_ownerSquare_product_dvd_commonBound_mul_normalizedProduct
    {ι : Type*}
    (S : Finset ι) (P q : ι → ℕ) (F : ι → ℤ) (L : ℕ)
    (hP : ∀ e ∈ S, 0 < P e)
    (hpair : (S : Set ι).Pairwise (Function.onFun Nat.Coprime P))
    (hq : ∀ e ∈ S, q e ∣ L)
    (hweighted : ∀ e ∈ S,
      (((P e) ^ 2 : ℕ) : ℤ) ∣ (q e : ℤ) * F e) :
    ((((∏ e ∈ S, P e) ^ 2 : ℕ) : ℤ)) ∣
      (L : ℤ) * ∏ e ∈ S, F e := by
  classical
  have hlossNat :=
    ownerNormalizationLoss_product_dvd_common_bound S P q L hpair hq
  have hloss :
      (((∏ e ∈ S, ownerNormalizationLoss (P e) (q e)) : ℕ) : ℤ)
        ∣ (L : ℤ) := by
    exact_mod_cast hlossNat
  have hreduced :
      (((∏ e ∈ S, reducedOwnerSquare (P e) (q e)) : ℕ) : ℤ)
        ∣ ∏ e ∈ S, F e := by
    simpa only [Nat.cast_prod] using Finset.prod_dvd_prod_of_dvd
      (fun e => ((reducedOwnerSquare (P e) (q e) : ℕ) : ℤ)) F
      (fun e he =>
        reducedOwnerSquare_dvd_of_square_dvd_coefficient_mul
          (hP e he) (hweighted e he))
  have hmul := mul_dvd_mul hloss hreduced
  rw [ownerSquareProduct_eq_loss_mul_reduced S P q]
  exact hmul

/-- The reduced square is still a divisor of the complete owner square. -/
theorem reducedOwnerSquare_dvd_square (P q : ℕ) :
    reducedOwnerSquare P q ∣ P ^ 2 := by
  refine ⟨ownerNormalizationLoss P q, ?_⟩
  simpa [mul_comm] using
    (ownerNormalizationLoss_mul_reducedOwnerSquare (P := P) (q := q)).symm

/-- Common-value form of the full-mass normalization theorem.  Unlike the
product-of-local-forms result, this puts every reduced owner square into one
shared integer `Z`.  Pairwise coprimality then yields

`(prod P)^2 | L*Z`.

This is the form needed by bounded bivariate osculation. -/
theorem full_ownerSquare_product_dvd_commonBound_mul_commonValue
    {ι : Type*}
    (S : Finset ι) (P q : ι → ℕ) (L : ℕ) (Z : ℤ)
    (hpair : (S : Set ι).Pairwise (Function.onFun Nat.Coprime P))
    (hq : ∀ e ∈ S, q e ∣ L)
    (hreduced : ∀ e ∈ S,
      ((reducedOwnerSquare (P e) (q e) : ℕ) : ℤ) ∣ Z) :
    ((((∏ e ∈ S, P e) ^ 2 : ℕ) : ℤ)) ∣ (L : ℤ) * Z := by
  classical
  have hlossNat :=
    ownerNormalizationLoss_product_dvd_common_bound S P q L hpair hq
  have hloss :
      (((∏ e ∈ S, ownerNormalizationLoss (P e) (q e)) : ℕ) : ℤ)
        ∣ (L : ℤ) := by
    exact_mod_cast hlossNat
  have hredPair : (S : Set ι).Pairwise
      (fun e f => IsCoprime
        ((reducedOwnerSquare (P e) (q e) : ℕ) : ℤ)
        ((reducedOwnerSquare (P f) (q f) : ℕ) : ℤ)) := by
    intro e he f hf hef
    exact (Nat.Coprime.of_dvd
      (reducedOwnerSquare_dvd_square (P e) (q e))
      (reducedOwnerSquare_dvd_square (P f) (q f))
      ((hpair he hf hef).pow 2 2)).isCoprime
  have hred :
      (((∏ e ∈ S, reducedOwnerSquare (P e) (q e)) : ℕ) : ℤ) ∣ Z := by
    simpa only [Nat.cast_prod] using
      Finset.prod_dvd_of_coprime hredPair hreduced
  have hmul := mul_dvd_mul hloss hred
  rw [ownerSquareProduct_eq_loss_mul_reduced S P q]
  exact hmul

/-- Before any modular inversion, the osculation algebra proves that the
owner square divides `b` times the common evaluation. -/
theorem osculation_owner_square_dvd_coefficient_mul_evaluation
    {r : ℕ} (coeff : OsculationMonomial r → ℤ)
    (P b : ℕ) (A n d j rho : ℤ)
    (hvalue : osculationEvaluate coeff j rho = 0)
    (hdirection : (b : ℤ) * osculationEvaluateDX coeff j rho +
      A * osculationEvaluateDY coeff j rho = 0)
    (hn : (P : ℤ) ∣ n + j) (hd : (P : ℤ) ∣ d + rho)
    (hsquare : ((P : ℤ) ^ 2) ∣
      (b : ℤ) * (d + rho) - A * (n + j)) :
    ((P : ℤ) ^ 2) ∣
      (b : ℤ) * osculationEvaluate coeff (-n) (-d) := by
  let Fx := osculationEvaluateDX coeff j rho
  let Fy := osculationEvaluateDY coeff j rho
  let linear := (n + j) * Fx + (d + rho) * Fy
  have hlinear_mul : ((P : ℤ) ^ 2) ∣ linear * (b : ℤ) := by
    rcases hsquare with ⟨s, hs⟩
    refine ⟨s * Fy, ?_⟩
    dsimp [linear, Fx, Fy]
    calc
      ((n + j) * osculationEvaluateDX coeff j rho +
          (d + rho) * osculationEvaluateDY coeff j rho) * (b : ℤ) =
        ((b : ℤ) * (d + rho) - A * (n + j)) *
            osculationEvaluateDY coeff j rho +
          (n + j) *
            ((b : ℤ) * osculationEvaluateDX coeff j rho +
              A * osculationEvaluateDY coeff j rho) := by ring
      _ = ((b : ℤ) * (d + rho) - A * (n + j)) *
          osculationEvaluateDY coeff j rho := by rw [hdirection]; ring
      _ = (P : ℤ) ^ 2 *
          (s * osculationEvaluateDY coeff j rho) := by rw [hs]; ring
  have hnx : (P : ℤ) ∣ -n - j := by
    rcases hn with ⟨s, hs⟩
    refine ⟨-s, ?_⟩
    calc
      -n - j = -(n + j) := by ring
      _ = -((P : ℤ) * s) := by rw [hs]
      _ = (P : ℤ) * -s := by ring
  have hdy : (P : ℤ) ∣ -d - rho := by
    rcases hd with ⟨s, hs⟩
    refine ⟨-s, ?_⟩
    calc
      -d - rho = -(d + rho) := by ring
      _ = -((P : ℤ) * s) := by rw [hs]
      _ = (P : ℤ) * -s := by ring
  have htaylor := osculation_first_order_remainder_dvd coeff
    (P : ℤ) j rho (-n - j) (-d - rho) hnx hdy
  have hxarg : j + (-n - j) = -n := by ring
  have hyarg : rho + (-d - rho) = -d := by ring
  have hsum : ((P : ℤ) ^ 2) ∣
      osculationEvaluate coeff (-n) (-d) + linear := by
    rw [show osculationEvaluate coeff (-n) (-d) + linear =
        osculationEvaluate coeff (-n) (-d) -
          osculationEvaluate coeff j rho -
          (-n - j) * osculationEvaluateDX coeff j rho -
          (-d - rho) * osculationEvaluateDY coeff j rho by
      rw [hvalue]
      dsimp [linear, Fx, Fy]
      ring]
    simpa only [hxarg, hyarg] using htaylor
  have hsumMul := dvd_mul_of_dvd_right hsum (b : ℤ)
  have hdiff := dvd_sub hsumMul hlinear_mul
  convert hdiff using 1
  ring

/-- Exact nonunit osculation cancellation at one owner. -/
theorem osculation_reducedOwnerSquare_dvd_evaluation
    {r : ℕ} (coeff : OsculationMonomial r → ℤ)
    (P b : ℕ) (A n d j rho : ℤ)
    (hP : 0 < P)
    (hvalue : osculationEvaluate coeff j rho = 0)
    (hdirection : (b : ℤ) * osculationEvaluateDX coeff j rho +
      A * osculationEvaluateDY coeff j rho = 0)
    (hn : (P : ℤ) ∣ n + j) (hd : (P : ℤ) ∣ d + rho)
    (hsquare : ((P : ℤ) ^ 2) ∣
      (b : ℤ) * (d + rho) - A * (n + j)) :
    ((reducedOwnerSquare P b : ℕ) : ℤ) ∣
      osculationEvaluate coeff (-n) (-d) := by
  apply reducedOwnerSquare_dvd_of_square_dvd_coefficient_mul hP
  exact osculation_owner_square_dvd_coefficient_mul_evaluation
    coeff P b A n d j rho hvalue hdirection hn hd hsquare

/-- Full-support nonunit osculation theorem.  All owner squares divide one
bounded polynomial evaluation at the cost of only one common coefficient
bound `L`. -/
theorem osculation_full_ownerSquare_product_dvd_commonBound_mul_evaluation
    {ι : Type*} {r : ℕ}
    (S : Finset ι) (coeff : OsculationMonomial r → ℤ)
    (P b : ι → ℕ) (A j rho : ι → ℤ)
    (n d : ℤ) (L : ℕ)
    (hP : ∀ e ∈ S, 0 < P e)
    (hpair : (S : Set ι).Pairwise (Function.onFun Nat.Coprime P))
    (hb : ∀ e ∈ S, b e ∣ L)
    (hvalue : ∀ e ∈ S,
      osculationEvaluate coeff (j e) (rho e) = 0)
    (hdirection : ∀ e ∈ S,
      (b e : ℤ) * osculationEvaluateDX coeff (j e) (rho e) +
        A e * osculationEvaluateDY coeff (j e) (rho e) = 0)
    (hn : ∀ e ∈ S, (P e : ℤ) ∣ n + j e)
    (hd : ∀ e ∈ S, (P e : ℤ) ∣ d + rho e)
    (hsquare : ∀ e ∈ S,
      ((P e : ℤ) ^ 2) ∣
        (b e : ℤ) * (d + rho e) - A e * (n + j e)) :
    ((((∏ e ∈ S, P e) ^ 2 : ℕ) : ℤ)) ∣
      (L : ℤ) * osculationEvaluate coeff (-n) (-d) := by
  apply full_ownerSquare_product_dvd_commonBound_mul_commonValue
    S P b L (osculationEvaluate coeff (-n) (-d)) hpair hb
  intro e he
  exact osculation_reducedOwnerSquare_dvd_evaluation
    coeff (P e) (b e) (A e) n d (j e) (rho e)
    (hP e he) (hvalue e he) (hdirection e he)
    (hn e he) (hd e he) (hsquare e he)

/-- All-prime canonical-grid specialization of the common-evaluation theorem.
This is the exact bridge from full canonical mass to one bounded-osculation
polynomial; no row-diagonal matching projection is used. -/
theorem canonical_allCells_square_dvd_cleaningLossSq_commonBound_mul_osculationEvaluation
    {k n d t r : ℕ} (data : CanonicalOwnerData k n d t)
    (coeff : OsculationMonomial r → ℤ)
    (b : ℕ × ℕ → ℕ) (A j rho : ℕ × ℕ → ℤ)
    (x y : ℤ) (L : ℕ)
    (hb : ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
      b cell ∣ L)
    (hvalue : ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
      osculationEvaluate coeff (j cell) (rho cell) = 0)
    (hdirection :
      ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
        (b cell : ℤ) * osculationEvaluateDX coeff (j cell) (rho cell) +
          A cell * osculationEvaluateDY coeff (j cell) (rho cell) = 0)
    (hx : ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
      (canonicalOwnerCell data cell.1 cell.2 : ℤ) ∣ x + j cell)
    (hy : ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
      (canonicalOwnerCell data cell.1 cell.2 : ℤ) ∣ y + rho cell)
    (hsquare :
      ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
        (canonicalOwnerCell data cell.1 cell.2 : ℤ) ^ 2 ∣
          (b cell : ℤ) * (y + rho cell) - A cell * (x + j cell)) :
    (((blockProduct k n) ^ 2 : ℕ) : ℤ) ∣
      (((canonicalOwnerResidual data) ^ 2 * L : ℕ) : ℤ) *
        osculationEvaluate coeff (-x) (-y) := by
  classical
  let grid := (Finset.Icc 1 k).product (Finset.Icc 1 k)
  let P : ℕ × ℕ → ℕ :=
    fun cell => canonicalOwnerCell data cell.1 cell.2
  have hpair : (grid : Set (ℕ × ℕ)).Pairwise
      (Function.onFun Nat.Coprime P) := by
    intro u hu v hv huv
    exact canonicalOwnerCells_pairwise_coprime data huv
  have hP : ∀ cell ∈ grid, 0 < P cell := by
    intro cell hcell
    dsimp [P]
    unfold canonicalOwnerCell
    apply Finset.prod_pos
    intro p hp
    split
    · exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
    · norm_num
  have hosc :=
    osculation_full_ownerSquare_product_dvd_commonBound_mul_evaluation
      grid coeff P b A j rho x y L hP hpair
      (by simpa [grid] using hb)
      (by simpa [grid] using hvalue)
      (by simpa [grid] using hdirection)
      (by simpa [grid, P] using hx)
      (by simpa [grid, P] using hy)
      (by simpa [grid, P] using hsquare)
  have hownerProduct :
      ∏ cell ∈ grid, P cell =
        ∏ row ∈ Finset.Icc 1 k,
          ∏ column ∈ Finset.Icc 1 k,
            canonicalOwnerCell data row column := by
    dsimp [grid, P]
    exact Finset.prod_product' _ _
      (fun row column => canonicalOwnerCell data row column)
  rw [hownerProduct] at hosc
  have hblock := canonicalOwnerResidual_mul_allCells data
  have hblockZ :
      (canonicalOwnerResidual data : ℤ) *
          (∏ row ∈ Finset.Icc 1 k,
            ∏ column ∈ Finset.Icc 1 k,
              (canonicalOwnerCell data row column : ℤ)) =
        (blockProduct k n : ℤ) := by
    exact_mod_cast hblock
  have hscaled := mul_dvd_mul
    (dvd_refl (((canonicalOwnerResidual data) ^ 2 : ℕ) : ℤ)) hosc
  convert hscaled using 1 <;>
    simp only [Nat.cast_mul, Nat.cast_pow]
  · push_cast
    rw [← hblockZ]
    ring
  · ring

/-- Factorial-cube form of the full canonical osculation bridge. -/
theorem canonical_allCells_square_dvd_factorialCube_mul_osculationEvaluation
    {k n d t r : ℕ} (data : CanonicalOwnerData k n d t)
    (coeff : OsculationMonomial r → ℤ)
    (b : ℕ × ℕ → ℕ) (A j rho : ℕ × ℕ → ℤ)
    (x y : ℤ)
    (hb : ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
      b cell ∣ (k - 1).factorial)
    (hvalue : ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
      osculationEvaluate coeff (j cell) (rho cell) = 0)
    (hdirection :
      ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
        (b cell : ℤ) * osculationEvaluateDX coeff (j cell) (rho cell) +
          A cell * osculationEvaluateDY coeff (j cell) (rho cell) = 0)
    (hx : ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
      (canonicalOwnerCell data cell.1 cell.2 : ℤ) ∣ x + j cell)
    (hy : ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
      (canonicalOwnerCell data cell.1 cell.2 : ℤ) ∣ y + rho cell)
    (hsquare :
      ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
        (canonicalOwnerCell data cell.1 cell.2 : ℤ) ^ 2 ∣
          (b cell : ℤ) * (y + rho cell) - A cell * (x + j cell)) :
    (((blockProduct k n) ^ 2 : ℕ) : ℤ) ∣
      (((k - 1).factorial ^ 3 : ℕ) : ℤ) *
        osculationEvaluate coeff (-x) (-y) := by
  have hexact :=
    canonical_allCells_square_dvd_cleaningLossSq_commonBound_mul_osculationEvaluation
      data coeff b A j rho x y (k - 1).factorial
      hb hvalue hdirection hx hy hsquare
  obtain ⟨u, hu⟩ := canonicalOwnerResidual_dvd_factorial data
  have hcoefNat :
      canonicalOwnerResidual data ^ 2 * (k - 1).factorial ∣
        (k - 1).factorial ^ 3 := by
    refine ⟨u ^ 2, ?_⟩
    rw [hu]
    ring
  have hcoefZ :
      (((canonicalOwnerResidual data ^ 2 * (k - 1).factorial : ℕ) : ℤ)) ∣
        (((k - 1).factorial ^ 3 : ℕ) : ℤ) := by
    exact_mod_cast hcoefNat
  obtain ⟨c, hc⟩ := hcoefZ
  apply dvd_trans hexact
  refine ⟨c, ?_⟩
  rw [hc]
  ring

/-- Normalized-form specialization of the exact nonunit cancellation. -/
theorem owner_square_reduced_normalized_dvd
    {P q : ℕ} {a b sign delta x : ℤ}
    (hP : 0 < P)
    (hfactorial : ((P : ℤ) ^ 2) ∣
      factorialMatchingForm (q : ℤ) a b sign delta x) :
    ((reducedOwnerSquare P q : ℕ) : ℤ) ∣
      normalizedMatchingForm a b sign delta x := by
  rw [factorialMatchingForm_eq_prefactor_mul_normalized] at hfactorial
  exact reducedOwnerSquare_dvd_of_square_dvd_coefficient_mul hP hfactorial

private theorem fullMass_neg_one_pow_add_eq_pred_mul_pred
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    (-1 : ℤ) ^ (i + j) =
      (-1 : ℤ) ^ (i - 1) * (-1 : ℤ) ^ (j - 1) := by
  have hexp : i + j = (i - 1) + (j - 1) + 2 := by omega
  rw [hexp, pow_add, pow_add]
  norm_num

/-- Equation-facing local theorem with no large-prime-support hypothesis.
The common factorial prefactor is exposed, and the exact reduced owner
square divides the same normalized matching form as in the high-prime
theorem. -/
theorem exists_matched_owner_reduced_normalized_square_dvd
    {k n d i j P : ℕ}
    (hP : 0 < P)
    (hd : k ≤ d)
    (hi : i ∈ Finset.Icc 1 k)
    (hj : j ∈ Finset.Icc 1 k)
    (hlower : P ∣ n + j)
    (hupper : P ∣ n + d + i)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ∃ q : ℕ,
      q ∣ (k - 1).factorial ∧
      ((reducedOwnerSquare P q : ℕ) : ℤ) ∣
        normalizedMatchingForm
          (reducedMatchingLeft k i j : ℤ)
          (reducedMatchingRight k i j : ℤ)
          ((-1 : ℤ) ^ (i + j))
          ((d + i - j : ℕ) : ℤ)
          ((n + j : ℕ) : ℤ) := by
  obtain ⟨q, hq, hFi, hFj⟩ :=
    exists_matchingCommonPrefactor hi hj
  have hraw := matched_owner_local_coefficients_dvd_sq
    hj hi hlower hupper heq
  rw [localBlockCoefficient_eq_sign_mul_nat hi,
    localBlockCoefficient_eq_sign_mul_nat hj] at hraw
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hsign := fullMass_neg_one_pow_add_eq_pred_mul_pred hi1 hj1
  have hweighted :
      ((P : ℤ) ^ 2) ∣
        (localBlockCoefficientNat k i : ℤ) *
            ((n + d + i : ℕ) : ℤ) -
          4 * ((-1 : ℤ) ^ (i + j)) *
            (localBlockCoefficientNat k j : ℤ) *
              ((n + j : ℕ) : ℤ) := by
    rcases neg_one_pow_eq_or ℤ (i - 1) with hisign | hisign
    · simpa [hisign, hsign, mul_assoc, mul_comm, mul_left_comm] using hraw
    · have hneg := dvd_neg.mpr hraw
      rw [hisign] at hneg
      convert hneg using 1
      rw [hsign, hisign]
      ring
  have hdiff :
      ((n + j : ℕ) : ℤ) + ((d + i - j : ℕ) : ℤ) =
        ((n + d + i : ℕ) : ℤ) := by
    have hjle : j ≤ d + i := by
      have hjk := (Finset.mem_Icc.mp hj).2
      have hi1' := (Finset.mem_Icc.mp hi).1
      omega
    exact_mod_cast (by omega :
      n + j + (d + i - j) = n + d + i)
  have hfactorial :
      ((P : ℤ) ^ 2) ∣
        factorialMatchingForm
          (q : ℤ)
          (reducedMatchingLeft k i j : ℤ)
          (reducedMatchingRight k i j : ℤ)
          ((-1 : ℤ) ^ (i + j))
          ((d + i - j : ℕ) : ℤ)
          ((n + j : ℕ) : ℤ) := by
    have hFiZ :
        (localBlockCoefficientNat k i : ℤ) =
          (q : ℤ) * (reducedMatchingRight k i j : ℤ) := by
      exact_mod_cast hFi
    have hFjZ :
        (localBlockCoefficientNat k j : ℤ) =
          (q : ℤ) * (reducedMatchingLeft k i j : ℤ) := by
      exact_mod_cast hFj
    unfold factorialMatchingForm
    rw [← hFiZ, ← hFjZ]
    convert hweighted using 1
    rw [← hdiff]
    ring
  exact ⟨q, hq, owner_square_reduced_normalized_dvd hP hfactorial⟩

/-- Every all-prime canonical cell is positive; unit cells are retained
literally rather than projected away. -/
theorem canonicalOwnerCell_pos_fullMass
    {k n d t j i : ℕ} (data : CanonicalOwnerData k n d t) :
    0 < canonicalOwnerCell data j i := by
  classical
  unfold canonicalOwnerCell
  apply Finset.prod_pos
  intro p hp
  split
  · exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · norm_num

/-- Actual all-prime canonical-grid specialization.  The full retained owner
mass is used, including every small-prime cell and every unit cell.  The only
normalization loss is one `(k-1)!`; the pre-existing canonical cleaning loss
appears squared because the complete block is `G * ownerProduct`.

In particular, this replaces the former `n^(2*pi(k))` projection loss by the
fixed coefficient `(canonicalOwnerResidual data)^2 * (k-1)!`. -/
theorem canonical_allCells_square_dvd_cleaningLossSq_factorial_mul_normalizedProduct
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (q : ℕ × ℕ → ℕ) (F : ℕ × ℕ → ℤ)
    (hq : ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
      q cell ∣ (k - 1).factorial)
    (hweighted :
      ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
        (((canonicalOwnerCell data cell.1 cell.2) ^ 2 : ℕ) : ℤ) ∣
          (q cell : ℤ) * F cell) :
    (((blockProduct k n) ^ 2 : ℕ) : ℤ) ∣
      (((canonicalOwnerResidual data) ^ 2 * (k - 1).factorial : ℕ) : ℤ) *
        ∏ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k), F cell := by
  classical
  let grid := (Finset.Icc 1 k).product (Finset.Icc 1 k)
  let P : ℕ × ℕ → ℕ :=
    fun cell => canonicalOwnerCell data cell.1 cell.2
  have hpair : (grid : Set (ℕ × ℕ)).Pairwise
      (Function.onFun Nat.Coprime P) := by
    intro x hx y hy hxy
    exact canonicalOwnerCells_pairwise_coprime data hxy
  have hP : ∀ cell ∈ grid, 0 < P cell := by
    intro cell hcell
    exact canonicalOwnerCell_pos_fullMass data
  have hfull :=
    full_ownerSquare_product_dvd_commonBound_mul_normalizedProduct
      grid P q F (k - 1).factorial hP hpair
      (by simpa [grid] using hq)
      (by simpa [grid, P] using hweighted)
  have hownerProduct :
      ∏ cell ∈ grid, P cell =
        ∏ j ∈ Finset.Icc 1 k,
          ∏ i ∈ Finset.Icc 1 k, canonicalOwnerCell data j i := by
    dsimp [grid, P]
    exact Finset.prod_product' _ _
      (fun j i => canonicalOwnerCell data j i)
  have hblock := canonicalOwnerResidual_mul_allCells data
  have hscaled := mul_dvd_mul
    (dvd_refl (((canonicalOwnerResidual data) ^ 2 : ℕ) : ℤ)) hfull
  rw [hownerProduct] at hscaled
  have hblockZ :
      (canonicalOwnerResidual data : ℤ) *
          (∏ j ∈ Finset.Icc 1 k,
            ∏ i ∈ Finset.Icc 1 k,
              (canonicalOwnerCell data j i : ℤ)) =
        (blockProduct k n : ℤ) := by
    exact_mod_cast hblock
  convert hscaled using 1 <;>
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_factorial]
  · push_cast
    rw [← hblockZ]
    ring
  · ring

/-- Coarser coefficient-only form of the preceding theorem.  Since the
canonical cleaning loss divides `(k-1)!`, the complete lower-block square
costs at most the fixed cube `((k-1)!)^3`, with no power of `n+k`. -/
theorem canonical_allCells_square_dvd_factorialCube_mul_normalizedProduct
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (q : ℕ × ℕ → ℕ) (F : ℕ × ℕ → ℤ)
    (hq : ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
      q cell ∣ (k - 1).factorial)
    (hweighted :
      ∀ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
        (((canonicalOwnerCell data cell.1 cell.2) ^ 2 : ℕ) : ℤ) ∣
          (q cell : ℤ) * F cell) :
    (((blockProduct k n) ^ 2 : ℕ) : ℤ) ∣
      (((k - 1).factorial ^ 3 : ℕ) : ℤ) *
        ∏ cell ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k), F cell := by
  have hexact :=
    canonical_allCells_square_dvd_cleaningLossSq_factorial_mul_normalizedProduct
      data q F hq hweighted
  obtain ⟨u, hu⟩ := canonicalOwnerResidual_dvd_factorial data
  have hcoefNat :
      canonicalOwnerResidual data ^ 2 * (k - 1).factorial ∣
        (k - 1).factorial ^ 3 := by
    refine ⟨u ^ 2, ?_⟩
    rw [hu]
    ring
  have hcoefZ :
      (((canonicalOwnerResidual data ^ 2 * (k - 1).factorial : ℕ) : ℤ)) ∣
        (((k - 1).factorial ^ 3 : ℕ) : ℤ) := by
    exact_mod_cast hcoefNat
  obtain ⟨c, hc⟩ := hcoefZ
  apply dvd_trans hexact
  refine ⟨c, ?_⟩
  rw [hc]
  ring

#print axioms reducedOwnerSquare_dvd_of_square_dvd_coefficient_mul
#print axioms ownerNormalizationLoss_product_dvd_common_bound
#print axioms ownerSquareProduct_eq_loss_mul_reduced
#print axioms full_ownerSquare_product_dvd_commonBound_mul_normalizedProduct
#print axioms reducedOwnerSquare_dvd_square
#print axioms full_ownerSquare_product_dvd_commonBound_mul_commonValue
#print axioms osculation_owner_square_dvd_coefficient_mul_evaluation
#print axioms osculation_reducedOwnerSquare_dvd_evaluation
#print axioms osculation_full_ownerSquare_product_dvd_commonBound_mul_evaluation
#print axioms canonical_allCells_square_dvd_cleaningLossSq_commonBound_mul_osculationEvaluation
#print axioms canonical_allCells_square_dvd_factorialCube_mul_osculationEvaluation
#print axioms owner_square_reduced_normalized_dvd
#print axioms exists_matched_owner_reduced_normalized_square_dvd
#print axioms canonical_allCells_square_dvd_cleaningLossSq_factorial_mul_normalizedProduct
#print axioms canonical_allCells_square_dvd_factorialCube_mul_normalizedProduct

end Erdos686Variant
end Erdos686
