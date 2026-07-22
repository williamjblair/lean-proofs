/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.LowDegreeOsculation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Erdős 686: bounded integer kernel vectors from a finite cube

This file banks the finite-cube part of the corrected osculation-kernel
argument.  For an integer matrix whose row `ℓ¹` norm is at most `L`, it
constructs an exact finite encoding of the image of the cube
`{0, ..., D}^N` into `(D*L+1)^q` boxes.  Pigeonhole then supplies a nonzero
integer kernel vector with coordinatewise absolute value at most `D`.

-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

section CubeEncoding

variable {q N : ℕ}

/-- A finite part of a coordinate cube has cardinality at most
`(D+1)^t` whenever restriction to `t` selected coordinates is injective.
This is the combinatorial end of the affine-subspace cube-intersection
lemma needed for the eventual independent-family extraction. -/
theorem cube_subset_card_le_of_restrict_injective
    (D : ℕ) (E : Finset (Fin N → Fin (D + 1)))
    (S : Finset (Fin N))
    (hinj : Set.InjOn
      (fun x : Fin N → Fin (D + 1) =>
        fun i : {i // i ∈ S} => x i.val)
      (E : Set (Fin N → Fin (D + 1)))) :
    E.card ≤ (D + 1) ^ S.card := by
  let f : {x // x ∈ E} → ({i // i ∈ S} → Fin (D + 1)) :=
    fun x i => x.val i.val
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply hinj x.property y.property
    simpa [f] using hxy
  have hcard := Fintype.card_le_of_injective f hf
  simpa using hcard

/-- Affine-subspace form of the preceding cardinal bound.  If every pairwise
difference of cube points belongs to `W`, and `t` selected coordinates detect
vectors of `W`, then the affine fiber has at most `(D+1)^t` points. -/
theorem affine_cube_subset_card_le_of_subspace_restrict_injective
    (D : ℕ) (E : Finset (Fin N → Fin (D + 1)))
    (W : Submodule ℚ (Fin N → ℚ)) (S : Finset (Fin N))
    (hdiff : ∀ x ∈ E, ∀ y ∈ E,
      (fun j => (x j : ℚ) - (y j : ℚ)) ∈ W)
    (hW : Function.Injective
      (fun w : W => fun i : {i // i ∈ S} => w.val i.val)) :
    E.card ≤ (D + 1) ^ S.card := by
  apply cube_subset_card_le_of_restrict_injective D E S
  intro x hx y hy hxy
  let w : W :=
    ⟨fun j => (x j : ℚ) - (y j : ℚ), hdiff x hx y hy⟩
  have hw0 : w = 0 := by
    apply hW
    funext i
    have hi := congrFun hxy i
    have hiQ : (x i.val : ℚ) = (y i.val : ℚ) :=
      congrArg (fun z : Fin (D + 1) => (z : ℚ)) hi
    simp [w, hiQ]
  funext j
  apply Fin.ext
  have hj := congrFun (congrArg Subtype.val hw0) j
  simp only [w] at hj
  exact_mod_cast sub_eq_zero.mp hj

private theorem exists_coordinate_finset_restrict_injective_le_aux (t : ℕ) :
    ∀ W : Submodule ℚ (Fin N → ℚ), Module.finrank ℚ W = t →
      ∃ S : Finset (Fin N),
        S.card ≤ t ∧
        Function.Injective
          (fun w : W => fun i : {i // i ∈ S} => w.val i.val) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro W ht
      by_cases ht0 : t = 0
      · refine ⟨∅, by simp [ht0], ?_⟩
        have hW0 : Module.finrank ℚ W = 0 := ht.trans ht0
        have hsub : Subsingleton W := Module.finrank_zero_iff.mp hW0
        exact fun x y _ => hsub.elim x y
      · have hnsub : ¬ Subsingleton W := by
          intro hs
          have hz : Module.finrank ℚ W = 0 :=
            Module.finrank_zero_iff.mpr hs
          omega
        letI : Nontrivial W := not_subsingleton_iff_nontrivial.mp hnsub
        obtain ⟨w, hw⟩ := exists_ne (0 : W)
        have hwi : ∃ i : Fin N, w.val i ≠ 0 := by
          by_contra hall
          push Not at hall
          apply hw
          apply Subtype.ext
          funext i
          exact hall i
        obtain ⟨i, hi⟩ := hwi
        let g : (Fin N → ℚ) →ₗ[ℚ] ℚ := LinearMap.proj i
        let K : Submodule ℚ (Fin N → ℚ) := W ⊓ g.ker
        have hKW : K < W := by
          change W ⊓ g.ker < W
          rw [inf_lt_left]
          intro hle
          have hwker : w.val ∈ g.ker := hle w.property
          exact hi (by simpa [g] using hwker)
        have hklt : Module.finrank ℚ K < t := by
          rw [← ht]
          exact Submodule.finrank_lt_finrank_of_lt hKW
        obtain ⟨S, hScard, hSinj⟩ :=
          ih (Module.finrank ℚ K) hklt K rfl
        refine ⟨insert i S, ?_, ?_⟩
        · calc
            (insert i S).card ≤ S.card + 1 := Finset.card_insert_le i S
            _ ≤ Module.finrank ℚ K + 1 := Nat.add_le_add_right hScard 1
            _ ≤ t := by omega
        · show Function.Injective
            (fun w : W => fun a : {a // a ∈ insert i S} => w.val a.val)
          intro x y hxy
          have hpoint : ∀ a, a ∈ insert i S → x.val a = y.val a := by
            intro a ha
            exact congrFun hxy ⟨a, ha⟩
          have hgi : g (x.val - y.val) = 0 := by
            have hiEq := hpoint i (Finset.mem_insert_self i S)
            simpa [g, sub_eq_zero] using hiEq
          have hdiffW : x.val - y.val ∈ W := W.sub_mem x.property y.property
          let z : K := ⟨x.val - y.val, by
            exact ⟨hdiffW, hgi⟩⟩
          have hz : z = 0 := by
            apply hSinj
            funext a
            have haEq := hpoint a.val (Finset.mem_insert_of_mem a.property)
            simp only [z]
            exact sub_eq_zero.mpr haEq
          apply Subtype.ext
          exact sub_eq_zero.mp (congrArg Subtype.val hz)

/-- Every rational subspace of a coordinate space has a set of exactly
`finrank W` pivot coordinates on which restriction is injective. -/
theorem exists_coordinate_finset_restrict_injective
    (W : Submodule ℚ (Fin N → ℚ)) :
    ∃ S : Finset (Fin N),
      S.card = Module.finrank ℚ W ∧
      Function.Injective
        (fun w : W => fun i : {i // i ∈ S} => w.val i.val) := by
  obtain ⟨S, hScard, hSinj⟩ :=
    exists_coordinate_finset_restrict_injective_le_aux
      (N := N) (Module.finrank ℚ W) W rfl
  have hdim : Module.finrank ℚ W ≤ N := by
    simpa [Module.finrank_fin_fun] using Submodule.finrank_le W
  obtain ⟨T, hST, hTcard⟩ :=
    Finset.exists_superset_card_eq hScard (by simpa using hdim)
  refine ⟨T, hTcard, ?_⟩
  intro x y hxy
  apply hSinj
  funext i
  exact congrFun hxy ⟨i.val, hST i.property⟩

/-- Sharp affine-subspace intersection bound for the coordinate cube. -/
theorem affine_cube_subset_card_le_finrank
    (D : ℕ) (E : Finset (Fin N → Fin (D + 1)))
    (W : Submodule ℚ (Fin N → ℚ))
    (hdiff : ∀ x ∈ E, ∀ y ∈ E,
      (fun j => (x j : ℚ) - (y j : ℚ)) ∈ W) :
    E.card ≤ (D + 1) ^ Module.finrank ℚ W := by
  obtain ⟨S, hScard, hSinj⟩ :=
    exists_coordinate_finset_restrict_injective W
  simpa [hScard] using
    affine_cube_subset_card_le_of_subspace_restrict_injective
      D E W S hdiff hSinj

/-- The negative coefficient mass in one row. -/
def rowNegativeMass (A : Matrix (Fin q) (Fin N) ℤ) (i : Fin q) : ℕ :=
  ∑ j, if A i j < 0 then (A i j).natAbs else 0

/-- A row dot product translated by `D` times its negative coefficient mass.
Every summand then lies in the interval from zero to `D * |A i j|`. -/
def adjustedCubeRow (A : Matrix (Fin q) (Fin N) ℤ) (D : ℕ)
    (i : Fin q) (x : Fin N → Fin (D + 1)) : ℤ :=
  ∑ j, (A i j) * (x j : ℤ) +
    (D : ℤ) * (rowNegativeMass A i : ℤ)

private theorem adjusted_term_nonneg (a : ℤ) {D t : ℕ} (ht : t ≤ D) :
    0 ≤ a * (t : ℤ) +
      (D : ℤ) * (if a < 0 then a.natAbs else 0 : ℕ) := by
  by_cases ha : a < 0
  · simp only [ha, if_true, Int.natCast_natAbs]
    rw [abs_of_neg ha]
    have ht' : (t : ℤ) ≤ D := by exact_mod_cast ht
    nlinarith
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    simp only [ha, if_false, Nat.cast_zero, mul_zero, add_zero]
    positivity

private theorem adjusted_term_le (a : ℤ) {D t : ℕ} (ht : t ≤ D) :
    a * (t : ℤ) +
        (D : ℤ) * (if a < 0 then a.natAbs else 0 : ℕ) ≤
      (D : ℤ) * (a.natAbs : ℤ) := by
  by_cases ha : a < 0
  · simp only [ha, if_true, Int.natCast_natAbs]
    rw [abs_of_neg ha]
    have ht0 : (0 : ℤ) ≤ t := by positivity
    nlinarith
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    simp only [ha, if_false, Nat.cast_zero, mul_zero, add_zero]
    rw [Int.natAbs_of_nonneg ha0]
    have ht' : (t : ℤ) ≤ D := by exact_mod_cast ht
    simpa [mul_comm] using mul_le_mul_of_nonneg_left ht' ha0

theorem adjustedCubeRow_nonneg
    (A : Matrix (Fin q) (Fin N) ℤ) (D : ℕ)
    (i : Fin q) (x : Fin N → Fin (D + 1)) :
    0 ≤ adjustedCubeRow A D i x := by
  rw [adjustedCubeRow, rowNegativeMass, Nat.cast_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_nonneg fun j _ =>
    adjusted_term_nonneg (A i j) (Nat.le_of_lt_succ (x j).isLt)

theorem adjustedCubeRow_le
    (A : Matrix (Fin q) (Fin N) ℤ) (D L : ℕ)
    (hrow : ∀ i, ∑ j, (A i j).natAbs ≤ L)
    (i : Fin q) (x : Fin N → Fin (D + 1)) :
    adjustedCubeRow A D i x ≤ (D * L : ℕ) := by
  rw [adjustedCubeRow, rowNegativeMass, Nat.cast_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    ∑ j, (A i j * (x j : ℤ) +
          (D : ℤ) * ↑(if A i j < 0 then (A i j).natAbs else 0)) ≤
        ∑ j, (D : ℤ) * ((A i j).natAbs : ℤ) :=
      Finset.sum_le_sum fun j _ =>
        adjusted_term_le (A i j) (Nat.le_of_lt_succ (x j).isLt)
    _ = (D : ℤ) * (∑ j, (A i j).natAbs : ℕ) := by
      rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ (D : ℤ) * L := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hrow i) (by positivity)
    _ = (D * L : ℕ) := by norm_num

/-- The exact finite encoding of all row values of the nonnegative cube. -/
def cubeImageCode (A : Matrix (Fin q) (Fin N) ℤ) (D L : ℕ)
    (hrow : ∀ i, ∑ j, (A i j).natAbs ≤ L)
    (x : Fin N → Fin (D + 1)) : Fin q → Fin (D * L + 1) :=
  fun i => ⟨(adjustedCubeRow A D i x).toNat, by
    have h0 := adjustedCubeRow_nonneg A D i x
    have hle := adjustedCubeRow_le A D L hrow i x
    have hcast : (adjustedCubeRow A D i x).toNat ≤ D * L :=
      Int.toNat_le.mpr hle
    omega⟩

theorem cubeImageCode_eq_iff_mulVec_eq
    (A : Matrix (Fin q) (Fin N) ℤ) (D L : ℕ)
    (hrow : ∀ i, ∑ j, (A i j).natAbs ≤ L)
    (x y : Fin N → Fin (D + 1)) :
    cubeImageCode A D L hrow x = cubeImageCode A D L hrow y ↔
      A.mulVec (fun j => (x j : ℤ)) =
        A.mulVec (fun j => (y j : ℤ)) := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    have hx0 := adjustedCubeRow_nonneg A D i x
    have hy0 := adjustedCubeRow_nonneg A D i y
    have hto : (adjustedCubeRow A D i x).toNat =
        (adjustedCubeRow A D i y).toNat := congrArg Fin.val hi
    have hadj : adjustedCubeRow A D i x = adjustedCubeRow A D i y := by
      calc
        adjustedCubeRow A D i x =
            ((adjustedCubeRow A D i x).toNat : ℤ) :=
          (Int.toNat_of_nonneg hx0).symm
        _ = ((adjustedCubeRow A D i y).toNat : ℤ) := by rw [hto]
        _ = adjustedCubeRow A D i y := Int.toNat_of_nonneg hy0
    simpa [adjustedCubeRow, Matrix.mulVec, dotProduct] using hadj
  · intro h
    funext i
    apply Fin.ext
    have hi := congrFun h i
    have hadj : adjustedCubeRow A D i x = adjustedCubeRow A D i y := by
      simpa [adjustedCubeRow, Matrix.mulVec, dotProduct] using
        congrArg (fun z => z + (D : ℤ) * (rowNegativeMass A i : ℤ)) hi
    exact congrArg Int.toNat hadj

/-- Finite-cube collision: a strict domain/codomain cardinal inequality gives
a nonzero bounded integer vector in the kernel. -/
theorem exists_nonzero_bounded_integer_kernel_vector_of_card_lt
    (A : Matrix (Fin q) (Fin N) ℤ) (D L : ℕ)
    (hrow : ∀ i, ∑ j, (A i j).natAbs ≤ L)
    (hcard : (D * L + 1) ^ q < (D + 1) ^ N) :
    ∃ z : Fin N → ℤ,
      z ≠ 0 ∧
      A.mulVec z = 0 ∧
      ∀ j, (z j).natAbs ≤ D := by
  let f := cubeImageCode A D L hrow
  have hdomain : Fintype.card (Fin N → Fin (D + 1)) = (D + 1) ^ N := by
    simp
  have hcodomain : Fintype.card (Fin q → Fin (D * L + 1)) =
      (D * L + 1) ^ q := by
    simp
  have hlt : Fintype.card (Fin q → Fin (D * L + 1)) <
      Fintype.card (Fin N → Fin (D + 1)) := by
    simpa [hdomain, hcodomain] using hcard
  obtain ⟨x, y, hxy, hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  refine ⟨fun j => (x j : ℤ) - (y j : ℤ), ?_, ?_, ?_⟩
  · intro hz
    apply hxy
    funext j
    apply Fin.ext
    have hj := congrFun hz j
    exact_mod_cast (sub_eq_zero.mp hj)
  · have hmul := (cubeImageCode_eq_iff_mulVec_eq A D L hrow x y).mp hfxy
    funext i
    have hi := congrFun hmul i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simpa [sub_eq_zero] using hi
  · intro j
    exact Int.natAbs_coe_sub_coe_le_of_le
      (Nat.le_of_lt_succ (x j).isLt)
      (Nat.le_of_lt_succ (y j).isLt)

/-- The corrected square-radius hypothesis is sufficient for the finite-cube
collision as soon as the number of columns is strictly larger than twice the
number of rows.  This is the numerical core used with `q = 2m` and
`N ≥ 4m+1`. -/
theorem exists_nonzero_bounded_integer_kernel_vector
    (A : Matrix (Fin q) (Fin N) ℤ) (D L : ℕ)
    (hrow : ∀ i, ∑ j, (A i j).natAbs ≤ L)
    (hq : 0 < q)
    (hcolumns : 2 * q < N)
    (hradius : D * L + 1 < (D + 1) ^ 2) :
    ∃ z : Fin N → ℤ,
      z ≠ 0 ∧
      A.mulVec z = 0 ∧
      ∀ j, (z j).natAbs ≤ D := by
  apply exists_nonzero_bounded_integer_kernel_vector_of_card_lt
    A D L hrow
  have hbase : 1 < D + 1 := by
    by_contra h
    have hD : D = 0 := by omega
    subst D
    norm_num at hradius
  have hp := Nat.pow_lt_pow_left hradius (Nat.ne_of_gt hq)
  have he := Nat.pow_lt_pow_right hbase hcolumns
  calc
    (D * L + 1) ^ q < ((D + 1) ^ 2) ^ q := hp
    _ = (D + 1) ^ (2 * q) := by rw [pow_mul]
    _ < (D + 1) ^ N := he

private theorem exists_fiber_card_gt
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (C : ℕ)
    (hcard : Fintype.card β * C < Fintype.card α) :
    ∃ y, (Finset.univ.filter (fun x => f x = y)).card > C := by
  by_contra hn
  push Not at hn
  have hsigma :
      (∑ y : β, Fintype.card {x : α // f x = y}) = Fintype.card α := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  have hle : (∑ y : β, Fintype.card {x : α // f x = y}) ≤
      Fintype.card β * C := by
    calc
      _ ≤ ∑ _y : β, C := Finset.sum_le_sum (fun y _ => by
        simpa only [Fintype.card_subtype] using hn y)
      _ = Fintype.card β * C := by simp
  omega

/-- The complete corrected finite-cube extraction.  Under the square-radius
inequality and `N > 2q`, there are `N-2q+1` linearly independent rational
casts of bounded integer kernel vectors. -/
theorem exists_bounded_independent_integer_kernel_family
    (A : Matrix (Fin q) (Fin N) ℤ) (D L : ℕ)
    (hrow : ∀ i, ∑ j, (A i j).natAbs ≤ L)
    (hq : 0 < q)
    (hcolumns : 2 * q < N)
    (hradius : D * L + 1 < (D + 1) ^ 2) :
    ∃ z : Fin (N - 2 * q + 1) → Fin N → ℤ,
      LinearIndependent ℚ (fun i j => (z i j : ℚ)) ∧
      (∀ i, A.mulVec (z i) = 0) ∧
      ∀ i j, (z i j).natAbs ≤ D := by
  let cube := Fin N → Fin (D + 1)
  let code := Fin q → Fin (D * L + 1)
  let f : cube → code := cubeImageCode A D L hrow
  have hbase : 1 < D + 1 := by
    by_contra h
    have hD : D = 0 := by omega
    subst D
    norm_num at hradius
  have hqpow : (D * L + 1) ^ q < (D + 1) ^ (2 * q) := by
    have hp := Nat.pow_lt_pow_left hradius (Nat.ne_of_gt hq)
    simpa [pow_mul] using hp
  have htwopos : 0 < (D + 1) ^ (N - 2 * q) :=
    Nat.pow_pos (by omega)
  have hfiberCard :
      Fintype.card code * (D + 1) ^ (N - 2 * q) <
        Fintype.card cube := by
    simp only [cube, code, Fintype.card_fun, Fintype.card_fin]
    calc
      (D * L + 1) ^ q * (D + 1) ^ (N - 2 * q) <
          (D + 1) ^ (2 * q) * (D + 1) ^ (N - 2 * q) :=
        Nat.mul_lt_mul_of_pos_right hqpow htwopos
      _ = (D + 1) ^ N := by
        rw [← pow_add]
        congr 1
        omega
  obtain ⟨c, hc⟩ := exists_fiber_card_gt f
    ((D + 1) ^ (N - 2 * q)) hfiberCard
  let E : Finset cube := Finset.univ.filter (fun x => f x = c)
  let diffQ (x y : cube) : Fin N → ℚ :=
    fun j => (x j : ℚ) - (y j : ℚ)
  let G : Set (Fin N → ℚ) :=
    {v | ∃ x ∈ E, ∃ y ∈ E, v = diffQ x y}
  let W : Submodule ℚ (Fin N → ℚ) := Submodule.span ℚ G
  have hdiff : ∀ x ∈ E, ∀ y ∈ E, diffQ x y ∈ W := by
    intro x hx y hy
    exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
  have hEcard : (D + 1) ^ (N - 2 * q) < E.card := by
    simpa [E] using hc
  have hdim : N - 2 * q < Module.finrank ℚ W := by
    by_contra hnot
    have hleDim : Module.finrank ℚ W ≤ N - 2 * q := by omega
    have hcube := affine_cube_subset_card_le_finrank
      (N := N) D E W hdiff
    have hp : (D + 1) ^ Module.finrank ℚ W ≤
        (D + 1) ^ (N - 2 * q) :=
      pow_le_pow_right' (by omega) hleDim
    omega
  have hs : N - 2 * q + 1 ≤ Module.finrank ℚ W := by omega
  obtain ⟨b, hbmem, -, hbLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ G
  let e : Fin (N - 2 * q + 1) → Fin (Module.finrank ℚ W) :=
    Fin.castLE hs
  have heinj : Function.Injective e := Fin.castLE_injective hs
  have hchoose : ∀ i : Fin (N - 2 * q + 1),
      ∃ x ∈ E, ∃ y ∈ E, b (e i) = diffQ x y := by
    intro i
    simpa [G] using hbmem (e i)
  choose x hx y hy hxy using hchoose
  let z : Fin (N - 2 * q + 1) → Fin N → ℤ :=
    fun i j => (x i j : ℤ) - (y i j : ℤ)
  refine ⟨z, ?_, ?_, ?_⟩
  · have hcomp : (fun i j => (z i j : ℚ)) = b ∘ e := by
      funext i j
      have hij := congrFun (hxy i) j
      simpa [z, diffQ] using hij.symm
    rw [hcomp]
    exact hbLI.comp e heinj
  · intro i
    have hfx : f (x i) = c := (Finset.mem_filter.mp (hx i)).2
    have hfy : f (y i) = c := (Finset.mem_filter.mp (hy i)).2
    have himage := (cubeImageCode_eq_iff_mulVec_eq
      A D L hrow (x i) (y i)).mp (hfx.trans hfy.symm)
    funext row
    have hi := congrFun himage row
    simp only [z, Matrix.mulVec, dotProduct, Pi.zero_apply]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hi
  · intro i j
    exact Int.natAbs_coe_sub_coe_le_of_le
      (Nat.le_of_lt_succ (x i j).isLt)
      (Nat.le_of_lt_succ (y i j).isLt)

/-- Osculation specialization: a `2m × N` matrix with `N ≥ 4m+1` has
`N-4m+1` independent bounded integer kernel vectors. -/
theorem exists_bounded_independent_osculation_kernel_family
    {m : ℕ} (A : Matrix (Fin (2 * m)) (Fin N) ℤ) (D L : ℕ)
    (hrow : ∀ i, ∑ j, (A i j).natAbs ≤ L)
    (hm : 0 < m)
    (hcolumns : 4 * m + 1 ≤ N)
    (hradius : D * L + 1 < (D + 1) ^ 2) :
    ∃ z : Fin (N - 4 * m + 1) → Fin N → ℤ,
      LinearIndependent ℚ (fun i j => (z i j : ℚ)) ∧
      (∀ i, A.mulVec (z i) = 0) ∧
      ∀ i j, (z i j).natAbs ≤ D := by
  have hcols : 2 * (2 * m) < N := by omega
  have heq : N - 2 * (2 * m) + 1 = N - 4 * m + 1 := by omega
  rw [← heq]
  exact exists_bounded_independent_integer_kernel_family
    (q := 2 * m) A D L hrow (by omega) hcols hradius

/-- The conservative radius `D=4L` satisfies the exact square-radius
inequality whenever the row bound is positive. -/
theorem four_mul_rowBound_radius
    {L : ℕ} (hL : 0 < L) :
    (4 * L) * L + 1 < (4 * L + 1) ^ 2 := by
  nlinarith [sq_nonneg L]

/-- Entrywise envelope form of the corrected osculation-kernel theorem.
For `N` columns and entry bound `H`, the coefficient radius is exactly
`4*N*H`. -/
theorem exists_bounded_independent_osculation_kernel_family_of_entry_bound
    {m : ℕ} (A : Matrix (Fin (2 * m)) (Fin N) ℤ) (H : ℕ)
    (hentry : ∀ i j, (A i j).natAbs ≤ H)
    (hm : 0 < m)
    (hcolumns : 4 * m + 1 ≤ N)
    (hH : 0 < H) :
    ∃ z : Fin (N - 4 * m + 1) → Fin N → ℤ,
      LinearIndependent ℚ (fun i j => (z i j : ℚ)) ∧
      (∀ i, A.mulVec (z i) = 0) ∧
      ∀ i j, (z i j).natAbs ≤ 4 * N * H := by
  have hrow : ∀ i, ∑ j, (A i j).natAbs ≤ N * H := by
    intro i
    calc
      ∑ j, (A i j).natAbs ≤ ∑ _j : Fin N, H :=
        Finset.sum_le_sum fun j _ => hentry i j
      _ = N * H := by simp
  have hNH : 0 < N * H := Nat.mul_pos (by omega) hH
  obtain ⟨z, hli, hker, hbound⟩ :=
    exists_bounded_independent_osculation_kernel_family
      A (4 * (N * H)) (N * H) hrow hm hcolumns
        (four_mul_rowBound_radius hNH)
  refine ⟨z, hli, hker, ?_⟩
  intro i j
  simpa [mul_assoc] using hbound i j

/-- The exact coefficient envelope advertised for the low-degree package. -/
theorem exists_bounded_independent_osculation_kernel_family_advertised
    {m r k : ℕ} (A : Matrix (Fin (2 * m)) (Fin N) ℤ)
    (hentry : ∀ i j,
      (A i j).natAbs ≤ 3 * r * 2 ^ k * k ^ (r - 1))
    (hm : 0 < m)
    (hcolumns : 4 * m + 1 ≤ N)
    (hr : 0 < r) (hk : 0 < k) :
    ∃ z : Fin (N - 4 * m + 1) → Fin N → ℤ,
      LinearIndependent ℚ (fun i j => (z i j : ℚ)) ∧
      (∀ i, A.mulVec (z i) = 0) ∧
      ∀ i j,
        (z i j).natAbs ≤
          12 * N * r * 2 ^ k * k ^ (r - 1) := by
  have hH : 0 < 3 * r * 2 ^ k * k ^ (r - 1) := by positivity
  obtain ⟨z, hli, hker, hbound⟩ :=
    exists_bounded_independent_osculation_kernel_family_of_entry_bound
      A (3 * r * 2 ^ k * k ^ (r - 1)) hentry hm hcolumns hH
  refine ⟨z, hli, hker, ?_⟩
  intro i j
  convert hbound i j using 1
  ring

end CubeEncoding

#print axioms adjustedCubeRow_nonneg
#print axioms cube_subset_card_le_of_restrict_injective
#print axioms affine_cube_subset_card_le_of_subspace_restrict_injective
#print axioms exists_coordinate_finset_restrict_injective
#print axioms affine_cube_subset_card_le_finrank
#print axioms adjustedCubeRow_le
#print axioms cubeImageCode_eq_iff_mulVec_eq
#print axioms exists_nonzero_bounded_integer_kernel_vector_of_card_lt
#print axioms exists_nonzero_bounded_integer_kernel_vector
#print axioms exists_bounded_independent_integer_kernel_family
#print axioms exists_bounded_independent_osculation_kernel_family
#print axioms four_mul_rowBound_radius
#print axioms exists_bounded_independent_osculation_kernel_family_of_entry_bound
#print axioms exists_bounded_independent_osculation_kernel_family_advertised

end Erdos686Variant
end Erdos686
