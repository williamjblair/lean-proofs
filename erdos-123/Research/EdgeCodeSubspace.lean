import Research.EdgeCodeFinset
import Research.EdgeCodeRecurrence

namespace Erdos123

open Combinatorics

noncomputable section

/-- Mixed positional weight at one c-adic code coordinate. -/
def edgePositionWeight (a c n : ℕ) (i : Fin n) : ℕ :=
  c ^ (i : ℕ) * a ^ (n - 1 - (i : ℕ))

/-- Contribution of coordinates fixed by a combinatorial subspace. -/
def subspaceFixedEval {η n : ℕ} (a b c : ℕ)
    (l : Subspace (Fin η) (Fin c) (Fin n)) : ℕ :=
  ∑ i : Fin n, match l.idxFun i with
    | Sum.inl r => edgePositionWeight a c n i * edgeBaseDigit a b c r
    | Sum.inr _ => 0

/-- Sum of the positional weights controlled by one subspace parameter. -/
def subspaceParamWeight {η n : ℕ} (a c : ℕ)
    (l : Subspace (Fin η) (Fin c) (Fin n)) (e : Fin η) : ℕ :=
  ∑ i : Fin n, if l.idxFun i = Sum.inr e then edgePositionWeight a c n i else 0

/-- Evaluation on a combinatorial subspace separates into one fixed part and
one univariate digit contribution for each independent parameter. -/
theorem edgeCodeEval_subspace_decomposition {a b c η n : ℕ}
    (l : Subspace (Fin η) (Fin c) (Fin n)) (x : Fin η → Fin c) :
    edgeCodeEval a b c n (l x) =
      subspaceFixedEval a b c l +
        ∑ e : Fin η, subspaceParamWeight a c l e *
          edgeBaseDigit a b c (x e) := by
  classical
  rw [edgeCodeEval_stationary]
  unfold subspaceFixedEval subspaceParamWeight edgePositionWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  cases hi : l.idxFun i with
  | inl r =>
      simp [Subspace.coe_apply, hi]
  | inr e =>
      simp only [Subspace.coe_apply, hi, Sum.elim_inr, zero_add]
      rw [Finset.sum_eq_single e]
      · simp
      · intro e' _he' hne
        have hne' : e ≠ e' := Ne.symm hne
        simp [hne']
      · simp

private theorem subspace_apply_injective {η α ι : Type*} [Nontrivial α]
    (l : Subspace η α ι) : Function.Injective l := by
  intro x y hxy
  funext e
  rcases l.proper e with ⟨i, hi⟩
  have := congrFun hxy i
  simpa [Subspace.coe_apply, hi] using this

/-- Carry-coloring plus the multidimensional Hales--Jewett theorem produces
arbitrarily high-dimensional combinatorial subspaces of edge-code words whose
actual evaluations all have one common carry quotient. -/
theorem edgeCodeEval_monochromatic_subspace {a b c : ℕ}
    (hc : 1 < c) (hacLt : a < c)
    (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (η : ℕ) :
    ∃ n : ℕ, ∃ l : Subspace (Fin η) (Fin c) (Fin n), ∃ k : ℕ,
      ∀ x : Fin η → Fin c,
        edgeCodeEval a b c n (l x) / c ^ n = k := by
  let A := edgeDigitMass a b c
  rcases Subspace.exists_mono_in_high_dimension_fin
      (Fin c) (Fin (A + 1)) (Fin η) with ⟨n, hn⟩
  have hQ : 0 < c ^ n := by positivity
  let color : (Fin n → Fin c) → Fin (A + 1) := fun w =>
    ⟨edgeCodeEval a b c n w / c ^ n, by
      have hbound := edgeCodeEval_le_mass_mul_pow (a := a) (b := b) (c := c)
        hacLt w
      have hle : edgeCodeEval a b c n w / c ^ n ≤ A := by
        apply Nat.div_le_of_le_mul
        simpa [A, Nat.mul_comm] using hbound
      omega⟩
  rcases hn color with ⟨l, k, hk⟩
  refine ⟨n, l, (k : ℕ), ?_⟩
  intro x
  exact congrArg Fin.val (hk x)

/-- Distinct parameter words in the monochromatic subspace give distinct
primitive subset sums, and every pair is separated by less than one modulus
`c^n`. -/
theorem primitive_monochromatic_subspace {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hacLt : a < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (η : ℕ) :
    ∃ n : ℕ, ∃ l : Subspace (Fin η) (Fin c) (Fin n),
      (∀ x, IsPrimitive (edgeCodeFinset a b c n (l x))) ∧
      (∀ x z, z ∈ edgeCodeFinset a b c n (l x) → z ∈ Smooth3 a b c) ∧
      (∀ x y, x ≠ y →
        0 < Nat.dist ((edgeCodeFinset a b c n (l x)).sum id)
          ((edgeCodeFinset a b c n (l y)).sum id) ∧
        Nat.dist ((edgeCodeFinset a b c n (l x)).sum id)
          ((edgeCodeFinset a b c n (l y)).sum id) < c ^ n) := by
  letI : Nontrivial (Fin c) := Fin.nontrivial_iff_two_le.mpr hc
  rcases edgeCodeEval_monochromatic_subspace hc hacLt hac hbc η with
    ⟨n, l, k, hk⟩
  refine ⟨n, l, ?_, ?_, ?_⟩
  · intro x
    exact edgeCodeFinset_isPrimitive ha hb hc hab hac hbc (l x)
  · intro x z hz
    exact edgeCodeFinset_subset_smooth3 (l x) z hz
  · intro x y hxy
    have hword : l x ≠ l y := fun h => hxy (subspace_apply_injective l h)
    have heval : edgeCodeEval a b c n (l x) ≠ edgeCodeEval a b c n (l y) := by
      intro h
      apply hword
      apply edgeCodeEval_mod_injective hc hac.symm hbc.symm
      exact congrArg (fun z => z % c ^ n) h
    have hQ : 0 < c ^ n := by positivity
    have hxmod := Nat.mod_add_div (edgeCodeEval a b c n (l x)) (c ^ n)
    have hymod := Nat.mod_add_div (edgeCodeEval a b c n (l y)) (c ^ n)
    rw [hk x] at hxmod
    rw [hk y] at hymod
    have hdist : Nat.dist (edgeCodeEval a b c n (l x))
        (edgeCodeEval a b c n (l y)) < c ^ n := by
      rw [← hxmod, ← hymod]
      rw [Nat.dist_add_add_right]
      by_cases hle : edgeCodeEval a b c n (l x) % c ^ n ≤
          edgeCodeEval a b c n (l y) % c ^ n
      · rw [Nat.dist_eq_sub_of_le hle]
        exact Nat.sub_lt_of_lt (Nat.mod_lt (edgeCodeEval a b c n (l y)) hQ)
      · have hle' : edgeCodeEval a b c n (l y) % c ^ n ≤
            edgeCodeEval a b c n (l x) % c ^ n := by omega
        rw [Nat.dist_eq_sub_of_le_right hle']
        exact Nat.sub_lt_of_lt (Nat.mod_lt (edgeCodeEval a b c n (l x)) hQ)
    rw [edgeCodeFinset_sum ha hb hc hab hac hbc (l x),
      edgeCodeFinset_sum ha hb hc hab hac hbc (l y)]
    exact ⟨Nat.dist_pos_of_ne heval, hdist⟩

end

end Erdos123
