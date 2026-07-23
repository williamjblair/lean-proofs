import Research.NumericalSemigroup
import Research.RegularSemigroup
import Research.DenseGcdTruncation
import Research.ElementaryAsymptotic

/-!
# An explicit elementary conductor for the dense regular increments

A finite family of natural numbers with gcd one gives all residues modulo any
positive modulus.  Reducing Bezout coefficients modulo the modulus makes the
representatives quantitatively bounded.  Applied to regular-grid increments,
this supplies the conductor needed by the elementary asymptotic reduction.
-/

namespace Erdos769

lemma intCast_finset_gcd (s : Finset ℕ) (f : ℕ → ℕ) :
    ((s.gcd f : ℕ) : ℤ) = s.gcd (fun i => (f i : ℤ)) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.gcd_insert, Finset.gcd_insert, ← ih]
    rw [← Int.coe_gcd, Int.gcd_natCast_natCast]
    rfl

/-- Quantitative Bezout residues.  If the values of `f` on `s` have gcd one,
lie below `L`, and belong to `S`, then every residue modulo `a` has a
representative in `S` bounded by `s.card * (a-1) * L`. -/
theorem AddSubmonoid.bounded_residues_of_finset_gcd_one
    (S : AddSubmonoid ℕ) (s : Finset ℕ) (f : ℕ → ℕ) {a L : ℕ}
    (ha : 0 < a) (hgcd : s.gcd f = 1)
    (hbound : ∀ i ∈ s, f i ≤ L)
    (hmem : ∀ i ∈ s, f i ∈ S) :
    ∀ r < a, ∃ w,
      w ≤ s.card * (a - 1) * L ∧ w ∈ S ∧ w % a = r := by
  letI : NeZero a := ⟨Nat.ne_of_gt ha⟩
  have hgcdInt : s.gcd (fun i => (f i : ℤ)) = 1 := by
    rw [← intCast_finset_gcd, hgcd]
    norm_num
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul s (fun i => (f i : ℤ))
  rw [hgcdInt] at hg
  intro r hr
  let coeff : ℕ → ℕ := fun i => ((r : ZMod a) * (g i : ZMod a)).val
  let w : ℕ := ∑ i ∈ s, coeff i * f i
  refine ⟨w, ?_, ?_, ?_⟩
  · calc
      w ≤ ∑ i ∈ s, (a - 1) * L := by
        dsimp [w]
        apply Finset.sum_le_sum
        intro i hi
        have hc : coeff i ≤ a - 1 := by
          have := ZMod.val_lt ((r : ZMod a) * (g i : ZMod a))
          dsimp [coeff]
          omega
        exact Nat.mul_le_mul hc (hbound i hi)
      _ = s.card * (a - 1) * L := by
        simp [mul_assoc]
  · dsimp [w]
    apply S.sum_mem
    intro i hi
    exact S.nsmul_mem (hmem i hi) (coeff i)
  · have hgmod := congrArg (fun z : ℤ => (z : ZMod a)) hg
    have hcast : (w : ZMod a) = (r : ZMod a) := by
      dsimp [w]
      push_cast
      simp_rw [show ∀ i, ((coeff i : ℕ) : ZMod a) =
          (r : ZMod a) * (g i : ZMod a) by
        intro i
        exact ZMod.natCast_zmod_val _]
      calc
        ∑ i ∈ s, ((r : ZMod a) * (g i : ZMod a)) * (f i : ZMod a) =
            (r : ZMod a) * ∑ i ∈ s, (f i : ZMod a) * (g i : ZMod a) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (r : ZMod a) * 1 := by
              congr 1
              simpa using hgmod.symm
        _ = (r : ZMod a) := mul_one _
    have hmod := (ZMod.natCast_eq_natCast_iff' w r a).mp hcast
    simpa [Nat.mod_eq_of_lt hr] using hmod

lemma regularIncrement_mem {n j : ℕ} (hj : 0 < j) :
    j ^ n - 1 ∈ AddSubmonoid.closure (regularIncrements n) := by
  apply AddSubmonoid.subset_closure
  exact ⟨j, hj, rfl⟩

/-- In every odd dimension at least 201, all increments above the elementary
threshold's main term belong to the semigroup of regular-grid increments. -/
theorem dense_regularIncrement_conductor
    {n : ℕ} (hn : 201 ≤ n) (hnodd : Odd n) :
    ∀ x, n * 2 ^ n * (denseBase n) ^ n ≤ x →
      x ∈ AddSubmonoid.closure (regularIncrements n) := by
  let M := denseBase n
  let s : Finset ℕ := Finset.Icc 2 M
  let f : ℕ → ℕ := fun j => j ^ n - 1
  let a := 2 ^ n - 1
  let R := n * 2 ^ n * M ^ n
  let S := AddSubmonoid.closure (regularIncrements n)
  have hM : 2 ≤ M := by
    have := (denseBase_bounds hn).1
    simpa [M] using (show 2 ≤ denseBase n by omega)
  have ha : 0 < a := by
    dsimp [a]
    have : 1 < 2 ^ n := one_lt_pow₀ (by norm_num) (by omega)
    omega
  have hgcd : s.gcd f = 1 := by
    simpa [s, f, M] using dense_regular_increment_gcd_eq_one hn hnodd
  have hbound : ∀ j ∈ s, f j ≤ M ^ n := by
    intro j hj
    have hjM : j ≤ M := (Finset.mem_Icc.mp hj).2
    dsimp [f]
    have hp := Nat.pow_le_pow_left hjM n
    omega
  have hmem : ∀ j ∈ s, f j ∈ S := by
    intro j hj
    have hjpos : 0 < j := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    exact regularIncrement_mem hjpos
  have hcard : s.card ≤ n := by
    dsimp [s]
    rw [Nat.card_Icc]
    have hb := denseBase_bounds hn
    dsimp [M]
    omega
  have ha_le : a - 1 ≤ 2 ^ n := by
    dsimp [a]
    omega
  have hres0 := AddSubmonoid.bounded_residues_of_finset_gcd_one
    S s f ha hgcd hbound hmem
  have hres : ∀ r < a, ∃ w, w ≤ R ∧ w ∈ S ∧ w % a = r := by
    intro r hr
    obtain ⟨w, hw, hwS, hwmod⟩ := hres0 r hr
    refine ⟨w, ?_, hwS, hwmod⟩
    dsimp [R]
    calc
      w ≤ s.card * (a - 1) * M ^ n := hw
      _ ≤ n * 2 ^ n * M ^ n :=
        Nat.mul_le_mul_right (M ^ n) (Nat.mul_le_mul hcard ha_le)
  have haS : a ∈ S := by
    dsimp [a, S]
    exact regularIncrement_mem (n := n) (j := 2) (by omega)
  intro x hx
  exact AddSubmonoid.all_ge_of_bounded_complete_residues
    S ha haS hres x (by simpa [R] using hx)

/-- The elementary threshold is eventually an actual cubical admissibility
threshold in every odd dimension. -/
theorem eventually_odd_elementaryThreshold_admissible :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → Odd n →
      ∀ k, elementaryThreshold n ≤ k → Admissible n k := by
  refine ⟨201, ?_⟩
  intro n hn hnodd k hk
  let x := k - 1
  have hxbound : n * 2 ^ n * denseBase n ^ n ≤ x := by
    dsimp [elementaryThreshold] at hk
    dsimp [x]
    omega
  have hxmem := dense_regularIncrement_conductor hn hnodd x hxbound
  have hadm := admissible_one_add_of_mem_regularIncrementClosure hxmem
  have hkpos : 0 < k := by
    have : 2 ≤ elementaryThreshold n := by
      dsimp [elementaryThreshold]
      omega
    omega
  have heq : 1 + x = k := by
    dsimp [x]
    omega
  simpa [heq] using hadm

end Erdos769
