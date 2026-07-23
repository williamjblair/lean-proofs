import Mathlib

namespace Erdos254.PiecewiseAssembly

open scoped BigOperators

noncomputable section

/-- `n` is a sum of distinct members of `B` (the empty sum is allowed). -/
def Representable (B : Set ℕ) (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ b ∈ s, b ∈ B) ∧ ∑ b ∈ s, b = n

lemma representable_mono {B C : Set ℕ} (hBC : B ⊆ C) {n : ℕ}
    (hn : Representable B n) : Representable C n := by
  obtain ⟨s, hsB, rfl⟩ := hn
  exact ⟨s, fun b hb => hBC (hsB b hb), rfl⟩

lemma representable_add_of_disjoint {B C : Set ℕ} (hBC : Disjoint B C)
    {m n : ℕ} (hm : Representable B m) (hn : Representable C n) :
    Representable (B ∪ C) (m + n) := by
  classical
  obtain ⟨s, hsB, rfl⟩ := hm
  obtain ⟨t, htC, rfl⟩ := hn
  have hst : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro x hxs hxt
    exact Set.disjoint_left.mp hBC (hsB x hxs) (htC x hxt)
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hxs | hxt
    · exact Or.inl (hsB x hxs)
    · exact Or.inr (htC x hxt)
  · rw [Finset.sum_union hst]

/-- A one-sided set is thick if it contains intervals of every finite length. -/
def IsThick (T : Set ℕ) : Prop :=
  ∀ L : ℕ, ∃ a : ℕ, ∀ k : ℕ, k ≤ L → a + k ∈ T

/-- A finite family of disjoint correction sums which covers every translate
of `good` converts a piecewise-good representability statement into thickness. -/
theorem correction_cover_makes_union_thick
    (B C : Set ℕ) (hBC : Disjoint B C)
    (J : Set ℕ) (good : ℕ → Prop)
    (hJ : IsThick J)
    (hpiece : ∀ n : ℕ, n ∈ J → good n → Representable B n)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Representable C q)
    (N₀ : ℕ)
    (hcover : ∀ n : ℕ, N₀ ≤ n →
      ∃ q ∈ Q, q ≤ n ∧ good (n - q)) :
    IsThick {n | Representable (B ∪ C) n} := by
  intro L
  let M := ∑ q ∈ Q, q
  obtain ⟨a, ha⟩ := hJ (N₀ + M + L)
  refine ⟨a + N₀ + M, ?_⟩
  intro k hk
  let n := a + N₀ + M + k
  have hn0 : N₀ ≤ n := by omega
  obtain ⟨q, hqQ, hqn, hgood⟩ := hcover n hn0
  have hqM : q ≤ M := by
    calc
      q = ∑ x ∈ ({q} : Finset ℕ), x := by simp
      _ ≤ ∑ x ∈ Q, x := Finset.sum_le_sum_of_subset (by simpa using hqQ)
  have hJmem : n - q ∈ J := by
    have heq : n - q = a + (N₀ + M + k - q) := by omega
    rw [heq]
    apply ha
    omega
  have hrepB := hpiece (n - q) hJmem hgood
  have hrep := representable_add_of_disjoint hBC hrepB (hQ q hqQ)
  have hnq : n - q + q = n := by omega
  rw [hnq] at hrep
  simpa [n, Nat.add_assoc] using hrep

/-- Adding a syndetic distinct-subset-sum set to a thick representability set
makes all sufficiently large integers representable, with disjointness ensuring
that no summand is reused. -/
theorem thick_add_syndetic_is_cofinite
    (E D : Set ℕ) (hED : Disjoint E D)
    (hthick : IsThick {n | Representable E n})
    (K : ℕ)
    (hsyndetic : ∀ n : ℕ, ∃ s : ℕ,
      Representable D s ∧ s ≤ n ∧ n ≤ s + K) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Representable (E ∪ D) n := by
  obtain ⟨a, ha⟩ := hthick K
  refine ⟨a + K, ?_⟩
  intro n hn
  obtain ⟨s, hsD, hslo, hshi⟩ := hsyndetic (n - a)
  let k := n - a - s
  have hk : k ≤ K := by omega
  have htE : Representable E (a + k) := ha k hk
  have heq : a + k + s = n := by omega
  have hadd := representable_add_of_disjoint hED htE hsD
  rwa [heq] at hadd

/-- Fully assembled abstract criterion: piecewise-good sums from `B`, a finite
correction cover from disjoint `C`, and a disjoint syndetic class `D` imply
cofinite distinct subset-sum representability. -/
theorem piecewise_correction_syndetic_assembly
    (B C D : Set ℕ)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (J : Set ℕ) (good : ℕ → Prop)
    (hJ : IsThick J)
    (hpiece : ∀ n : ℕ, n ∈ J → good n → Representable B n)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Representable C q)
    (N₁ : ℕ) (hcover : ∀ n : ℕ, N₁ ≤ n →
      ∃ q ∈ Q, q ≤ n ∧ good (n - q))
    (K : ℕ) (hsyndetic : ∀ n : ℕ, ∃ s : ℕ,
      Representable D s ∧ s ≤ n ∧ n ≤ s + K) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Representable (B ∪ C ∪ D) n := by
  have hthick := correction_cover_makes_union_thick B C hBC J good hJ hpiece
    Q hQ N₁ hcover
  have hUnionD : Disjoint (B ∪ C) D := hBD.union_left hCD
  simpa [Set.union_assoc] using
    thick_add_syndetic_is_cofinite (B ∪ C) D hUnionD hthick K hsyndetic

end

end Erdos254.PiecewiseAssembly
