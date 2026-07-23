import Mathlib

namespace Erdos254.TailSemigroup

open scoped BigOperators Topology

noncomputable section

/-- Finite sums of distinct eligible terms, all beyond a cutoff. -/
def tailSubsetSums {G : Type*} [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) (N : ℕ) : Set G :=
  {g | ∃ s : Finset ℕ,
    (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧ (∑ n ∈ s, x n) = g}

/-- Points approximable by distinct subset sums beyond every cutoff. -/
def tailLimit {G : Type*} [TopologicalSpace G] [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) : Set G :=
  ⋂ N : ℕ, closure (tailSubsetSums A x N)

lemma tailLimit_isClosed {G : Type*} [TopologicalSpace G] [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) : IsClosed (tailLimit A x) := by
  exact isClosed_iInter (fun N => isClosed_closure)

lemma zero_mem_tailLimit {G : Type*} [TopologicalSpace G] [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) : 0 ∈ tailLimit A x := by
  rw [tailLimit, Set.mem_iInter]
  intro N
  apply subset_closure
  exact ⟨∅, by simp, by simp⟩

/-- In a translation-invariant metric additive group, the tail-limit set is
closed under addition. Distinctness is preserved by putting the second
approximating finset strictly beyond the first. -/
lemma tailLimit_add_mem {G : Type*} [PseudoMetricSpace G] [AddCommGroup G]
    [IsIsometricVAdd G G]
    (A : Set ℕ) (x : ℕ → G) {u v : G}
    (hu : u ∈ tailLimit A x) (hv : v ∈ tailLimit A x) :
    u + v ∈ tailLimit A x := by
  rw [tailLimit, Set.mem_iInter] at hu hv ⊢
  intro N
  rw [Metric.mem_closure_iff]
  intro ε hε
  have huN := hu N
  rw [Metric.mem_closure_iff] at huN
  obtain ⟨a, ha, hua⟩ := huN (ε / 2) (by positivity)
  obtain ⟨s, hs, hsa⟩ := ha
  let K := max N (s.sup (fun k : ℕ => k) + 1)
  have hvK := hv K
  rw [Metric.mem_closure_iff] at hvK
  obtain ⟨b, hb, hvb⟩ := hvK (ε / 2) (by positivity)
  obtain ⟨t, ht, htb⟩ := hb
  have hdisj : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro n hns hnt
    have hnle : n ≤ s.sup (fun k : ℕ => k) :=
      Finset.le_sup (f := fun k : ℕ => k) hns
    have hnK : n < K := by
      dsimp [K]
      omega
    have hKn : K ≤ n := (ht n hnt).2
    omega
  refine ⟨∑ n ∈ s ∪ t, x n, ?_, ?_⟩
  · refine ⟨s ∪ t, ?_, rfl⟩
    intro n hn
    rw [Finset.mem_union] at hn
    rcases hn with hns | hnt
    · exact hs n hns
    · exact ⟨(ht n hnt).1,
        le_trans (le_max_left N (s.sup (fun k : ℕ => k) + 1)) (ht n hnt).2⟩
  · rw [Finset.sum_union hdisj, hsa, htb]
    calc
      dist (u + v) (a + b) ≤ dist (u + v) (a + v) + dist (a + v) (a + b) :=
        dist_triangle _ _ _
      _ = dist u a + dist v b := by
        rw [dist_add_right, dist_add_left]
      _ < ε := by linarith

lemma tailSubsetSums_mono_cutoff {G : Type*} [AddCommMonoid G]
    (A : Set ℕ) (x : ℕ → G) {N M : ℕ} (hNM : N ≤ M) :
    tailSubsetSums A x M ⊆ tailSubsetSums A x N := by
  rintro g ⟨s, hs, rfl⟩
  exact ⟨s, fun n hn => ⟨(hs n hn).1, hNM.trans (hs n hn).2⟩, rfl⟩

/-- If a closed target set meets the actual subset sums beyond every cutoff,
then it meets their common tail-limit set. -/
theorem tailLimit_meets_closed {G : Type*} [TopologicalSpace G]
    [AddCommMonoid G] [CompactSpace G] [T2Space G]
    (A : Set ℕ) (x : ℕ → G) (E : Set G) (hE : IsClosed E)
    (hmeet : ∀ N, (tailSubsetSums A x N ∩ E).Nonempty) :
    (tailLimit A x ∩ E).Nonempty := by
  let K : ℕ → Set G := fun N => closure (tailSubsetSums A x N) ∩ E
  have hKn : ∀ N, (K N).Nonempty := by
    intro N
    obtain ⟨g, hg, hgE⟩ := hmeet N
    exact ⟨g, subset_closure hg, hgE⟩
  have hKclosed : ∀ N, IsClosed (K N) := fun N => isClosed_closure.inter hE
  have hKcompact : ∀ N, IsCompact (K N) := fun N => (hKclosed N).isCompact
  have hKdir : Directed (fun X Y : Set G => X ⊇ Y) K := by
    intro N M
    refine ⟨max N M, ?_, ?_⟩
    · intro g hg
      exact ⟨closure_mono (tailSubsetSums_mono_cutoff A x (le_max_left N M)) hg.1, hg.2⟩
    · intro g hg
      exact ⟨closure_mono (tailSubsetSums_mono_cutoff A x (le_max_right N M)) hg.1, hg.2⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    K hKdir hKn hKcompact hKclosed
  refine ⟨g, ?_, ?_⟩
  · rw [tailLimit, Set.mem_iInter]
    intro N
    exact (Set.mem_iInter.mp hg N).1
  · exact (Set.mem_iInter.mp hg 0).2

end

end Erdos254.TailSemigroup
