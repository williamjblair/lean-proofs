/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBSeries
import ErdosProblems.Erdos23GapGACanonical

/-!
# Erdős 23 G-B: bridge-free corridor coverage

This file banks two proper reductions for the inductive RL* frontier.

First, it retains the exact partner-distance size gate for series blocks,
instead of replacing it by the sufficient but lossy condition that both
bridge components have at least four vertices.

Second, it isolates the finite interval-cover argument behind a bridge-free
stub corridor.  Every non-bridge interior corridor edge is covered by an
off-corridor component attachment interval.  If a component with `q`
vertices spans at most `q+1` corridor edges, then complete interior coverage
forces `d <= 2s+2`.  Consequently an `n>=14` bridge-free residual instance
has `s>=4`, eliminating the previously open `s=2,3` thin-corridor rows.

The graph application still has to supply the already-banked attachment-span
and non-bridge coverage hypotheses.  No multi-edge mass bound or full RL*
closure is claimed here.
-/

namespace Erdos23GapGBJoint

open scoped BigOperators
open Erdos23GapGBSeries

/-- The exceptional value of the partner-distance function is attained only
at stub distance one. -/
theorem partnerDistance_eq_three_iff {d : ℕ} :
    partnerDistance d = 3 ↔ d = 1 := by
  unfold partnerDistance
  by_cases h1 : d = 1
  · simp [h1]
  · by_cases heven : d % 2 = 0 <;> simp [h1, heven]

/-- Moving an M-free endpoint leaf one step inward cannot increase the exact
RL budget.  This is the arithmetic node used by both root move and stub
retraction. -/
theorem rlBudget_pred_le {s d : ℕ} (hd : 2 ≤ d) :
    rlBudget s (d - 1) ≤ rlBudget s d := by
  have hp : partnerDistance (d - 1) ≤ partnerDistance d + 1 := by
    unfold partnerDistance
    by_cases hd1 : d = 1
    · omega
    by_cases hpred1 : d - 1 = 1
    · simp [hpred1]
      have : d = 2 := by omega
      subst d
      decide
    · simp [hd1, hpred1]
      split <;> split <;> omega
  have hmul := Nat.mul_le_mul_left (2 * s) hp
  unfold rlBudget
  have hbase : 2 * (d - 1) + 2 + s = 2 * d + s := by omega
  calc
    s * (2 * (d - 1) + 2 + s) + 2 * s * partnerDistance (d - 1) =
        s * (2 * d + s) + 2 * s * partnerDistance (d - 1) := by rw [hbase]
    _ ≤ s * (2 * d + s) + 2 * s * (partnerDistance d + 1) :=
      Nat.add_le_add_left hmul _
    _ = s * (2 * d + 2 + s) + 2 * s * partnerDistance d := by ring

/-- Exact residual dispatch for an interior series bridge.  If both bridge
components contain at least three vertices, strict Gamma induction applies
through the exact partner-distance gate.  Thus any gate failure in the
middle regime has a two-vertex endpoint component, which is precisely the
M-free endpoint-leaf case handled by root move or stub retraction. -/
theorem residual_series_gate_or_endpoint_pair
    {n n₁ n₂ d d₁ d₂ s : ℕ}
    (hn : 14 ≤ n) (hnSplit : n = n₁ + n₂)
    (hdSplit : d = d₁ + d₂ + 1)
    (hd₁pos : 1 ≤ d₁) (hd₂pos : 1 ≤ d₂)
    (hd₁size : d₁ + 1 ≤ n₁) (hd₂size : d₂ + 1 ≤ n₂)
    (hs : s = n - 1 - d)
    (hresidual : 2 * s * partnerDistance d < (d + 1) ^ 2) :
    (partnerDistance d₁ < n₂ ∧ partnerDistance d₂ < n₁) ∨
      n₁ = 2 ∨ n₂ = 2 := by
  by_contra hgoal
  push Not at hgoal
  rcases hgoal with ⟨hgate, hn₁two, hn₂two⟩
  have hn₁three : 3 ≤ n₁ := by omega
  have hn₂three : 3 ≤ n₂ := by omega
  have hbadGate : n₂ ≤ partnerDistance d₁ ∨
      n₁ ≤ partnerDistance d₂ := by omega
  rcases hbadGate with hbad | hbad
  · have hp₁le := partnerDistance_le_three d₁
    have hn₂le : n₂ ≤ 3 := hbad.trans hp₁le
    have hn₂eq : n₂ = 3 := by omega
    have hp₁ : partnerDistance d₁ = 3 := by omega
    have hd₁one : d₁ = 1 := partnerDistance_eq_three_iff.mp hp₁
    have hd₂le : d₂ ≤ 2 := by omega
    have hdle : d ≤ 4 := by omega
    have hsLower : 9 ≤ s := by omega
    interval_cases d <;> simp [partnerDistance] at hresidual <;> omega
  · have hp₂le := partnerDistance_le_three d₂
    have hn₁le : n₁ ≤ 3 := hbad.trans hp₂le
    have hn₁eq : n₁ = 3 := by omega
    have hp₂ : partnerDistance d₂ = 3 := by omega
    have hd₂one : d₂ = 1 := partnerDistance_eq_three_iff.mp hp₂
    have hd₁le : d₁ ≤ 2 := by omega
    have hdle : d ≤ 4 := by omega
    have hsLower : 9 ≤ s := by omega
    interval_cases d <;> simp [partnerDistance] at hresidual <;> omega

/-- Corridor edge indices with positive distance on both the root and stub
sides.  Index `i` represents the edge from positions `i` to `i+1`. -/
def interiorCorridorIndices (d : ℕ) : Finset ℕ :=
  Finset.Ico 1 (d - 1)

/-- The union of all attachment intervals supplied by off-corridor
components. -/
def coveredCorridorIndices
    {α : Type*} [DecidableEq α]
    (components : Finset α) (lo hi : α → ℕ) : Finset ℕ :=
  components.biUnion fun c => Finset.Ico (lo c) (hi c)

/-- Abstract interval-cover count used by the bridge-free graph
application.  It contains every constant explicitly. -/
theorem interior_coverage_card_le_twice_mass
    {α : Type*} [DecidableEq α]
    {components : Finset α} {lo hi size : α → ℕ} {d s : ℕ}
    (hcover : interiorCorridorIndices d ⊆
      coveredCorridorIndices components lo hi)
    (hspan : ∀ c ∈ components, hi c - lo c ≤ size c + 1)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c ≤ s) :
    (interiorCorridorIndices d).card ≤ 2 * s := by
  have hcardCover :
      (interiorCorridorIndices d).card ≤
        (coveredCorridorIndices components lo hi).card :=
    Finset.card_le_card hcover
  have hunion :
      (coveredCorridorIndices components lo hi).card ≤
        ∑ c ∈ components, (Finset.Ico (lo c) (hi c)).card := by
    exact Finset.card_biUnion_le
  have hinterval :
      (∑ c ∈ components, (Finset.Ico (lo c) (hi c)).card) ≤
        ∑ c ∈ components, (size c + 1) := by
    apply Finset.sum_le_sum
    intro c hc
    simpa using hspan c hc
  have hcomponents : components.card ≤ ∑ c ∈ components, size c := by
    calc
      components.card = ∑ _c ∈ components, 1 := by simp
      _ ≤ ∑ c ∈ components, size c := by
        apply Finset.sum_le_sum
        intro c hc
        exact hpositive c hc
  have hsum : ∑ c ∈ components, (size c + 1) ≤ 2 * s := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, smul_eq_mul]
    omega
  exact hcardCover.trans (hunion.trans (hinterval.trans hsum))

/-- Complete bridge-free interior coverage forces the corridor length to be
at most twice the off-corridor mass plus two. -/
theorem corridor_length_le_twice_slack_add_two
    {α : Type*} [DecidableEq α]
    {components : Finset α} {lo hi size : α → ℕ} {d s : ℕ}
    (hd : 2 ≤ d)
    (hcover : interiorCorridorIndices d ⊆
      coveredCorridorIndices components lo hi)
    (hspan : ∀ c ∈ components, hi c - lo c ≤ size c + 1)
    (hpositive : ∀ c ∈ components, 1 ≤ size c)
    (hmass : ∑ c ∈ components, size c ≤ s) :
    d ≤ 2 * s + 2 := by
  have hcard := interior_coverage_card_le_twice_mass
    hcover hspan hpositive hmass
  have hcardEq : (interiorCorridorIndices d).card = d - 2 := by
    simp [interiorCorridorIndices]
    omega
  rw [hcardEq] at hcard
  omega

/-- In the `n>=14` residual, the bridge-free coverage inequality excludes
both previously enumerated thin rows `s=2` and `s=3`. -/
theorem bridge_free_residual_slack_at_least_four
    {n d s : ℕ}
    (hn : 14 ≤ n)
    (hsize : n = d + 1 + s)
    (hcorridor : d ≤ 2 * s + 2) :
    4 ≤ s := by
  omega

section GraphApplication

open SimpleGraph
open Erdos23GapGA

variable {V : Type*}

/-- Every canonical off-corridor component contains at least one vertex. -/
theorem offCorridorComponentFinset_card_pos
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (C : OffCorridorComponent P) :
    0 < (offCorridorComponentFinset C).card := by
  classical
  obtain ⟨x, hx⟩ := C.nonempty
  exact Finset.card_pos.mpr ⟨x, (mem_offCorridorComponentFinset C).2 hx⟩

/-- Graph-level bridge-free corridor bound.  This instantiates the abstract
interval count with the canonical connected components of `G - V(P)` and
uses the already verified attachment-span theorem. -/
theorem IsGeodesic.length_le_twice_slack_add_two_of_interior_nonbridge
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P) (hd : 2 ≤ P.length)
    (hnonbridge : ∀ i ∈ interiorCorridorIndices P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    P.length ≤ 2 * slack P + 2 := by
  classical
  let components : Finset (OffCorridorComponent P) := Finset.univ
  let intervals : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  have hcover : interiorCorridorIndices P.length ⊆
      components.biUnion intervals := by
    intro i hi
    have hiLt : i < P.length := by
      have hiIco := (Finset.mem_Ico.mp hi).2
      omega
    obtain ⟨C, hC⟩ :=
      hP.exists_offCorridorComponent_coversIndex_of_not_isBridge hiLt
        (hnonbridge i hi)
    apply Finset.mem_biUnion.mpr
    exact ⟨C, Finset.mem_univ C,
      mem_offCorridorComponentIntervalEdges_of_coversIndex P C hC⟩
  have hunion :
      (interiorCorridorIndices P.length).card ≤
        ∑ C : OffCorridorComponent P, (intervals C).card := by
    calc
      (interiorCorridorIndices P.length).card ≤
          (components.biUnion intervals).card := Finset.card_le_card hcover
      _ ≤ ∑ C ∈ components, (intervals C).card :=
        Finset.card_biUnion_le
      _ = ∑ C : OffCorridorComponent P, (intervals C).card := by
        simp [components]
  have hspan :
      ∑ C : OffCorridorComponent P, (intervals C).card ≤
        ∑ C : OffCorridorComponent P,
          ((offCorridorComponentFinset C).card + 1) := by
    apply Finset.sum_le_sum
    intro C _
    rw [show (intervals C).card = offCorridorComponentSpan P C by
      simpa [intervals] using card_offCorridorComponentIntervalEdges P C]
    exact hP.offCorridorComponentSpan_le_card_add_one C
  have hpositive :
      (Finset.univ : Finset (OffCorridorComponent P)).card ≤
        ∑ C : OffCorridorComponent P,
          (offCorridorComponentFinset C).card := by
    calc
      (Finset.univ : Finset (OffCorridorComponent P)).card =
          ∑ _C : OffCorridorComponent P, 1 := by simp
      _ ≤ ∑ C : OffCorridorComponent P,
          (offCorridorComponentFinset C).card := by
        apply Finset.sum_le_sum
        intro C _
        exact offCorridorComponentFinset_card_pos C
  have hmassRaw :
      ∑ C : OffCorridorComponent P,
          (offCorridorComponentFinset C).card =
        ((Finset.univ : Finset V) \ supportFinset P).card := by
    calc
      ∑ C : OffCorridorComponent P,
          (offCorridorComponentFinset C).card =
          ∑ C : OffCorridorComponent P, ∑ x : V,
            if x ∈ C then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro C _
        rw [Finset.sum_boole]
        congr 1
      _ = ∑ x : V, ∑ C : OffCorridorComponent P,
          if x ∈ C then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ x : V, if x ∉ supportFinset P then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ supportFinset P
        · simp [ComponentCompl.mem_supp_iff, hx]
        · simp [ComponentCompl.mem_supp_iff, hx]
      _ = ((Finset.univ : Finset V) \ supportFinset P).card := by
        rw [Finset.sum_boole, ← Finset.sdiff_eq_filter]
        norm_cast
  have hsupp := hP.card_supportFinset
  have hle : P.length + 1 ≤ Fintype.card V := by
    rw [← hsupp]
    exact Finset.card_le_univ _
  have hmass :
      ∑ C : OffCorridorComponent P,
          (offCorridorComponentFinset C).card = slack P := by
    rw [hmassRaw, Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, slack]
    omega
  have hcard : (interiorCorridorIndices P.length).card ≤ 2 * slack P := by
    rw [Finset.sum_add_distrib] at hspan
    simp only [Finset.sum_const, smul_eq_mul] at hspan
    omega
  have hcardEq : (interiorCorridorIndices P.length).card = P.length - 2 := by
    simp [interiorCorridorIndices]
    omega
  rw [hcardEq] at hcard
  omega

/-- Concrete bridge-free residual consequence, expressed directly using
the ambient graph order and the canonical geodesic slack. -/
theorem IsGeodesic.slack_at_least_four_of_large_bridge_free_corridor
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P)
    (hn : 14 ≤ Fintype.card V) (hd : 2 ≤ P.length)
    (hnonbridge : ∀ i ∈ interiorCorridorIndices P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    4 ≤ slack P := by
  have hcorridor :=
    length_le_twice_slack_add_two_of_interior_nonbridge hP hd hnonbridge
  have hsupp := hP.card_supportFinset
  simp only [slack] at hcorridor ⊢
  omega

end GraphApplication

#print axioms interior_coverage_card_le_twice_mass
#print axioms corridor_length_le_twice_slack_add_two
#print axioms bridge_free_residual_slack_at_least_four
#print axioms partnerDistance_eq_three_iff
#print axioms rlBudget_pred_le
#print axioms residual_series_gate_or_endpoint_pair
#print axioms IsGeodesic.length_le_twice_slack_add_two_of_interior_nonbridge
#print axioms IsGeodesic.slack_at_least_four_of_large_bridge_free_corridor

end Erdos23GapGBJoint
