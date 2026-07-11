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

/-- Absorption inequality for a Gamma-controlled block attached beyond an
endpoint corridor bridge.  A block of order `a >= 2` contributes at most
`a^2`; the remaining rooted block has slack `s` and distance `d`, while the
whole instance has slack `s+a-1` and distance `d+1`. -/
theorem gammaBlock_endpointBridge_le_rlBudget
    {a s d Γ : ℕ} (ha : 2 ≤ a) (hd : 1 ≤ d) (hΓ : Γ ≤ a ^ 2) :
    Γ + rlBudget s d ≤ rlBudget (s + a - 1) (d + 1) := by
  have hp : partnerDistance d ≤ partnerDistance (d + 1) + 1 := by
    unfold partnerDistance
    by_cases hd1 : d = 1
    · subst d
      decide
    · by_cases heven : d % 2 = 0
      · have hmod := Nat.add_mod d 1 2
        have hd0 : d ≠ 0 := by omega
        have hnextOdd : (d + 1) % 2 ≠ 0 := by
          simp [heven] at hmod
          omega
        simp [hd0, hd1, heven, hnextOdd]
      · simp [hd1, heven]
  have hppos := partnerDistance_pos (d + 1)
  have hmul := Nat.mul_le_mul_left (2 * s) hp
  have hsa : s + a - 1 = s + (a - 1) := by omega
  have haEq : a - 1 + 1 = a := by omega
  rw [hsa]
  unfold rlBudget
  calc
    Γ + (s * (2 * d + 2 + s) + 2 * s * partnerDistance d) ≤
        a ^ 2 + (s * (2 * d + 2 + s) +
          2 * s * (partnerDistance (d + 1) + 1)) := by omega
    _ ≤ (s + (a - 1)) *
          (2 * (d + 1) + 2 + (s + (a - 1))) +
        2 * (s + (a - 1)) * partnerDistance (d + 1) := by
      nlinarith [show 0 ≤ 2 * s * (a - 1) by omega,
        show 0 ≤ 2 * (a - 1) * d by omega,
        show 0 ≤ 2 * (a - 1) * partnerDistance (d + 1) by omega]

/-- Exact endpoint-block dispatch: an endpoint component is either one of
the three M-free small orders or is large enough to provide the strict
partner-distance room for the opposite minimal composite. -/
theorem endpointBlock_small_or_partner_lt (a d : ℕ) :
    a ≤ 3 ∨ partnerDistance d < a := by
  have hp := partnerDistance_le_three d
  omega

section CutPotentialDuality

@[simp]
theorem separation_not_not (a b : Bool) :
    separation (!a) (!b) = separation a b := by
  cases a <;> cases b <;> simp [separation]

/-- Membership of a vertex value above an integer threshold. -/
def thresholdBit {V : Type*} (f : V → ℕ) (k : ℕ) (v : V) : Bool :=
  decide (k < f v)

/-- Exact layer-cake identity: the number of thresholds separating two
natural values is their natural distance. -/
theorem sum_thresholdSeparation_eq_dist
    {a b H : ℕ} (ha : a ≤ H) (hb : b ≤ H) :
    ∑ k ∈ Finset.range H,
        separation (decide (k < a)) (decide (k < b)) = Nat.dist a b := by
  have hforward : ∀ {x y : ℕ}, x ≤ y → y ≤ H →
      (∑ k ∈ Finset.range H,
        separation (decide (k < x)) (decide (k < y))) = y - x := by
    intro x y hxy hyH
    have hfilter :
        (Finset.range H).filter (fun k => x ≤ k ∧ k < y) =
          Finset.Ico x y := by
      ext k
      simp
      omega
    calc
      ∑ k ∈ Finset.range H,
          separation (decide (k < x)) (decide (k < y)) =
          ∑ k ∈ Finset.range H, if x ≤ k ∧ k < y then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hkx : k < x <;> by_cases hky : k < y <;>
              simp [separation, hkx, hky] <;> omega
      _ = (Finset.Ico x y).card := by
        rw [Finset.sum_boole]
        exact congrArg Finset.card hfilter
      _ = y - x := by simp
  rcases le_total a b with hab | hba
  · rw [hforward hab hb]
    exact (Nat.dist_eq_sub_of_le hab).symm
  · have hsym :
        (∑ k ∈ Finset.range H,
          separation (decide (k < a)) (decide (k < b))) =
        ∑ k ∈ Finset.range H,
          separation (decide (k < b)) (decide (k < a)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact separation_comm _ _
    rw [hsym, hforward hba ha]
    exact (Nat.dist_eq_sub_of_le_right hba).symm

/-- Exact coarea dual of RFC.  If every threshold cut of an integer
potential satisfies the rooted cut inequality, then the total potential
variation of all internal demands plus the terminal pair is dominated by
the supply-edge variation.

The finite index types permit repeated abstract edges; graph applications
instantiate them with edge subtypes. -/
theorem rootedCutCondition_natPotential
    {V I_B I_M : Type*} [Fintype I_B] [Fintype I_M]
    (b₁ b₂ : I_B → V) (m₁ m₂ : I_M → V)
    (w x₀ : V) (f : V → ℕ) (H : ℕ)
    (hf : ∀ v, f v ≤ H)
    (hcut : ∀ k < H,
      (∑ i : I_M, separation (thresholdBit f k (m₁ i))
          (thresholdBit f k (m₂ i))) +
        separation (thresholdBit f k w) (thresholdBit f k x₀) ≤
      ∑ e : I_B, separation (thresholdBit f k (b₁ e))
        (thresholdBit f k (b₂ e))) :
    (∑ i : I_M, Nat.dist (f (m₁ i)) (f (m₂ i))) +
        Nat.dist (f w) (f x₀) ≤
      ∑ e : I_B, Nat.dist (f (b₁ e)) (f (b₂ e)) := by
  have hsum := Finset.sum_le_sum fun k (hk : k ∈ Finset.range H) =>
    hcut k (Finset.mem_range.mp hk)
  calc
    (∑ i : I_M, Nat.dist (f (m₁ i)) (f (m₂ i))) +
        Nat.dist (f w) (f x₀) =
      (∑ i : I_M, ∑ k ∈ Finset.range H,
        separation (thresholdBit f k (m₁ i))
          (thresholdBit f k (m₂ i))) +
      ∑ k ∈ Finset.range H,
        separation (thresholdBit f k w) (thresholdBit f k x₀) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro i _
            simpa [thresholdBit] using
              (sum_thresholdSeparation_eq_dist (hf (m₁ i)) (hf (m₂ i))).symm
          · simpa [thresholdBit] using
              (sum_thresholdSeparation_eq_dist (hf w) (hf x₀)).symm
    _ = ∑ k ∈ Finset.range H,
        ((∑ i : I_M, separation (thresholdBit f k (m₁ i))
            (thresholdBit f k (m₂ i))) +
          separation (thresholdBit f k w) (thresholdBit f k x₀)) := by
      rw [Finset.sum_comm]
      simp [Finset.sum_add_distrib]
    _ ≤ ∑ k ∈ Finset.range H,
        ∑ e : I_B, separation (thresholdBit f k (b₁ e))
          (thresholdBit f k (b₂ e)) := hsum
    _ = ∑ e : I_B, Nat.dist (f (b₁ e)) (f (b₂ e)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      simpa [thresholdBit] using
        sum_thresholdSeparation_eq_dist (hf (b₁ e)) (hf (b₂ e))

/-- Direct all-cuts form of the integer-potential dual.  This is the exact
abstract RFC interface: instantiate `cut` by membership in an arbitrary
vertex subset. -/
theorem rootedCutCondition_natPotential_of_allCuts
    {V I_B I_M : Type*} [Fintype I_B] [Fintype I_M]
    (b₁ b₂ : I_B → V) (m₁ m₂ : I_M → V)
    (w x₀ : V)
    (hRFC : ∀ cut : V → Bool,
      (∑ i : I_M, separation (cut (m₁ i)) (cut (m₂ i))) +
          separation (cut w) (cut x₀) ≤
        ∑ e : I_B, separation (cut (b₁ e)) (cut (b₂ e)))
    (f : V → ℕ) (H : ℕ) (hf : ∀ v, f v ≤ H) :
    (∑ i : I_M, Nat.dist (f (m₁ i)) (f (m₂ i))) +
        Nat.dist (f w) (f x₀) ≤
      ∑ e : I_B, Nat.dist (f (b₁ e)) (f (b₂ e)) := by
  exact rootedCutCondition_natPotential b₁ b₂ m₁ m₂ w x₀ f H hf
    (fun k _ => hRFC (thresholdBit f k))

/-- Original rooted RFC form, quantified only over cuts not containing the
root.  Complementing a cut containing the root preserves every separation,
so it supplies the all-cuts hypothesis above. -/
theorem rootedCutCondition_natPotential_of_rootCuts
    {V I_B I_M : Type*} [Fintype I_B] [Fintype I_M]
    (b₁ b₂ : I_B → V) (m₁ m₂ : I_M → V)
    (w x₀ : V)
    (hRFC : ∀ cut : V → Bool, cut w = false →
      (∑ i : I_M, separation (cut (m₁ i)) (cut (m₂ i))) +
          separation (cut w) (cut x₀) ≤
        ∑ e : I_B, separation (cut (b₁ e)) (cut (b₂ e)))
    (f : V → ℕ) (H : ℕ) (hf : ∀ v, f v ≤ H) :
    (∑ i : I_M, Nat.dist (f (m₁ i)) (f (m₂ i))) +
        Nat.dist (f w) (f x₀) ≤
      ∑ e : I_B, Nat.dist (f (b₁ e)) (f (b₂ e)) := by
  apply rootedCutCondition_natPotential_of_allCuts b₁ b₂ m₁ m₂ w x₀
    (f := f) (H := H) (hf := hf)
  intro cut
  by_cases hw : cut w = false
  · exact hRFC cut hw
  · let cut' : V → Bool := fun v => !(cut v)
    have hwtrue : cut w = true := by
      cases h : cut w <;> simp_all
    have hcomp := hRFC cut' (by simp [cut', hwtrue])
    simpa [cut'] using hcomp

/-- A potential that separates every internal demand by its prescribed cost
plus a common reserve `lambda` certifies the total cost.  The reserve is paid
twice because the intended RL application has at least two internal edges. -/
theorem totalCost_le_of_potentialCertificate
    {I : Type*} [Fintype I]
    (cost variation : I → ℕ) (terminal budget lambda : ℕ)
    (hcard : 2 ≤ Fintype.card I)
    (hseparate : ∀ i, cost i + lambda ≤ variation i)
    (hcoarea : (∑ i, variation i) + terminal ≤
      terminal + budget + 2 * lambda) :
    ∑ i, cost i ≤ budget := by
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ : Finset I)) =>
    hseparate i
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  have hcard' : 2 ≤ (Finset.univ : Finset I).card := by
    simpa using hcard
  have hlambda : 2 * lambda ≤ (Finset.univ : Finset I).card * lambda := by
    exact Nat.mul_le_mul_right lambda hcard'
  omega

/-- Complete RFC cut-dual certificate interface.  The hypotheses after RFC
are now purely constructive: a bounded natural potential, a uniform reserve,
per-demand quadratic separation, and one explicit supply-variation budget.
Supplying such data for BF-RL would close its aggregation without any
multicommodity-routing assertion. -/
theorem rootedCutCondition_totalCost_le_of_potentialCertificate
    {V I_B I_M : Type*} [Fintype I_B] [Fintype I_M]
    (b₁ b₂ : I_B → V) (m₁ m₂ : I_M → V)
    (w x₀ : V)
    (hRFC : ∀ cut : V → Bool, cut w = false →
      (∑ i : I_M, separation (cut (m₁ i)) (cut (m₂ i))) +
          separation (cut w) (cut x₀) ≤
        ∑ e : I_B, separation (cut (b₁ e)) (cut (b₂ e)))
    (cost : I_M → ℕ) (f : V → ℕ) (H budget lambda : ℕ)
    (hf : ∀ v, f v ≤ H) (hcard : 2 ≤ Fintype.card I_M)
    (hseparate : ∀ i, cost i + lambda ≤
      Nat.dist (f (m₁ i)) (f (m₂ i)))
    (hbudget : (∑ e : I_B, Nat.dist (f (b₁ e)) (f (b₂ e))) ≤
      Nat.dist (f w) (f x₀) + budget + 2 * lambda) :
    ∑ i : I_M, cost i ≤ budget := by
  have hcoarea := rootedCutCondition_natPotential_of_rootCuts
    b₁ b₂ m₁ m₂ w x₀ hRFC f H hf
  apply totalCost_le_of_potentialCertificate cost
    (fun i => Nat.dist (f (m₁ i)) (f (m₂ i)))
    (Nat.dist (f w) (f x₀)) budget lambda hcard hseparate
  exact hcoarea.trans hbudget

end CutPotentialDuality

/-- Removing an M-free endpoint block of `a` vertices retracts one corridor
edge and `a-1` slack vertices, and cannot increase the RL budget. -/
theorem rlBudget_endpointBlock_retraction_le
    {a s d : ℕ} (hd : 2 ≤ d) :
    rlBudget (s - (a - 1)) (d - 1) ≤ rlBudget s d := by
  calc
    rlBudget (s - (a - 1)) (d - 1) ≤ rlBudget s (d - 1) := by
      unfold rlBudget
      have hp := partnerDistance_pos (d - 1)
      nlinarith [Nat.sub_le s (a - 1)]
    _ ≤ rlBudget s d := rlBudget_pred_le hd

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

/-- Any specified set of nonbridge corridor edges is bounded by twice the
off-corridor slack.  This instantiates the interval count with the canonical
connected components of `G - V(P)`. -/
theorem IsGeodesic.corridorIndexSet_card_le_twice_slack
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P) (indices : Finset ℕ)
    (hindices : ∀ i ∈ indices, i < P.length)
    (hnonbridge : ∀ i ∈ indices,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    indices.card ≤ 2 * slack P := by
  classical
  let components : Finset (OffCorridorComponent P) := Finset.univ
  let intervals : OffCorridorComponent P → Finset ℕ :=
    offCorridorComponentIntervalEdges P
  have hcover : indices ⊆ components.biUnion intervals := by
    intro i hi
    obtain ⟨C, hC⟩ :=
      hP.exists_offCorridorComponent_coversIndex_of_not_isBridge (hindices i hi)
        (hnonbridge i hi)
    apply Finset.mem_biUnion.mpr
    exact ⟨C, Finset.mem_univ C,
      mem_offCorridorComponentIntervalEdges_of_coversIndex P C hC⟩
  have hunion :
      indices.card ≤ ∑ C : OffCorridorComponent P, (intervals C).card := by
    calc
      indices.card ≤ (components.biUnion intervals).card :=
        Finset.card_le_card hcover
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
  have hcard : indices.card ≤ 2 * slack P := by
    rw [Finset.sum_add_distrib] at hspan
    simp only [Finset.sum_const, smul_eq_mul] at hspan
    omega
  exact hcard

/-- If every interior corridor edge is a nonbridge, then the corridor has
length at most `2s+2`. -/
theorem IsGeodesic.length_le_twice_slack_add_two_of_interior_nonbridge
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P) (hd : 2 ≤ P.length)
    (hnonbridge : ∀ i ∈ interiorCorridorIndices P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    P.length ≤ 2 * slack P + 2 := by
  have hcard := corridorIndexSet_card_le_twice_slack hP
    (interiorCorridorIndices P.length) (by
      intro i hi
      have hiIco := (Finset.mem_Ico.mp hi).2
      omega) hnonbridge
  have hcardEq : (interiorCorridorIndices P.length).card = P.length - 2 := by
    simp [interiorCorridorIndices]
    omega
  rw [hcardEq] at hcard
  omega

/-- If every edge of the selected geodesic is a nonbridge, complete
attachment coverage removes the two endpoint losses and gives `d <= 2s`. -/
theorem IsGeodesic.length_le_twice_slack_of_all_nonbridge
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    P.length ≤ 2 * slack P := by
  let indices := Finset.Ico 0 P.length
  have hcard := corridorIndexSet_card_le_twice_slack hP indices (by
    intro i hi
    exact (Finset.mem_Ico.mp hi).2) (by
      intro i hi
      exact hnonbridge i (Finset.mem_Ico.mp hi).2)
  simpa [indices] using hcard

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

/-- After endpoint-bridge reduction as well, the full bridge-free residual
has at least five slack vertices. -/
theorem IsGeodesic.slack_at_least_five_of_large_all_nonbridge_corridor
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {P : G.Walk u v} (hP : IsGeodesic P)
    (hn : 14 ≤ Fintype.card V)
    (hnonbridge : ∀ i < P.length,
      ¬G.IsBridge s(P.getVert i, P.getVert (i + 1))) :
    5 ≤ slack P := by
  have hcorridor := length_le_twice_slack_of_all_nonbridge hP hnonbridge
  have hsupp := hP.card_supportFinset
  simp only [slack] at hcorridor ⊢
  omega

end GraphApplication

#print axioms interior_coverage_card_le_twice_mass
#print axioms corridor_length_le_twice_slack_add_two
#print axioms bridge_free_residual_slack_at_least_four
#print axioms partnerDistance_eq_three_iff
#print axioms rlBudget_pred_le
#print axioms gammaBlock_endpointBridge_le_rlBudget
#print axioms endpointBlock_small_or_partner_lt
#print axioms sum_thresholdSeparation_eq_dist
#print axioms rootedCutCondition_natPotential
#print axioms rootedCutCondition_natPotential_of_allCuts
#print axioms rootedCutCondition_natPotential_of_rootCuts
#print axioms totalCost_le_of_potentialCertificate
#print axioms rootedCutCondition_totalCost_le_of_potentialCertificate
#print axioms rlBudget_endpointBlock_retraction_le
#print axioms residual_series_gate_or_endpoint_pair
#print axioms IsGeodesic.corridorIndexSet_card_le_twice_slack
#print axioms IsGeodesic.length_le_twice_slack_add_two_of_interior_nonbridge
#print axioms IsGeodesic.length_le_twice_slack_of_all_nonbridge
#print axioms IsGeodesic.slack_at_least_four_of_large_bridge_free_corridor
#print axioms IsGeodesic.slack_at_least_five_of_large_all_nonbridge_corridor

end Erdos23GapGBJoint
