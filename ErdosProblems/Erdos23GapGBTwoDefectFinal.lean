/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair, OpenAI Codex
-/
import ErdosProblems.Erdos23GapGBTwoDefectAlignment

/-!
# Erdős 23 G-B: final graph constructors on the two-defect boundary

This module closes the four canonical graph shapes left after the exact
`d = 2s-2` deficit classification.
-/

namespace Erdos23GapGBTwoDefectFinal

open scoped BigOperators
open SimpleGraph
open Erdos23GapGA
open Erdos23GapGBSeries
open Erdos23GapGBJoint
open Erdos23GapGBEqualityBoundary
open Erdos23GapGBOneDefect
open Erdos23GapGBOneDefectAlignment
open Erdos23GapGBOneDefectIntervals
open Erdos23GapGBBinaryLayers
open Erdos23GapGBLayerCapacity
open Erdos23GapGBTwoDefect
open Erdos23GapGBTwoDefectAlignment

/-- A positive finite level set of size `s` that meets every one of the `d`
consecutive level gaps at the two-defect row has at most two adjacent pairs.
The endpoint level `d` is allowed, which is needed for the mass/span tip. -/
theorem activeLevelSet_high_card_le_two
    (E : Finset ℕ) (s d : ℕ)
    (hd : d = 2 * s - 2)
    (hsub : E ⊆ Finset.range (d + 1))
    (hpos : ∀ k ∈ E, 1 ≤ k)
    (hcard : E.card = s)
    (hactive : ∀ r < d, r ∈ E ∨ r + 1 ∈ E) :
    ((Finset.range d).filter fun r => r ∈ E ∧ r + 1 ∈ E).card ≤ 2 := by
  classical
  let predE := E.image Nat.pred
  have hpredSub : predE ⊆ Finset.range d := by
    intro r hr
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hr
    have heRange := Finset.mem_range.mp (hsub he)
    have hePos := hpos e he
    have hsucc : Nat.pred e + 1 = e := Nat.succ_pred_eq_of_pos (by omega)
    exact Finset.mem_range.mpr (by omega)
  have hrangeSub : Finset.range d ⊆ E ∪ predE := by
    intro r hr
    have hrlt := Finset.mem_range.mp hr
    rcases hactive r hrlt with hrE | hr1E
    · exact Finset.mem_union_left predE hrE
    · apply Finset.mem_union_right E
      exact Finset.mem_image.mpr ⟨r + 1, hr1E, by simp⟩
  have hpredInj : Set.InjOn Nat.pred (E : Set ℕ) := by
    intro a ha b hb hab
    have haPos := hpos a ha
    have hbPos := hpos b hb
    have haSucc : Nat.pred a + 1 = a := Nat.succ_pred_eq_of_pos (by omega)
    have hbSucc : Nat.pred b + 1 = b := Nat.succ_pred_eq_of_pos (by omega)
    omega
  have hcardPred : predE.card = E.card := by
    exact Finset.card_image_iff.mpr hpredInj
  have hcardUnion := Finset.card_union_add_card_inter E predE
  have hrangeCardLe : d ≤ (E ∪ predE).card := by
    simpa using Finset.card_le_card hrangeSub
  have hinterLe : (E ∩ predE).card ≤ 2 := by
    rw [hcardPred, hcard] at hcardUnion
    omega
  have hfilterEq :
      (Finset.range d).filter (fun r => r ∈ E ∧ r + 1 ∈ E) =
        E ∩ predE := by
    ext r
    constructor
    · intro hr
      have hrData := Finset.mem_filter.mp hr
      exact Finset.mem_inter.mpr
        ⟨hrData.2.1,
          Finset.mem_image.mpr ⟨r + 1, hrData.2.2, by simp⟩⟩
    · intro hr
      have hrData := Finset.mem_inter.mp hr
      obtain ⟨e, heE, hePred⟩ := Finset.mem_image.mp hrData.2
      have hePos := hpos e heE
      have heSucc : Nat.pred e + 1 = e := Nat.succ_pred_eq_of_pos (by omega)
      have her : e = r + 1 := by omega
      have hrRange := hpredSub hrData.2
      exact Finset.mem_filter.mpr
        ⟨hrRange, hrData.1, by simpa [her] using heE⟩
  rw [hfilterEq]
  exact hinterLe

/-- If both endpoints have the ordinary corridor anchors immediately below
and above their rooted levels, every legal same-side pair is level aligned. -/
theorem IsGeodesic.levelAligned_of_twoSidedAnchors
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ x y : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (hP : IsGeodesic P)
    (hxNext : G.dist w x < P.length →
      G.Adj x (P.getVert (G.dist w x + 1)))
    (hxPrev : 0 < G.dist w x →
      G.Adj (P.getVert (G.dist w x - 1)) x)
    (hyNext : G.dist w y < P.length →
      G.Adj y (P.getVert (G.dist w y + 1)))
    (hyPrev : 0 < G.dist w y →
      G.Adj (P.getVert (G.dist w y - 1)) y)
    (hxBound : G.dist w x ≤ P.length)
    (hyBound : G.dist w y ≤ P.length)
    (hlevelEven : Even (Nat.dist (G.dist w x) (G.dist w y)))
    (hlegal : 4 ≤ G.dist x y) :
    G.dist x y = Nat.dist (G.dist w x) (G.dist w y) := by
  have hsame : G.dist w x = G.dist w y → G.dist x y ≤ 2 := by
    intro heq
    by_cases hzero : G.dist w x = 0
    · have hxw : x = w :=
        ((hconn.dist_eq_zero_iff (u := w) (v := x)).mp hzero).symm
      have hyzero : G.dist w y = 0 := by omega
      have hyw : y = w :=
        ((hconn.dist_eq_zero_iff (u := w) (v := y)).mp hyzero).symm
      subst x
      subst y
      simp
    · have hxAnchor := hxPrev (by omega)
      have hyAnchor := hyPrev (by omega)
      have hs : G.dist w x - 1 = G.dist w y - 1 := by omega
      rw [hs] at hxAnchor
      have hxDist : G.dist x (P.getVert (G.dist w y - 1)) = 1 :=
        dist_eq_one_iff_adj.mpr hxAnchor.symm
      have hyDist : G.dist (P.getVert (G.dist w y - 1)) y = 1 :=
        dist_eq_one_iff_adj.mpr hyAnchor
      have htri := hconn.dist_triangle
        (u := x) (v := P.getVert (G.dist w y - 1)) (w := y)
      omega
  have hlower := bfsLevel_natDist_le hconn w x y
  rcases lt_trichotomy (G.dist w x) (G.dist w y) with hlt | heq | hgt
  · have heven : Even (G.dist w y - G.dist w x) := by
      simpa [Nat.dist_eq_sub_of_le hlt.le] using hlevelEven
    obtain ⟨q, hq⟩ := heven
    have hgap : G.dist w x + 2 ≤ G.dist w y := by omega
    have hupper := IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
      hconn hP hgap hyBound (hxNext (by omega)) (hyPrev (by omega))
    rw [Nat.dist_eq_sub_of_le hlt.le] at hlower ⊢
    omega
  · have hclose := hsame heq
    omega
  · have heven : Even (G.dist w x - G.dist w y) := by
      simpa [Nat.dist_eq_sub_of_le_right hgt.le] using hlevelEven
    obtain ⟨q, hq⟩ := heven
    have hgap : G.dist w y + 2 ≤ G.dist w x := by omega
    have hupper := IsGeodesic.dist_le_levelSub_of_adjacent_corridorAnchors
      hconn hP hgap hxBound (hyNext (by omega)) (hxPrev (by omega))
    rw [SimpleGraph.dist_comm] at hupper
    rw [Nat.dist_eq_sub_of_le_right hgt.le] at hlower ⊢
    omega

/-- A size-two component of span two is a doubled diamond vertex together
with one tip.  The doubled vertex is on level `l+1` and the tip on `l+2`. -/
theorem IsGeodesic.pair_spanTwo_geometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {w x₀ : V} {P : G.Walk w x₀}
    (hconn : G.Connected) (color : G.Coloring Bool) (hP : IsGeodesic P)
    (C : OffCorridorComponent P) (l : ℕ)
    (hsize : (offCorridorComponentFinset C).card = 2)
    (hinterval : offCorridorComponentIntervalEdges P C =
      Finset.Ico l (l + 2)) :
    ∃ anchor tip : V,
      offCorridorComponentFinset C = {anchor, tip} ∧
      anchor ≠ tip ∧ G.Adj anchor tip ∧
      G.Adj anchor (P.getVert l) ∧
      G.Adj anchor (P.getVert (l + 2)) ∧
      G.dist w anchor = l + 1 ∧ G.dist w tip = l + 2 := by
  classical
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hsize
  have hAdjAB : G.Adj a b :=
    offCorridorComponent_adj_of_finset_eq_pair C hab hset
  obtain ⟨hleft, hright, hbounds⟩ :=
    attachment_extrema_of_interval_eq_length P C l 2 (by omega) hinterval
  obtain ⟨hlLength, cL, hcL, hAdjL⟩ :=
    (mem_offCorridorAttachmentIndices P C l).1 hleft
  obtain ⟨hrLength, cR, hcR, hAdjR⟩ :=
    (mem_offCorridorAttachmentIndices P C (l + 2)).1 hright
  have hcEq : cL = cR := by
    by_contra hne
    have hcLcases : cL = a ∨ cL = b := by simpa [hset] using hcL
    have hcRcases : cR = a ∨ cR = b := by simpa [hset] using hcR
    have hAdjLR : G.Adj cL cR := by
      rcases hcLcases with rfl | rfl <;> rcases hcRcases with rfl | rfl
      · exact (hne rfl).elim
      · exact hAdjAB
      · exact hAdjAB.symm
      · exact (hne rfl).elim
    have hp₁ := color.valid (P.adj_getVert_succ (i := l) (by omega))
    have hp₂ := color.valid (P.adj_getVert_succ (i := l + 1) (by omega))
    have hcl := color.valid hAdjL
    have hcr := color.valid hAdjR
    have hlr := color.valid hAdjLR
    cases h0 : color (P.getVert l) <;>
      cases h1 : color (P.getVert (l + 1)) <;>
      cases h2 : color (P.getVert (l + 2)) <;>
      cases hL : color cL <;>
      cases hR : color cR <;>
      simp_all
  subst cR
  have hcLcases : cL = a ∨ cL = b := by simpa [hset] using hcL
  obtain ⟨tip, hcomponent, hne, hAdjAT⟩ :
      ∃ tip : V, offCorridorComponentFinset C = {cL, tip} ∧
        cL ≠ tip ∧ G.Adj cL tip := by
    rcases hcLcases with hca | hcb
    · subst cL
      exact ⟨b, hset, hab, hAdjAB⟩
    · subst cL
      exact ⟨a, by simpa [Finset.pair_comm] using hset,
        hab.symm, hAdjAB.symm⟩
  have hleftLevel : G.dist w (P.getVert l) = l := by
    simpa using hP.dist_getVert_eq_sub (i := 0) (j := l) (by omega) hlLength
  have hrightLevel : G.dist w (P.getVert (l + 2)) = l + 2 := by
    simpa using hP.dist_getVert_eq_sub (i := 0) (j := l + 2)
      (by omega) hrLength
  have hAdjLDist : G.dist (P.getVert l) cL = 1 :=
    dist_eq_one_iff_adj.mpr hAdjL.symm
  have hAdjRDist : G.dist cL (P.getVert (l + 2)) = 1 :=
    dist_eq_one_iff_adj.mpr hAdjR
  have hupperA := hconn.dist_triangle (u := w) (v := P.getVert l) (w := cL)
  have hlowerA := hconn.dist_triangle
    (u := w) (v := cL) (w := P.getVert (l + 2))
  have hlevelA : G.dist w cL = l + 1 := by omega
  have htC : tip ∈ offCorridorComponentFinset C := by simp [hcomponent]
  have htComp : tip ∈ C := (mem_offCorridorComponentFinset C).1 htC
  obtain ⟨htOffSet, htCompEq⟩ := ComponentCompl.mem_supp_iff.mp htComp
  have htNot : tip ∉ P.support := by simpa [supportFinset] using htOffSet
  have hneighborLower : ∀ y : V, G.Adj tip y → l + 1 ≤ G.dist w y := by
    intro y hty
    by_cases hySupport : y ∈ P.support
    · let j := P.support.idxOf y
      have hjLength : j ≤ P.length := support_idxOf_le_length P hySupport
      have hjGet : P.getVert j = y := P.getVert_support_idxOf hySupport
      have hjAttach : j ∈ offCorridorAttachmentIndices P C := by
        exact (mem_offCorridorAttachmentIndices P C j).2
          ⟨hjLength, tip, htC, by simpa [hjGet] using hty⟩
      have hjBounds := hbounds j hjAttach
      have hjLevel : G.dist w y = j := by
        rw [← hjGet]
        exact IsGeodesic.rootDist_getVert hP hjLength
      have hjNe : j ≠ l := by
        intro hjEq
        have htipLeft : G.Adj tip (P.getVert l) := by
          simpa [hjGet, hjEq] using hty
        have hat := color.valid hAdjAT
        have hal := color.valid hAdjL
        have htl := color.valid htipLeft
        cases ht : color tip <;>
          cases ha : color cL <;>
          cases hp : color (P.getVert l) <;>
          simp_all
      omega
    · have hcompEq := offCorridorComponentOf_eq_of_adj P htNot hySupport hty
      have htOwn : offCorridorComponentOf P tip htNot = C := by
        simpa [offCorridorComponentOf, supportFinset] using htCompEq
      have hyOwn : y ∈ offCorridorComponentFinset
          (offCorridorComponentOf P y hySupport) :=
        mem_offCorridorComponentOf P hySupport
      have hyC : y ∈ offCorridorComponentFinset C := by
        simpa [← htOwn, hcompEq] using hyOwn
      have hyCases : y = cL ∨ y = tip := by simpa [hcomponent] using hyC
      rcases hyCases with rfl | rfl
      · omega
      · exact (G.loopless.irrefl tip hty).elim
  have htUpper : G.dist w tip ≤ l + 2 := by
    have hATDist : G.dist cL tip = 1 := dist_eq_one_iff_adj.mpr hAdjAT
    have htri := hconn.dist_triangle (u := w) (v := cL) (w := tip)
    omega
  have hwSupport : w ∈ P.support := by simpa using P.getVert_mem_support 0
  have htw : tip ≠ w := by
    intro h
    subst tip
    exact htNot hwSupport
  obtain ⟨Q, hQ⟩ := hconn.exists_walk_length_eq_dist w tip
  have hQnotNil : ¬ Q.Nil := by
    intro hnil
    have hwt : w = tip := hnil.eq
    exact htw hwt
  have hpenAdj : G.Adj tip Q.penultimate := (Q.adj_penultimate hQnotNil).symm
  have hpenLower := hneighborLower Q.penultimate hpenAdj
  have hdrop : G.dist w Q.penultimate ≤ Q.dropLast.length := dist_le Q.dropLast
  have hlen := Q.length_dropLast_add_one hQnotNil
  have htLower : l + 2 ≤ G.dist w tip := by omega
  have htLevel : G.dist w tip = l + 2 := by omega
  exact ⟨cL, tip, hcomponent, hne, hAdjAT, hAdjL, hAdjR,
    hlevelA, htLevel⟩

#print axioms activeLevelSet_high_card_le_two
#print axioms IsGeodesic.levelAligned_of_twoSidedAnchors
#print axioms IsGeodesic.pair_spanTwo_geometry

end Erdos23GapGBTwoDefectFinal
