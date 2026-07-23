import Mathlib
import Research.Statement
import Research.Growth
import Research.Negative
import Research.GrowthPartition
import Research.PhaseShellDecomposition
import Research.CanonicalCountableReserve
import Research.ReserveComplementPhase
import Research.CountableConvergencePhases
import Research.PowerShellCountablePhases

namespace Erdos254.UniversalCorrectionPartition

open Filter
open scoped BigOperators
open Erdos254
open Erdos254.GrowthPartition
open Erdos254.PhaseShellDecomposition
open Erdos254.CanonicalCountableReserve
open Erdos254.ReserveGrowth
open Erdos254.ReserveComplementPhase
open Erdos254.CountableConvergencePhases
open Erdos254.PowerShellCountablePhases

noncomputable section

/-- A fixed quarter of each power shell, selected by increasing rank. -/
def seedCorrection (A : Set ℕ) : Set ℕ := colorClass A 0

/-- Everything outside the seed correction class. -/
def seedReserve (A : Set ℕ) : Set ℕ := A \ seedCorrection A

lemma powerShell_colorClass (A : Set ℕ) (j c : ℕ) (_hc : c < 4) :
    powerShell (colorClass A c) j = balancedPart (powerShell A j) c := by
  classical
  ext n
  constructor
  · intro hn
    have hndata := Finset.mem_filter.mp hn
    obtain ⟨l, hnl⟩ := hndata.2
    have hnAl := balancedPart_subset (powerShell A l) c hnl
    have hnAj : n ∈ powerShell A j := by
      exact Finset.mem_filter.mpr ⟨hndata.1, (Finset.mem_filter.mp hnAl).2⟩
    have hjl : j = l := powerShell_index_unique A hnAj hnAl
    simpa [hjl] using hnl
  · intro hn
    have hnA := balancedPart_subset (powerShell A j) c hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnA).1, ⟨j, hn⟩⟩

lemma shellCount_power_eq_powerShell_card (C : Set ℕ) (j : ℕ) :
    Erdos254.shellCount C (2 ^ j) = (powerShell C j).card := by
  simp [Erdos254.shellCount, powerShell, pow_succ, mul_comm]

lemma colorClass_powerShell_card_tendsto
    (A : Set ℕ) (c : ℕ) (hc : c < 4)
    (hdyadic : Tendsto (Erdos254.dyadicIncrement A) atTop atTop) :
    Tendsto (fun j => (powerShell (colorClass A c) j).card) atTop atTop := by
  classical
  rw [tendsto_atTop]
  intro K
  have hmuch := Erdos254.dyadic_tendsto_eventually_many A hdyadic (4 * K)
  have hpowers :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by decide)).eventually hmuch
  filter_upwards [hpowers] with j hj
  rw [powerShell_colorClass A j c hc]
  apply balancedPart_card_ge (powerShell A j) c K hc
  simpa [shellCount_power_eq_powerShell_card] using hj

lemma seedCorrection_powerShell_card_tendsto
    (A : Set ℕ)
    (hdyadic : Tendsto (Erdos254.dyadicIncrement A) atTop atTop) :
    Tendsto (fun j => (powerShell (seedCorrection A) j).card) atTop atTop :=
  colorClass_powerShell_card_tendsto A 0 (by omega) hdyadic

lemma color_one_subset_seedReserve (A : Set ℕ) :
    colorClass A 1 ⊆ seedReserve A := by
  classical
  intro n hn1
  have hnA : n ∈ A := by
    obtain ⟨j, hnj⟩ := hn1
    exact (Finset.mem_filter.mp
      (balancedPart_subset (powerShell A j) 1 hnj)).2
  refine ⟨hnA, ?_⟩
  intro hn0
  exact Set.disjoint_left.mp (colorClass_pairwise_disjoint A (by omega)) hn0 hn1

lemma seedReserve_powerShell_card_tendsto
    (A : Set ℕ)
    (hdyadic : Tendsto (Erdos254.dyadicIncrement A) atTop atTop) :
    Tendsto (fun j => (powerShell (seedReserve A) j).card) atTop atTop := by
  classical
  have h1 := colorClass_powerShell_card_tendsto A 1 (by omega) hdyadic
  rw [tendsto_atTop] at h1 ⊢
  intro K
  filter_upwards [h1 K] with j hj
  apply hj.trans
  apply Finset.card_le_card
  intro n hn
  have hn1 : n ∈ colorClass A 1 :=
    (Finset.mem_filter.mp hn).2
  have hnR := color_one_subset_seedReserve A hn1
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, hnR⟩

lemma seedCorrection_canonical_power_tendsto
    (A : Set ℕ)
    (hdyadic : Tendsto (Erdos254.dyadicIncrement A) atTop atTop) :
    Tendsto (fun j => Erdos254.shellCount (seedCorrection A) (2 ^ j))
      atTop atTop := by
  simpa only [shellCount_power_eq_powerShell_card] using
    seedCorrection_powerShell_card_tendsto A hdyadic

lemma phasePartialSum_split (A C : Set ℕ) (hCA : C ⊆ A)
    (θ : ℝ) (N : ℕ) :
    phasePartialSum A θ N =
      phasePartialSum C θ N + phasePartialSum (A \ C) θ N := by
  classical
  let I := Finset.Icc 1 N
  let f : ℕ → ℝ := fun n => nearestIntegerDistance (θ * (n : ℝ))
  have hpart := Finset.sum_filter_add_sum_filter_not
    (I.filter fun n => n ∈ A) (fun n => n ∈ C) f
  have hleft : ((I.filter fun n => n ∈ A).filter fun n => n ∈ C) =
      I.filter (fun n => n ∈ C) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hnI, hnA⟩, hnC⟩
      exact ⟨hnI, hnC⟩
    · rintro ⟨hnI, hnC⟩
      exact ⟨⟨hnI, hCA hnC⟩, hnC⟩
  have hright : ((I.filter fun n => n ∈ A).filter fun n => n ∉ C) =
      I.filter (fun n => n ∈ A \ C) := by
    ext n
    simp only [Finset.mem_filter, Set.mem_sdiff]
    tauto
  rw [hleft, hright] at hpart
  simpa [phasePartialSum, I, f] using hpart.symm

lemma phase_diverges_on_seedReserve_of_seed_bounded
    (A : Set ℕ) (θ : ℝ)
    (hA : Tendsto (phasePartialSum A θ) atTop atTop)
    (hbound : ∃ B : ℝ, ∀ N,
      phasePartialSum (seedCorrection A) θ N ≤ B) :
    Tendsto (phasePartialSum (seedReserve A) θ) atTop atTop := by
  classical
  obtain ⟨B, hB⟩ := hbound
  rw [tendsto_atTop]
  intro b
  have hlarge := tendsto_atTop.1 hA (b + B)
  filter_upwards [hlarge] with N hN
  have hsplit := phasePartialSum_split A (seedCorrection A)
    (fun n hn => by
      obtain ⟨j, hnj⟩ := hn
      exact (Finset.mem_filter.mp
        (balancedPart_subset (powerShell A j) 0 hnj)).2) θ N
  dsimp [seedReserve]
  linarith [hB N]

lemma phasePartialSum_mono_set {C D : Set ℕ} (hCD : C ⊆ D)
    (θ : ℝ) (N : ℕ) :
    phasePartialSum C θ N ≤ phasePartialSum D θ N := by
  classical
  simp only [phasePartialSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hCD hn.2⟩
  · intro n hnD hnC
    exact nd_nonneg _

lemma phase_divergence_mono_set {C D : Set ℕ} (hCD : C ⊆ D)
    (θ : ℝ) (hC : Tendsto (phasePartialSum C θ) atTop atTop) :
    Tendsto (phasePartialSum D θ) atTop atTop := by
  rw [tendsto_atTop] at hC ⊢
  intro b
  filter_upwards [hC b] with N hN
  exact hN.trans (phasePartialSum_mono_set hCD θ N)

/-- Core extraction theorem: the original hypotheses yield a growing
power-shell reserve whose actual complement retains phase divergence at every
nonzero phase, not merely at a prescribed list. -/
theorem exists_universally_phase_protected_growing_reserve
    (A : Set ℕ)
    (hdyadic : Tendsto (Erdos254.dyadicIncrement A) atTop atTop)
    (hphase : ∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
      Tendsto (phasePartialSum A θ) atTop atTop) :
    ∃ R : ℕ → Finset ℕ,
      (∀ j, R j ⊆ powerShell (seedReserve A) j) ∧
      Tendsto (fun j => (R j).card) atTop atTop ∧
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 1 →
        Tendsto (phasePartialSum (A \ reserveSet R) θ) atTop atTop) ∧
      (∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ,
        (∀ b ∈ t, b ∈ reserveSet R) ∧
        (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b) + K) := by
  classical
  let C₀ := seedCorrection A
  let B₀ := seedReserve A
  let H : Set ℝ := {θ | θ ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∃ B : ℝ, ∀ N, phasePartialSum C₀ θ N ≤ B}
  have hHcount : H.Countable := by
    refine (countable_bounded_phase_set_of_powerShells
      (seedCorrection_canonical_power_tendsto A hdyadic)).mono ?_
    intro θ hθ
    exact ⟨⟨hθ.1.1.le, hθ.1.2.le⟩, hθ.2⟩
  have hBcard : Tendsto (fun j => (powerShell B₀ j).card) atTop atTop :=
    seedReserve_powerShell_card_tendsto A hdyadic
  by_cases hHne : H.Nonempty
  · obtain ⟨θseq, hθrange⟩ := hHcount.exists_eq_range hHne
    have hθmem : ∀ i, θseq i ∈ H := by
      intro i
      rw [hθrange]
      exact ⟨i, rfl⟩
    let w : ℕ → ℕ → ℝ := fun i n =>
      nearestIntegerDistance (θseq i * (n : ℝ))
    have hw : ∀ i j n, n ∈ powerShell B₀ j → 0 ≤ w i n := by
      intro i j n hn
      exact nd_nonneg _
    have hBphase : ∀ i, Tendsto (phasePartialSum B₀ (θseq i)) atTop atTop := by
      intro i
      exact phase_diverges_on_seedReserve_of_seed_bounded A (θseq i)
        (hphase (θseq i) (hθmem i).1)
        (hθmem i).2
    have hdiv : ∀ i, Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ∑ n ∈ powerShell B₀ j, w i n) atTop atTop := by
      intro i
      exact phase_divergence_implies_powerShell_divergence B₀ (θseq i)
        (hBphase i)
    obtain ⟨R, hRsub, hRcard, hRkeep, hRsynd⟩ :=
      exists_eventual_syndetic_reserve_preserving_countable_divergence
        B₀ w hw hBcard hdiv
    refine ⟨R, hRsub, hRcard, ?_, hRsynd⟩
    intro θ hθ
    by_cases hθH : θ ∈ H
    · rw [hθrange] at hθH
      obtain ⟨i, hi⟩ := hθH
      subst θ
      obtain ⟨J, hrem⟩ := hRkeep i
      have hBcomp := complement_phase_diverges_of_shell_remainder
        B₀ R hRsub (θseq i) J hrem
      apply phase_divergence_mono_set (C := B₀ \ reserveSet R)
        (D := A \ reserveSet R) _ (θseq i) hBcomp
      intro n hn
      exact ⟨hn.1.1, hn.2⟩
    · have hCdiv : Tendsto (phasePartialSum C₀ θ) atTop atTop := by
        rw [phasePartialSum_tendsto_iff_unbounded]
        intro b
        by_contra hno
        have hbnd : ∀ N, phasePartialSum C₀ θ N ≤ b := by
          intro N
          exact le_of_not_ge fun hb => hno ⟨N, hb⟩
        exact hθH ⟨hθ, b, hbnd⟩
      apply phase_divergence_mono_set (C := C₀)
        (D := A \ reserveSet R) _ θ hCdiv
      intro n hnC
      refine ⟨?_, ?_⟩
      · obtain ⟨j, hnj⟩ := hnC
        exact (Finset.mem_filter.mp
          (balancedPart_subset (powerShell A j) 0 hnj)).2
      · rintro ⟨j, hnR⟩
        have hnB : n ∈ B₀ := (Finset.mem_filter.mp (hRsub j hnR)).2
        exact hnB.2 hnC
  · have hCall : ∀ θ, θ ∈ Set.Ioo (0 : ℝ) 1 →
        Tendsto (phasePartialSum C₀ θ) atTop atTop := by
      intro θ hθ
      rw [phasePartialSum_tendsto_iff_unbounded]
      intro b
      by_contra hno
      have hbnd : ∀ N, phasePartialSum C₀ θ N ≤ b := by
        intro N
        exact le_of_not_ge fun hb => hno ⟨N, hb⟩
      exact hHne ⟨θ, hθ, b, hbnd⟩
    let w : ℕ → ℕ → ℝ := fun _ _ => 1
    have hw : ∀ i j n, n ∈ powerShell B₀ j → 0 ≤ w i n := by
      intro i j n hn
      simp [w]
    have hdiv : ∀ i, Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ∑ n ∈ powerShell B₀ j, w i n) atTop atTop := by
      intro i
      rw [tendsto_atTop]
      intro b
      obtain ⟨J, hJ⟩ := eventually_atTop.1
        (tendsto_atTop.1 hBcard (Nat.ceil (max b 0)))
      filter_upwards [eventually_ge_atTop (J + 1)] with N hN
      have hcardN : Nat.ceil (max b 0) ≤ (powerShell B₀ (N - 1)).card :=
        hJ (N - 1) (by omega)
      have hlast : N - 1 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      calc
        b ≤ (Nat.ceil (max b 0) : ℝ) := by
          exact (le_max_left b 0).trans (Nat.le_ceil _)
        _ ≤ ((powerShell B₀ (N - 1)).card : ℝ) := by exact_mod_cast hcardN
        _ = ∑ n ∈ powerShell B₀ (N - 1), w i n := by simp [w]
        _ ≤ ∑ j ∈ Finset.range N, ∑ n ∈ powerShell B₀ j, w i n := by
          exact Finset.single_le_sum
            (fun j hj => Finset.sum_nonneg (fun n hn => by simp [w])) hlast
    obtain ⟨R, hRsub, hRcard, hRkeep, hRsynd⟩ :=
      exists_eventual_syndetic_reserve_preserving_countable_divergence
        B₀ w hw hBcard hdiv
    refine ⟨R, hRsub, hRcard, ?_, hRsynd⟩
    intro θ hθ
    apply phase_divergence_mono_set (C := C₀)
      (D := A \ reserveSet R) _ θ (hCall θ hθ)
    intro n hnC
    refine ⟨?_, ?_⟩
    · obtain ⟨j, hnj⟩ := hnC
      exact (Finset.mem_filter.mp
        (balancedPart_subset (powerShell A j) 0 hnj)).2
    · rintro ⟨j, hnR⟩
      have hnB : n ∈ B₀ := (Finset.mem_filter.mp (hRsub j hnR)).2
      exact hnB.2 hnC

end

end Erdos254.UniversalCorrectionPartition
