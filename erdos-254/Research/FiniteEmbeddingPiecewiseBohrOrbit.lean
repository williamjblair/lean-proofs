import Mathlib
import Research.PiecewiseAssembly

namespace Erdos254.FiniteEmbeddingPiecewiseBohrOrbit

open Filter Topology
open Erdos254.PiecewiseAssembly

noncomputable section

/-- Orbit-point strengthening of F-073: if the original open set contains a
forward orbit point, so does the reassembled open set. -/
theorem piecewise_bohr_of_finite_embedding_orbit
    {T : Type*} [TopologicalSpace T] [T2Space T] [AddCommGroup T]
    [IsTopologicalAddGroup T] [CompactSpace T]
    (a : T) (U : Set T) (hUopen : IsOpen U)
    (u₀ : ℕ) (hu₀ : u₀ • a ∈ U)
    (S : Set ℕ)
    (hembed : ∀ F : Finset ℕ,
      (∀ n ∈ F, n • a ∈ U) →
      ∃ r : ℕ, ∀ n ∈ F, n + r ∈ S) :
    ∃ W : Set T, IsOpen W ∧
      ∃ n₀ : ℕ, n₀ • a ∈ W ∧
      ∃ J : Set ℕ, IsThick J ∧
        ∀ n : ℕ, n ∈ J → n • a ∈ W → n ∈ S := by
  classical
  let F : ℕ → Finset ℕ := fun L =>
    (Finset.range (L + 1)).filter (fun n => n • a ∈ U)
  have hF : ∀ L n, n ∈ F L ↔ n ≤ L ∧ n • a ∈ U := by
    intro L n
    simp [F]
  have hr_exists : ∀ L, ∃ r : ℕ, ∀ n : ℕ,
      n ≤ L → n • a ∈ U → n + r ∈ S := by
    intro L
    obtain ⟨r, hr⟩ := hembed (F L) (fun n hn => (hF L n).mp hn |>.2)
    exact ⟨r, fun n hnL hnU => hr n ((hF L n).mpr ⟨hnL, hnU⟩)⟩
  choose r hr using hr_exists
  let p : Ultrafilter ℕ := Ultrafilter.of atTop
  let y : T := Ultrafilter.extend (fun L => r L • a) p
  have hlim : Tendsto (fun L => r L • a) (↑p : Filter ℕ) (𝓝 y) :=
    ultrafilter_extend_eq_iff.mp rfl
  have hsubEventually :
      ∀ᶠ z : T × T in (𝓝 (u₀ • a + y, y)), z.1 - z.2 ∈ U := by
    apply continuous_sub.continuousAt
    simpa using hUopen.mem_nhds hu₀
  rw [nhds_prod_eq] at hsubEventually
  obtain ⟨pW, hpW, pV, hpV, hpWV⟩ :=
    eventually_prod_iff.mp hsubEventually
  obtain ⟨W, hWsub, hWopen, huW⟩ := eventually_nhds_iff.mp hpW
  have hphaseV : ∀ᶠ L in (↑p : Filter ℕ), pV (r L • a) := hlim hpV
  let I : Set ℕ := {L | pV (r L • a)}
  have hIunbounded : ∀ K : ℕ, ∃ L ∈ I, K ≤ L := by
    intro K
    have hge : ∀ᶠ L : ℕ in (↑p : Filter ℕ), K ≤ L :=
      Ultrafilter.of_le atTop (eventually_ge_atTop K)
    obtain ⟨L, hLI, hLK⟩ := (hphaseV.and hge).exists
    exact ⟨L, hLI, hLK⟩
  let J : Set ℕ := {n | ∃ L ∈ I, ∃ k : ℕ, k ≤ L ∧ n = r L + k}
  have hJthick : IsThick J := by
    intro K
    obtain ⟨L, hLI, hKL⟩ := hIunbounded K
    exact ⟨r L, fun k hk => ⟨L, hLI, k, hk.trans hKL, rfl⟩⟩
  have hlimAdd : Tendsto (fun L => u₀ • a + r L • a)
      (↑p : Filter ℕ) (𝓝 (u₀ • a + y)) := tendsto_const_nhds.add hlim
  have hphaseW : ∀ᶠ L in (↑p : Filter ℕ), u₀ • a + r L • a ∈ W :=
    hlimAdd (hWopen.mem_nhds huW)
  obtain ⟨L₀, hL₀⟩ := hphaseW.exists
  refine ⟨W, hWopen, u₀ + r L₀, ?_, J, hJthick, ?_⟩
  · simpa [add_nsmul] using hL₀
  · intro n hnJ hnW
    obtain ⟨L, hLI, k, hkL, rfl⟩ := hnJ
    have hkphase : k • a ∈ U := by
      change pV (r L • a) at hLI
      have hp := hpWV (hWsub _ hnW) hLI
      simpa [add_nsmul] using hp
    simpa [Nat.add_comm] using hr L k hkL hkphase

end

end Erdos254.FiniteEmbeddingPiecewiseBohrOrbit
