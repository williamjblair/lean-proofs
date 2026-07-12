/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686EvenK28CandidateCover

/-! # Erdős 686: unconditional closure of the row `k=28` -/

namespace Erdos686
namespace Erdos686Variant

private lemma k28_allowed_int
    {p : ℕ} [NeZero p] (A : ZMod p → Bool)
    (hallow : ∀ w v : ZMod p,
      evenTable28S w = 4 * evenTable28S v →
        A (evenTable28T w - 2 * evenTable28T v) = true)
    {w v m : ℤ} (hS : evenTable28S w = 4 * evenTable28S v)
    (hm : m = evenTable28T w - 2 * evenTable28T v) :
    A (m : ZMod p) = true := by
  have hSp : evenTable28S (w : ZMod p) =
      4 * evenTable28S (v : ZMod p) := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) hS
    simpa [evenTable28S] using h
  subst m
  simpa [evenTable28T] using hallow (w : ZMod p) (v : ZMod p) hSp

private theorem even28_all_candidate_conditions
    {w v : ℤ} {t : ℕ}
    (hS : evenTable28S w = 4 * evenTable28S v)
    (ht : -(50176 * (t : ℤ)) = evenTable28T w - 2 * evenTable28T v) :
    even28CandidateAllowed t = true := by
  have h29 := k28_allowed_int even28A29 even28_allowed_29 hS ht
  have h349 := k28_allowed_int even28A349 even28_allowed_349 hS ht
  have h347 := k28_allowed_int even28A347 even28_allowed_347 hS ht
  have h317 := k28_allowed_int even28A317 even28_allowed_317 hS ht
  have h331 := k28_allowed_int even28A331 even28_allowed_331 hS ht
  have h353 := k28_allowed_int even28A353 even28_allowed_353 hS ht
  have h283 := k28_allowed_int even28A283 even28_allowed_283 hS ht
  have h337 := k28_allowed_int even28A337 even28_allowed_337 hS ht
  have h293 := k28_allowed_int even28A293 even28_allowed_293 hS ht
  have h281 := k28_allowed_int even28A281 even28_allowed_281 hS ht
  have h307 := k28_allowed_int even28A307 even28_allowed_307 hS ht
  have h257 := k28_allowed_int even28A257 even28_allowed_257 hS ht
  have h271 := k28_allowed_int even28A271 even28_allowed_271 hS ht
  have h239 := k28_allowed_int even28A239 even28_allowed_239 hS ht
  have h197 := k28_allowed_int even28A197 even28_allowed_197 hS ht
  have h313 := k28_allowed_int even28A313 even28_allowed_313 hS ht
  have h241 := k28_allowed_int even28A241 even28_allowed_241 hS ht
  have h277 := k28_allowed_int even28A277 even28_allowed_277 hS ht
  have h5 := k28_allowed_int even28A5 even28_allowed_5 hS ht
  have h37 := k28_allowed_int even28A37 even28_allowed_37 hS ht
  rw [even28CandidateAllowed, Bool.and_eq_true]
  refine ⟨h29, ?_⟩
  rw [even28CandidateAllowedRest]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h349, h347⟩, h317⟩, h331⟩, h353⟩,
    h283⟩, h337⟩, h293⟩, h281⟩, h307⟩, h257⟩, h271⟩, h239⟩,
    h197⟩, h313⟩, h241⟩, h277⟩, h5⟩, h37⟩

/-- The row `k=28` has no quotient-four gap solution once `d≥28`. -/
theorem no_gap_solution_four_even_twentyeight {n d : ℕ} (hd : 28 ≤ d) :
    blockProduct 28 (n + d) ≠ 4 * blockProduct 28 n :=
  no_gap_solution_four_even_twentyeight_of_cert
    even28_all_candidate_conditions even28_candidate_cover hd

#print axioms no_gap_solution_four_even_twentyeight

end Erdos686Variant
end Erdos686
