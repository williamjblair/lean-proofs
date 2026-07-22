/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.EvenK.K32.CandidateCover

/-! # Erdős 686: unconditional closure of the row `k=32` -/

namespace Erdos686
namespace Erdos686Variant

private lemma k32_allowed_int
    {p : ℕ} [NeZero p] (A : ZMod p → Bool)
    (hallow : ∀ w v : ZMod p,
      evenTable32S w = 4 * evenTable32S v →
        A (evenTable32T w - 2 * evenTable32T v) = true)
    {w v m : ℤ} (hS : evenTable32S w = 4 * evenTable32S v)
    (hm : m = evenTable32T w - 2 * evenTable32T v) :
    A (m : ZMod p) = true := by
  have hSp : evenTable32S (w : ZMod p) =
      4 * evenTable32S (v : ZMod p) := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) hS
    simpa [evenTable32S] using h
  subst m
  simpa [evenTable32T] using hallow (w : ZMod p) (v : ZMod p) hSp

private theorem even32_all_candidate_conditions
    {w v : ℤ} {t : ℕ}
    (hS : evenTable32S w = 4 * evenTable32S v)
    (ht : -(3221225472 * (t : ℤ)) = evenTable32T w - 2 * evenTable32T v) :
    even32CandidateAllowed t = true := by
  have h17 := k32_allowed_int even32A17 even32_allowed_17 hS ht
  have h521 := k32_allowed_int even32A521 even32_allowed_521 hS ht
  have h509 := k32_allowed_int even32A509 even32_allowed_509 hS ht
  have h491 := k32_allowed_int even32A491 even32_allowed_491 hS ht
  have h457 := k32_allowed_int even32A457 even32_allowed_457 hS ht
  have h463 := k32_allowed_int even32A463 even32_allowed_463 hS ht
  have h487 := k32_allowed_int even32A487 even32_allowed_487 hS ht
  have h383 := k32_allowed_int even32A383 even32_allowed_383 hS ht
  have h449 := k32_allowed_int even32A449 even32_allowed_449 hS ht
  have h439 := k32_allowed_int even32A439 even32_allowed_439 hS ht
  have h499 := k32_allowed_int even32A499 even32_allowed_499 hS ht
  have h443 := k32_allowed_int even32A443 even32_allowed_443 hS ht
  have h7 := k32_allowed_int even32A7 even32_allowed_7 hS ht
  have h431 := k32_allowed_int even32A431 even32_allowed_431 hS ht
  have h397 := k32_allowed_int even32A397 even32_allowed_397 hS ht
  have h467 := k32_allowed_int even32A467 even32_allowed_467 hS ht
  have h409 := k32_allowed_int even32A409 even32_allowed_409 hS ht
  rw [even32CandidateAllowed, Bool.and_eq_true]
  refine ⟨h17, ?_⟩
  rw [even32CandidateAllowedRest]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h521, h509⟩, h491⟩, h457⟩, h463⟩,
    h487⟩, h383⟩, h449⟩, h439⟩, h499⟩, h443⟩, h7⟩, h431⟩, h397⟩,
    h467⟩, h409⟩

/-- The row `k=32` has no quotient-four gap solution once `d≥32`. -/
theorem no_gap_solution_four_even_thirtytwo {n d : ℕ} (hd : 32 ≤ d) :
    blockProduct 32 (n + d) ≠ 4 * blockProduct 32 n :=
  no_gap_solution_four_even_thirtytwo_of_cert
    even32_all_candidate_conditions even32_candidate_cover hd

#print axioms no_gap_solution_four_even_thirtytwo

end Erdos686Variant
end Erdos686
