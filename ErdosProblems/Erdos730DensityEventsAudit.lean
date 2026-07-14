/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730DensityEvents

/-!
# Erdős 730 finite density events: kernel audit

The audit expands both the bad-parameter predicate and the witnessed event
count.  Its final statement is the literal finite `Bad(X) ≤ E(X)` union
bound, with no asymptotic or analytic assumption.
-/

namespace Erdos730
namespace DensityEventsAudit

open ConsecutiveTransition FullDensityCore DensityEvents

noncomputable section

local instance : DecidablePred (fun w : ObstructionWitness =>
    DropObstruction (n w.1) w.2.1 w.2.2.1 w.2.2.2) :=
  fun _ => Classical.propDecidable _

local instance : DecidablePred (fun w : ObstructionWitness =>
    EntryObstruction (n w.1) w.2.1 w.2.2.1 w.2.2.2) :=
  fun _ => Classical.propDecidable _

/-- Independent membership audit for the finite bad-parameter set. -/
theorem bad_membership_expanded_audit {X x : ℕ} :
    x ∈ badParametersUpTo X ↔
      1 ≤ x ∧ x ≤ X ∧
      (n x).centralBinom.primeFactors ≠
        (n x + 1).centralBinom.primeFactors := by
  constructor
  · intro hx
    rcases mem_badParametersUpTo.mp hx with ⟨hxrange, hnot⟩
    rcases mem_parameterRange.mp hxrange with ⟨hx1, hxX⟩
    refine ⟨hx1, hxX, ?_⟩
    intro heq
    exact hnot ⟨hx1, heq⟩
  · rintro ⟨hx1, hxX, hne⟩
    apply mem_badParametersUpTo.mpr
    refine ⟨mem_parameterRange.mpr ⟨hx1, hxX⟩, ?_⟩
    intro hgood
    exact hne hgood.2

/-- Independent audit that a bad parameter is covered by a concrete
quadruple in one of the two finite witness sets. -/
theorem pointwise_witness_coverage_audit
    {X x : ℕ} (hx : x ∈ badParametersUpTo X) :
    (∃ p a c,
      (x, (p, (a, c))) ∈ dropWitnessesUpTo X ∧
      DropObstruction (n x) p a c) ∨
    (∃ p a c,
      (x, (p, (a, c))) ∈ entryWitnessesUpTo X ∧
      EntryObstruction (n x) p a c) := by
  rcases bad_mem_dropParameters_or_entryParameters hx with hdrop | hentry
  · rw [dropParametersUpTo, Finset.mem_image] at hdrop
    rcases hdrop with ⟨w, hw, hwx⟩
    rcases w with ⟨wx, ⟨p, ⟨a, c⟩⟩⟩
    simp only [witnessParameter] at hwx
    subst x
    exact Or.inl ⟨p, a, c, hw, (mem_dropWitnessesUpTo.mp hw).2⟩
  · rw [entryParametersUpTo, Finset.mem_image] at hentry
    rcases hentry with ⟨w, hw, hwx⟩
    rcases w with ⟨wx, ⟨p, ⟨a, c⟩⟩⟩
    simp only [witnessParameter] at hwx
    subst x
    exact Or.inr ⟨p, a, c, hw, (mem_entryWitnessesUpTo.mp hw).2⟩

/-- The exact finite union bound with the witness sets expanded as filters
of a finite quadruple box. -/
theorem finite_bad_union_bound_audit (X : ℕ) :
    ((Finset.Icc 1 X).filter fun x =>
      ¬(1 ≤ x ∧
        (n x).centralBinom.primeFactors =
          (n x + 1).centralBinom.primeFactors)).card ≤
      ((witnessBox X).filter fun (w : ObstructionWitness) =>
        DropObstruction (n w.1) w.2.1 w.2.2.1 w.2.2.2).card +
      ((witnessBox X).filter fun (w : ObstructionWitness) =>
        EntryObstruction (n w.1) w.2.1 w.2.2.1 w.2.2.2).card := by
  simpa [badParametersUpTo, parameterRange, GoodParameter,
    dropWitnessesUpTo, entryWitnessesUpTo, witnessParameter,
    witnessPrime, witnessExponent, witnessCofactor] using
    bad_card_le_witnessed_obstruction_count X

/-- Independent partition audit: Good and Bad are complementary and have
exactly `X` parameters in total, including the boundary `X=0`. -/
theorem good_bad_exact_count_audit (X : ℕ) :
    (goodParametersUpTo X).card + (badParametersUpTo X).card = X := by
  exact good_card_add_bad_card X

/-- Independent boundary audit for the finite witness box. -/
theorem witness_box_bounds_audit
    {X : ℕ} {w : ObstructionWitness} :
    w ∈ witnessBox X ↔
      1 ≤ w.1 ∧ w.1 ≤ X ∧
      w.2.1 < 2 * n X + 2 ∧
      w.2.2.1 < 2 * n X + 2 ∧
      w.2.2.2 < 2 * n X + 2 := by
  rw [mem_witnessBox, mem_parameterRange]
  simp only [witnessBound]
  constructor
  · rintro ⟨⟨hx1, hxX⟩, hp, ha, hc⟩
    exact ⟨hx1, hxX, hp, ha, hc⟩
  · rintro ⟨hx1, hxX, hp, ha, hc⟩
    exact ⟨⟨hx1, hxX⟩, hp, ha, hc⟩

/-- Audit of the exact four-range cardinal partition.  The assumptions and
endpoint placement are explicit, while the cutoffs remain arbitrary. -/
theorem four_range_cardinality_audit
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    (dropWitnessesUpTo X).card + (entryWitnessesUpTo X).card =
      (higherPowerWitnessesUpTo X).card +
        ((smallPrimeWitnessesUpTo X smallCut).card +
          ((transitionPrimeWitnessesUpTo X smallCut topCut).card +
            (topPrimeWitnessesUpTo X topCut).card)) := by
  exact witnessed_obstruction_count_card_fourRange X smallCut topCut hcuts

/-- Independent named audit of the fact that drop and entry quadruples do
not overlap. -/
theorem drop_entry_disjoint_audit (X : ℕ) :
    Disjoint (dropWitnessesUpTo X) (entryWitnessesUpTo X) := by
  exact drop_entry_witnesses_disjoint X

#print axioms bad_membership_expanded_audit
#print axioms pointwise_witness_coverage_audit
#print axioms finite_bad_union_bound_audit
#print axioms good_bad_exact_count_audit
#print axioms witness_box_bounds_audit
#print axioms four_range_cardinality_audit
#print axioms drop_entry_disjoint_audit

end

end DensityEventsAudit
end Erdos730
