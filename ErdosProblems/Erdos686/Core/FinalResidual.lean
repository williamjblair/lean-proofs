/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.CFTailReduction
import ErdosProblems.Erdos686.Core.ThirdObstructionNonzero
import ErdosProblems.Erdos686.EvenK.K16
import ErdosProblems.Erdos686.EvenK.K18
import ErdosProblems.Erdos686.EvenK.K182024
import ErdosProblems.Erdos686.EvenK.K22.Packed.PackedCover
import ErdosProblems.Erdos686.EvenK.K28
import ErdosProblems.Erdos686.EvenK.K32
import ErdosProblems.Erdos686.Core.EvenTailSupply
import ErdosProblems.Erdos686.Core.SmallPrimeBand
import ErdosProblems.Erdos686.Core.CenteredRatioWindowSharp
import ErdosProblems.Erdos686.Core.CenterComponentLogStrip
import ErdosProblems.Erdos686.Core.LargePrimeGapComponent
import ErdosProblems.Erdos686.Core.HighPrimePowerComponent
import ErdosProblems.Erdos686.Core.PrimePowerBinomialBoundary
import ErdosProblems.Erdos686.Core.LargePrimeSameOwner
import ErdosProblems.Erdos686.Core.LargeOddTwoPrimePell

/-!
# Erdős 686: exact residual after the 2026-07-12 campaign

This module gives one quantified statement packaging the part of the `N = 4`
exclusion not discharged by the new unconditional results.

The odd arm starts only at `10^1000` and is supplied with the complete
all-owner certificate, including nonzero second and third obstructions.  The
large-row arm omits the seven fully closed rows `16,18,20,22,24,28,32`; every remaining
even row is restricted to the finite strip below its constructed Runge
threshold; every parity is restricted to the strict complement `k^2 < 18*d`
of the uniform quadratic strip; and all prime-power lower terms covered by the exact factorial-loss
criterion, together with every large-base prime-power owner whose cofactor
`a` satisfies the exact uniform bound `3707904a ≤ 1218443k`, have been removed.
Every canonical prime-power component at least `k` is forced below its exact
base-sensitive high-component threshold; every large-base component and every
complete cleaned owner bucket is also forced below an explicit square ceiling.
Prime-power boundary rows `k=p^a-1` exclude divisibility of both endpoint
parameters by `p^a` for `p≥5`.  Whole two-large-prime gaps in odd rows carry
the uniform `A=3k+2` Pell and second-lift certificate; its equation-facing composition
theorem proves that the two exact second obstructions cannot both vanish.

The residual statement is not asserted here.  The theorems below prove both
directions of its equivalence with the updated odd-tail and large-smoothness
hypotheses.  Its more restricted-looking premises record the banked results;
they do not make the missing contradiction mathematically weaker.
-/

namespace Erdos686
namespace Erdos686Variant

/-- The single exact residual core left after all unconditional results in
this campaign are composed.  It exposes the banked restrictions explicitly,
but is equivalent to the conjunction of the updated terminal hypotheses. -/
def FinalResidual686Hypothesis : Prop :=
  ∀ k n d : ℕ,
    blockProduct k (n + d) = 4 * blockProduct k n →
    ((k ∈ ({5, 7, 9, 11, 13, 15} : Finset ℕ) ∧
        10 ^ 1000 ≤ d ∧
        Nonempty (AllOwnerAssemblyThirdNonzeroCertificate k n d)) ∨
      (16 ≤ k ∧ k ≤ d ∧
        k ≠ 16 ∧ k ≠ 18 ∧ k ≠ 20 ∧ k ≠ 22 ∧ k ≠ 24 ∧ k ≠ 28 ∧ k ≠ 32 ∧
        1218443 * k * d < 1853952 * n ∧
        k ^ 2 < 18 * d ∧
        (∀ r : ℕ, ∀ hr : 2 ≤ r, k = 2 * r →
          d < max (2 * r)
            (universalEvenTailCoefficientCertificate r hr).threshold) ∧
        (∀ p i A : ℕ, p.Prime → i ∈ Finset.Icc 1 k →
          (k - 1).factorial.factorization p ≤
            (4 : ℕ).factorization p +
              (localBlockCoefficientNat k i).factorization p →
          n + i ≠ p ^ A) ∧
        (∀ p i A a : ℕ, p.Prime → k < p →
          i ∈ Finset.Icc 1 k → 1 ≤ A →
          3707904 * a ≤ 1218443 * k →
          n + i ≠ a * p ^ A) ∧
        (∀ p e : ℕ, p.Prime → 0 < e → k ≤ p → p ^ e ∣ d →
          6 * p ^ (2 * e) < (13 * k - 6) * d + 18 * (k - 1)) ∧
        (∀ p e : ℕ, p.Prime → d.factorization p = e → k ≤ p ^ e →
          (p = 2 →
            24 * 2 ^ (2 * e - highComponentLambda 2 k) <
              (13 * k - 6) * d + 18 * (k - 1)) ∧
          (p = 3 →
            6 * 3 ^ (2 * e - highComponentMuThree k e - 1) <
              (13 * k - 6) * d + 18 * (k - 1)) ∧
          (5 ≤ p →
            6 * p ^ (2 * e - highComponentLambda p k) <
              (13 * k - 6) * d + 18 * (k - 1))) ∧
        (∃ owner : ℕ → ℕ,
          GlobalResidualOwnerAssignment k n d owner ∧
          ∀ i : ℕ, i ∈ Finset.Icc 1 k →
            6 * (globalResidualGroupedLeft k d owner i) ^ 2 <
              (13 * k - 6) * d + 18 * (k - 1)) ∧
        (∀ p a : ℕ, p.Prime → 5 ≤ p → 0 < a →
          k = p ^ a - 1 →
          ¬ p ^ a ∣ n ∧ ¬ p ^ a ∣ n + d) ∧
        (∀ p q e f r : ℕ,
          p.Prime → q.Prime → p ≠ q → 0 < e → 0 < f →
          8 ≤ r → k = 2 * r + 1 →
          2 * r + 1 ≤ p → 2 * r + 1 ≤ q →
          d = p ^ e * q ^ f →
          LargeOddTwoPrimePellCertificate p q e f r n d))) →
    False

private lemma targetRowDisjunction_of_mem
    {k : ℕ} (hk : k ∈ ({5, 7, 9, 11, 13, 15} : Finset ℕ)) :
    k = 5 ∨ k = 7 ∨ k = 9 ∨ k = 11 ∨ k = 13 ∨ k = 15 := by
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hk

/-- The residual core supplies the genuinely remaining six odd tails, now
starting at `10^1000` and carrying the complete all-owner obstruction data. -/
theorem oddThueTail1000Hypothesis_of_finalResidual
    (hres : FinalResidual686Hypothesis) :
    OddThueTail1000Hypothesis := by
  intro k hk n d hd1000 heq
  have hk' := targetRowDisjunction_of_mem hk
  have hd120 : 10 ^ 120 ≤ d := by
    have hpow : (10 : ℕ) ^ 120 ≤ 10 ^ 1000 := by
      exact pow_le_pow_right' (by norm_num) (by norm_num)
    exact hpow.trans hd1000
  have hcert :
      Nonempty (AllOwnerAssemblyThirdNonzeroCertificate k n d) :=
    exists_allOwnerAssemblyThirdNonzeroCertificate hk' hd120 heq
  exact hres k n d heq (Or.inl ⟨hk, hd1000, hcert⟩)

/-- Every large-row equation outside the fully closed rows, universal even
tails, and exact prime-power families is exactly an instance of the residual
core. -/
theorem no_gap_solution_large_k_of_finalResidual
    (hres : FinalResidual686Hypothesis)
    {k n d : ℕ} (hk : 16 ≤ k) (hd : k ≤ d) :
    blockProduct k (n + d) ≠ 4 * blockProduct k n := by
  intro heq
  by_cases hk16 : k = 16
  · subst k
    exact no_gap_solution_four_even_sixteen hd heq
  by_cases hk18 : k = 18
  · subst k
    exact no_gap_solution_four_even_eighteen hd heq
  by_cases hk20 : k = 20
  · subst k
    exact no_gap_solution_four_even_twenty hd heq
  by_cases hk22 : k = 22
  · subst k
    exact no_gap_solution_four_even_twentytwo hd heq
  by_cases hk24 : k = 24
  · subst k
    exact no_gap_solution_four_even_twentyfour hd heq
  by_cases hk28 : k = 28
  · subst k
    exact no_gap_solution_four_even_twentyeight hd heq
  by_cases hk32 : k = 32
  · subst k
    exact no_gap_solution_four_even_thirtytwo hd heq
  have hsharpWindow : 1218443 * k * d < 1853952 * n :=
    maximal_sharp_bracket_ratio_of_four_solution hk hd heq
  have hquadraticStripComplement : k ^ 2 < 18 * d := by
    by_contra hnot
    have hstrip : 18 * d ≤ k ^ 2 := Nat.le_of_not_gt hnot
    exact (no_four_solution_of_quadratic_strip hk hd hstrip) heq
  have hevenStrip : ∀ r : ℕ, ∀ hr : 2 ≤ r, k = 2 * r →
      d < max (2 * r)
        (universalEvenTailCoefficientCertificate r hr).threshold := by
    intro r hr hkr
    by_contra hnot
    have hdTail : max (2 * r)
        (universalEvenTailCoefficientCertificate r hr).threshold ≤ d :=
      Nat.le_of_not_gt hnot
    exact (no_even_tail_solution_universal
      (r := r) (n := n) (d := d) hr hdTail) (by simpa [hkr] using heq)
  have hprimePower : ∀ p i A : ℕ, p.Prime → i ∈ Finset.Icc 1 k →
      (k - 1).factorial.factorization p ≤
        (4 : ℕ).factorization p +
          (localBlockCoefficientNat k i).factorization p →
      n + i ≠ p ^ A := by
    intro p i A hp hi hloss howner
    exact (no_gap_solution_lower_term_prime_power_of_factorial_loss_le
      hp hk hd hi howner hloss) heq
  have hsmallCofactor : ∀ p i A a : ℕ, p.Prime → k < p →
      i ∈ Finset.Icc 1 k → 1 ≤ A →
      3707904 * a ≤ 1218443 * k →
      n + i ≠ a * p ^ A := by
    intro p i A a hp hkp hi hA ha howner
    exact (no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_maximal_sharp_band
      hp hk hd hkp hi hA ha howner) heq
  have hlargePrimeComponents : ∀ p e : ℕ,
      p.Prime → 0 < e → k ≤ p → p ^ e ∣ d →
      6 * p ^ (2 * e) < (13 * k - 6) * d + 18 * (k - 1) := by
    intro p e hp he hkp hpow
    exact large_prime_gap_component_square_strict_upper_of_four_solution
      hp he hk hd hkp hpow heq
  have hhighPrimePowerComponents : ∀ p e : ℕ,
      p.Prime → d.factorization p = e → k ≤ p ^ e →
      (p = 2 →
        24 * 2 ^ (2 * e - highComponentLambda 2 k) <
          (13 * k - 6) * d + 18 * (k - 1)) ∧
      (p = 3 →
        6 * 3 ^ (2 * e - highComponentMuThree k e - 1) <
          (13 * k - 6) * d + 18 * (k - 1)) ∧
      (5 ≤ p →
        6 * p ^ (2 * e - highComponentLambda p k) <
          (13 * k - 6) * d + 18 * (k - 1)) := by
    intro p e hp hexact hcomponent
    constructor
    · intro hp2
      by_contra hnot
      have hdom :
          (13 * k - 6) * d + 18 * (k - 1) ≤
            24 * 2 ^ (2 * e - highComponentLambda 2 k) :=
        Nat.le_of_not_gt hnot
      exact (no_four_solution_of_highPrimePower_component
        hp hk hd hexact hcomponent (Or.inl ⟨hp2, hdom⟩)) heq
    constructor
    · intro hp3
      by_contra hnot
      have hdom :
          (13 * k - 6) * d + 18 * (k - 1) ≤
            6 * 3 ^ (2 * e - highComponentMuThree k e - 1) :=
        Nat.le_of_not_gt hnot
      exact (no_four_solution_of_highPrimePower_component
        hp hk hd hexact hcomponent (Or.inr (Or.inl ⟨hp3, hdom⟩))) heq
    · intro hp5
      by_contra hnot
      have hdom :
          (13 * k - 6) * d + 18 * (k - 1) ≤
            6 * p ^ (2 * e - highComponentLambda p k) :=
        Nat.le_of_not_gt hnot
      exact (no_four_solution_of_highPrimePower_component
        hp hk hd hexact hcomponent (Or.inr (Or.inr ⟨hp5, hdom⟩))) heq
  have hgroupedOwners : ∃ owner : ℕ → ℕ,
      GlobalResidualOwnerAssignment k n d owner ∧
      ∀ i : ℕ, i ∈ Finset.Icc 1 k →
        6 * (globalResidualGroupedLeft k d owner i) ^ 2 <
          (13 * k - 6) * d + 18 * (k - 1) := by
    obtain ⟨owner, howner⟩ :=
      exists_globalResidualOwnerAssignment (by omega) hd heq
    refine ⟨owner, howner, ?_⟩
    intro i hi
    exact grouped_owner_square_strict_upper_of_four_solution
      hk hd hi howner heq
  have hprimePowerBoundary : ∀ p a : ℕ,
      p.Prime → 5 ≤ p → 0 < a → k = p ^ a - 1 →
      ¬ p ^ a ∣ n ∧ ¬ p ^ a ∣ n + d := by
    intro p a hp hp5 _ha hkPow
    have hqeq :
        blockProduct (p ^ a - 1) (n + d) =
          4 * blockProduct (p ^ a - 1) n := by
      simpa [hkPow] using heq
    exact prime_power_pred_four_solution_endpoints_not_dvd hp hp5 hqeq
  have hlargeOddPell : ∀ p q e f r : ℕ,
      p.Prime → q.Prime → p ≠ q → 0 < e → 0 < f →
      8 ≤ r → k = 2 * r + 1 →
      2 * r + 1 ≤ p → 2 * r + 1 ≤ q →
      d = p ^ e * q ^ f →
      LargeOddTwoPrimePellCertificate p q e f r n d := by
    intro p q e f r hp hq hpq he hf hr8 hkOdd hpk hqk hgap
    have heq' :
        blockProduct (2 * r + 1) (n + d) =
          4 * blockProduct (2 * r + 1) n := by
      simpa [hkOdd] using heq
    exact large_odd_two_large_prime_pell_certificate
      hp hq hpq he hf hr8 hpk hqk hgap heq'
  exact hres k n d heq (Or.inr
    ⟨hk, hd, hk16, hk18, hk20, hk22, hk24, hk28, hk32, hsharpWindow,
      hquadraticStripComplement,
      hevenStrip, hprimePower, hsmallCofactor, hlargePrimeComponents,
      hhighPrimePowerComponents, hgroupedOwners, hprimePowerBoundary,
      hlargeOddPell⟩)

/-- The one residual core implies the former large-`k` smoothness interface.
The smoothness premise is intentionally unused: the prime obstruction has
already made any exact equation smooth, while the residual theorem excludes
the remaining equations themselves. -/
theorem largeKSmoothHypothesis_of_finalResidual
    (hres : FinalResidual686Hypothesis) :
    LargeKSmoothHypothesis := by
  intro k n d hk hd heq _hsmooth
  exact no_gap_solution_large_k_of_finalResidual hres hk hd heq

/-- Conversely, the two updated terminal hypotheses immediately discharge
the corresponding disjuncts of the packaged residual.  This theorem records
that `FinalResidual686Hypothesis` is equivalent packaging, not a claim of a
strictly weaker missing theorem. -/
theorem finalResidual_of_tail1000_and_smooth
    (htails : OddThueTail1000Hypothesis)
    (hsmooth : LargeKSmoothHypothesis) :
    FinalResidual686Hypothesis := by
  intro k n d heq hcase
  rcases hcase with hodd | hlarge
  · exact (htails k hodd.1 n d hodd.2.1) heq
  · exact (no_gap_solution_large_k_of_smooth hsmooth hlarge.1 hlarge.2.1) heq

/-- Exact logical audit of the single residual interface. -/
theorem finalResidual_iff_tail1000_and_smooth :
    FinalResidual686Hypothesis ↔
      OddThueTail1000Hypothesis ∧ LargeKSmoothHypothesis := by
  constructor
  · intro hres
    exact ⟨oddThueTail1000Hypothesis_of_finalResidual hres,
      largeKSmoothHypothesis_of_finalResidual hres⟩
  · rintro ⟨htails, hsmooth⟩
    exact finalResidual_of_tail1000_and_smooth htails hsmooth

/-- Terminal refutation from the single exact residual core. -/
theorem erdos686_false_of_finalResidual
    (hres : FinalResidual686Hypothesis) :
    ¬ ∀ N : ℕ, 2 ≤ N → ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (N : ℚ) =
        (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ))) := by
  exact erdos686_false_of_tail1000_and_smooth
    (oddThueTail1000Hypothesis_of_finalResidual hres)
    (largeKSmoothHypothesis_of_finalResidual hres)

#print axioms oddThueTail1000Hypothesis_of_finalResidual
#print axioms no_gap_solution_large_k_of_finalResidual
#print axioms largeKSmoothHypothesis_of_finalResidual
#print axioms finalResidual_of_tail1000_and_smooth
#print axioms finalResidual_iff_tail1000_and_smooth
#print axioms erdos686_false_of_finalResidual

end Erdos686Variant
end Erdos686
