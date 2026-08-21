/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos730.FullDensityCore

/-!
# Erdős 730 full-density family core: independent kernel audit

This module imports the producer but independently recomputes its principal
arithmetic and set-theoretic bridge.  It deliberately does not supply any of
the analytic hypotheses needed to prove that the good-parameter set is
infinite.
-/

namespace Erdos730
namespace FullDensityCoreAudit

open FullDensityCore

/-- Independent expansion of all four branches. -/
theorem branch_expansions_audit (x : ℕ) :
    P x = 222138 * x + 11 ∧
    Q x = 380808 * x + 13 ∧
    R x = 148092 * x + 5 ∧
    S x = 380808 * x + 19 := by
  norm_num [P, Q, R, S, T]

/-- Independent exact expansion of the quadratic family. -/
theorem n_expansion_audit (x : ℕ) :
    n x = 84591927504 * x ^ 2 + 7076682 * x + 142 := by
  unfold n
  have hprod :
      P x * Q x = 84591927504 * x ^ 2 + 7076682 * x + 143 := by
    simp only [P, Q, T]
    ring
  rw [hprod]
  omega

/-- Independent simultaneous check of the product identity and all six
linear identities, in subtraction-free natural-number form. -/
theorem family_identities_audit (x : ℕ) :
    2 * (P x * Q x) = 3 * (R x * S x) + 1 ∧
    12 * P x = 7 * Q x + 41 ∧
    18 * R x + 43 = 7 * S x ∧
    12 * P x + 1 = 7 * S x ∧
    7 * Q x = 18 * R x + 1 ∧
    2 * P x = 3 * R x + 7 ∧
    S x = Q x + 6 := by
  simp only [P, Q, R, S, T]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · trivial

/-- Independent successor-step certificate for strict growth. -/
theorem n_growth_step_audit (x : ℕ) : n x < n (x + 1) := by
  rw [n_expansion_audit, n_expansion_audit]
  nlinarith

theorem n_strictMono_audit : StrictMono n :=
  strictMono_nat_of_lt_succ n_growth_step_audit

/-- Independent check that a good parameter lands in the exact upstream
pair set. -/
theorem familyPair_mem_pairSet_audit {x : ℕ} (hx : GoodParameter x) :
    familyPair x ∈ PairSet := by
  change n x < n x + 1 ∧
    (n x).centralBinom.primeFactors =
      (n x + 1).centralBinom.primeFactors
  exact ⟨Nat.lt_succ_self _, hx.2⟩

theorem familyPair_mapsTo_pairSet_audit :
    Set.MapsTo familyPair GoodParameters PairSet := by
  intro x hx
  exact familyPair_mem_pairSet_audit hx

theorem familyPair_injective_audit : Function.Injective familyPair := by
  intro x y hxy
  have hnxy : n x = n y := congrArg Prod.fst hxy
  exact n_strictMono_audit.injective hnxy

/-- Independent reconstruction of the infinite-image bridge. -/
theorem pairSet_infinite_bridge_audit
    (hgood : GoodParameters.Infinite) : PairSet.Infinite := by
  have hinj : Set.InjOn familyPair GoodParameters :=
    fun _ _ _ _ h => familyPair_injective_audit h
  have himage : (familyPair '' GoodParameters).Infinite :=
    Set.Infinite.image hinj hgood
  exact himage.mono (by
    rintro _ ⟨x, hx, rfl⟩
    exact familyPair_mem_pairSet_audit hx)

/-- Independent fixed-prime and small-prime congruence computation. -/
theorem fixed_prime_congruences_audit (x : ℕ) :
    (P x % 41 = 11 ∧ Q x % 41 = 13 ∧
      R x % 41 = 5 ∧ S x % 41 = 19) ∧
    (P x % 43 = 11 ∧ Q x % 43 = 13 ∧
      R x % 43 = 5 ∧ S x % 43 = 19) ∧
    (P x % 3 = 2 ∧ Q x % 3 = 1 ∧
      R x % 3 = 2 ∧ S x % 3 = 1) ∧
    P x % 7 = 4 ∧ R x % 7 = 5 := by
  simp only [P, Q, R, S, T]
  omega

/-- Independent finite enumeration of both top-range unit tables. -/
theorem top_residue_tables_audit :
    unitsMod 7 = {1, 2, 3, 4, 5, 6} ∧
    PAllowedResidues = {3, 4} ∧
    unitsMod 14 = {1, 3, 5, 9, 11, 13} ∧
    RAllowedResidues = {5, 9} := by
  decide

/-- Independent exact cardinality certificate: two allowed unit residues out
of six in each top branch. -/
theorem top_residue_card_audit :
    (unitsMod 7).card = 6 ∧ PAllowedResidues.card = 2 ∧
    (unitsMod 14).card = 6 ∧ RAllowedResidues.card = 2 := by
  decide

/-- Independent `P` top-digit inequality check. -/
theorem P_top_digit_audit
    {p c r d : ℕ} (hc : 0 < c) (hp : 130 * c < p)
    (hr : r = 3 ∨ r = 5 ∨ r = 6)
    (heq : 7 * d + 41 * c = r * p) :
    0 < d ∧ d < p ∧ (2 * d < p ↔ r = 3) := by
  rcases hr with rfl | rfl | rfl <;> omega

/-- Independent `Q` and `S` top-digit exclusions. -/
theorem Q_S_top_digit_audit
    {p c dQ dS : ℕ} (_hc : 0 < c) (_hp : 130 * c < p)
    (hQ : 12 * dQ = 7 * p + 41 * c)
    (hS : 12 * dS + 43 * c + 6 = 7 * p) :
    p < 2 * dQ ∧ p < 2 * dS ∧ dS < p := by
  omega

/-- Independent `R` top-digit inequality check. -/
theorem R_top_digit_audit
    {p c r d : ℕ} (hc : 0 < c) (hp : 130 * c < p)
    (hr : r = 6 ∨ r = 10 ∨ r = 12)
    (heq : 14 * d + 7 = r * p + 129 * c) :
    0 < d ∧ d < p ∧ (2 * d < p ↔ r = 6) := by
  rcases hr with rfl | rfl | rfl <;> omega

/-- Independent exact factorization and class-count arithmetic. -/
theorem switching_arithmetic_audit :
    42 * T = 2 * 3 ^ 2 * 7 * 41 * 43 ∧
    28 * T = 2 ^ 2 * 3 * 7 * 41 * 43 ∧
    3 * 20160 = 60480 ∧ 3 * 13440 = 40320 := by
  norm_num [T]

#print axioms branch_expansions_audit
#print axioms n_expansion_audit
#print axioms family_identities_audit
#print axioms n_strictMono_audit
#print axioms familyPair_mem_pairSet_audit
#print axioms familyPair_mapsTo_pairSet_audit
#print axioms familyPair_injective_audit
#print axioms pairSet_infinite_bridge_audit
#print axioms fixed_prime_congruences_audit
#print axioms top_residue_tables_audit
#print axioms top_residue_card_audit
#print axioms P_top_digit_audit
#print axioms Q_S_top_digit_audit
#print axioms R_top_digit_audit
#print axioms switching_arithmetic_audit

end FullDensityCoreAudit
end Erdos730
