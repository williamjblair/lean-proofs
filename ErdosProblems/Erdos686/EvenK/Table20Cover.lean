import ErdosProblems.Erdos686.EvenK.FiniteTableDefs
namespace Erdos686.Erdos686Variant

def even20CandidateAllowed (t : Fin 1830) : Bool :=
  even20A227 ((-(3200 * (t.val : ℤ)) : ℤ) : ZMod 227) &&
  even20A199 ((-(3200 * (t.val : ℤ)) : ℤ) : ZMod 199) &&
  even20A233 ((-(3200 * (t.val : ℤ)) : ℤ) : ZMod 233) &&
  even20A239 ((-(3200 * (t.val : ℤ)) : ℤ) : ZMod 239) &&
  even20A211 ((-(3200 * (t.val : ℤ)) : ℤ) : ZMod 211) &&
  even20A197 ((-(3200 * (t.val : ℤ)) : ℤ) : ZMod 197) &&
  even20A241 ((-(3200 * (t.val : ℤ)) : ℤ) : ZMod 241)

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 1000000 in
theorem even20_candidate_cover :
    ∀ t : Fin 1830, t.val ≠ 0 → even20CandidateAllowed t = false := by decide

end Erdos686.Erdos686Variant
