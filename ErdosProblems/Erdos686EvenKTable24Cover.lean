import ErdosProblems.Erdos686EvenKFiniteTableDefs
namespace Erdos686.Erdos686Variant

def even24CandidateAllowed (t : Fin 565) : Bool :=
  even24A13 ((-(10616832 * (t.val : ℤ)) : ℤ) : ZMod 13) &&
  even24A191 ((-(10616832 * (t.val : ℤ)) : ℤ) : ZMod 191) &&
  even24A157 ((-(10616832 * (t.val : ℤ)) : ℤ) : ZMod 157) &&
  even24A227 ((-(10616832 * (t.val : ℤ)) : ℤ) : ZMod 227) &&
  even24A239 ((-(10616832 * (t.val : ℤ)) : ℤ) : ZMod 239) &&
  even24A241 ((-(10616832 * (t.val : ℤ)) : ℤ) : ZMod 241) &&
  even24A131 ((-(10616832 * (t.val : ℤ)) : ℤ) : ZMod 131) &&
  even24A197 ((-(10616832 * (t.val : ℤ)) : ℤ) : ZMod 197) &&
  even24A71 ((-(10616832 * (t.val : ℤ)) : ℤ) : ZMod 71)

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 1000000 in
theorem even24_candidate_cover :
    ∀ t : Fin 565, t.val ≠ 0 → even24CandidateAllowed t = false := by decide

end Erdos686.Erdos686Variant
