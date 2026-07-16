/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686K5AllPunctures

/-!
Independent axiom-surface check for the completed `k = 5` proper-support
certificate.  This file deliberately imports only the public aggregate.
-/

#check Erdos686.Erdos686Variant.exists_k5_punctureJetWitness
#check Erdos686.Erdos686Variant.no_k5_tail_solution_of_proper_support
#print axioms Erdos686.Erdos686Variant.no_k5_tail_solution_of_proper_support
