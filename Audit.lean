/-
Axiom audit entrypoint. Lists `#print axioms` for every headline theorem that
this repo hosts as a `formal_proof` target. `scripts/check_axioms.sh` builds
this file and fails CI if any line reports `sorryAx` or an axiom outside the
allowed set `[propext, Classical.choice, Quot.sound]`.

When you add a proof, add its module import and a `#print axioms` line here and
a matching entry in `proofs.yaml`.
-/
import ErdosProblems.Erdos154Sumset
import ErdosProblems.Erdos617

#print axioms Erdos154.erdos_154_sumset
#print axioms Erdos617.Balanced.no_monochromatic_clique
#print axioms Erdos617.Balanced.sum_le_sq
#print axioms Erdos617.statement_five_of_extension_demand
