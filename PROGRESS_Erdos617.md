# PROGRESS.md - Erdős Problem #617

Date: 2026-07-10 (live campaign)
Lane: decide the r = 5 case — does a 5-coloring of E(K_26) exist with
every color class of independence number ≤ 5? SAT disproves the whole
Erdős–Gyárfás conjecture; UNSAT proves the first open case since 1999.

## Status

- [R] Lean foundation banked (`ErdosProblems/Erdos617.lean`): Balanced
  vocabulary (definitionally matches formal-conjectures), monochromatic-
  clique exclusion, independence bridge, vertex-deletion frame with
  attachment partition, hitting-set counting interface, and the
  conditional reduction `statement_five_of_extension_demand`.
- [R] Structure: every counterexample class is K_6-free AND α ≤ 5 (a
  (6,6)-Ramsey graph); the affine AG(2,5)+∞ family is exactly empty
  (all 6 omitted-direction completions UNSAT); at most one class has a
  5-clique cover; ≥ 4 classes need ≥ 59 edges (Brouwer refinement).
- [R] First SMS verdict: silent classes (α ≤ 4) need ≥ 76 edges
  ⟹ the two-silent-classes case is closed (302 > 300).
- [E] Every valid K_25 coloring examined (79 pairwise non-isomorphic +
  complete translation-invariant classification) is non-extendable with
  extension demand Σh ≥ 37 vs budget 25; SLS plateaus universally.
- Calibration: r=3 K_10 UNSAT reproduced (222s CDCL; 0.02s under SMS —
  4 orders of magnitude from native symmetry handling); K_25 SAT side
  reproduces the affine solution.
- In flight: SMS on the direct K_26 instance and on the decisive
  sum_silent leg; sub-cube swarm (1044 cubes, majority UNSAT so far,
  zero SAT); E7-bounded kissat. LRAT certification supported by smsg
  for the endgame. Live logs: compute617/sat_log.md,
  compute617/constructions_log.md.

## Verifier

compute617/core.py `is_counterexample` is ground truth; any claimed
witness must pass it exactly.
