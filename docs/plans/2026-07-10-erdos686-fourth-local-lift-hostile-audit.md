# Erdős 686 Fourth Local Lift Hostile Audit Plan

**Goal:** Independently decide whether the frozen fourth-local-lift checkpoint is exact, kernel-clean, and correctly scoped as a proper one-digit restriction rather than a closure of the three-owner branch.

**Frozen producer inputs:**

- `ErdosProblems/Erdos686FourthLocalLift.lean` (`22d853c7eac8064aeee977c20757b5f4000006483a2cfade54ef0347c8c4d0be`)
- `compute/campaign686/fourth_local_lift_verify.py` (`22ab5000e33fb6fd4dc6011de76f61165e658d06b8d7efd96139d0133e025068`)
- `compute/campaign686/test_fourth_local_lift_verify.py` (`99451323a4c12646a62666d6e72ada7da9cbac40ccffd2ca20a8a9e3bdab963f`)
- `compute/campaign686/fourth_local_lift_findings.md` (`03b50d019a69760f2b64baa7b57855adae957c2b0cd591383d45b773c432471a`)
- `docs/plans/2026-07-10-erdos686-fourth-local-lift.md` (`a162050046ae840a9e520d5c226190cb2ea1676d67e0b7cd256e3951b4930ed0`)

## Task 1: Re-derive the local identity

- Reconstruct `C,D,E,F` from reciprocal elementary symmetric sums, not the producer's polynomial multiplication.
- Expand `27*T4-G4` exactly and retain all `A` corrections.
- Exercise signed values, `H=3`, `H=+-1`, center owners, and reflected owners.

## Task 2: Re-derive the cyclic composition

- Starting from both square-residual differences, separately verify the refined third-order residue modulo `P^3` and the fourth correction modulo `P`.
- Check that `(bc)^2` is necessary for the stated elimination, that the refined `-108` term is retained, and that `6804=84*9^2`.
- Exhaust all 1,035 target-row triples cyclically with signed and unit-component fixtures, including owner component `P=3`.

## Task 3: Rebuild the Hensel/CRT falsifier

- Independently solve the third lift modulo `P_i^2`, then the fourth lift modulo `P_i` from the finite-difference derivative.
- Reproduce the target-size `e=20` member and a range of exponents.
- Directly check square residuals, owner divisibility, second/third/fourth congruences, composed congruences, `P_i^5` block-difference congruences, the exact block equation, and every short-window inequality.

## Task 4: Audit the kernel surface and issue a verdict

- Compile a fresh audit module and print axioms for all four public theorems.
- Run a forbidden-token gate without treating `#print axioms` as a declaration.
- Record a node-by-node verdict and the exact remaining quantified gap.
- Modify no producer or shared integration file.
