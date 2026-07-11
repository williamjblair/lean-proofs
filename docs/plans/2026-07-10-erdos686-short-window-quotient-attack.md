# Erdős 686 Short-Window Quotient Attack Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Determine whether the exact three-owner square, second-, third-, and fourth-lift conditions admit a target-size short-window pseudo-witness, and otherwise bank a proper quotient/lattice restriction with exact verification.

**Architecture:** Normalize each selected residual as `X_s = q*d + P_s*y_s`, introduce the exact third quotient `z_s = F_s/P_s^2`, and independently reproduce the cyclic fourth quotient congruence.  Exhaust the finite row/index coefficient geometry, search exact finite and parametric pseudo-witness families, and isolate only restrictions that are strictly stronger than restating the open short-CRT target.

**Tech Stack:** Python 3 exact integers and `fractions.Fraction`; Lean 4/mathlib for any proper generic arithmetic lemma; pytest; repository axiom gate.

---

### Task 1: Freeze the quotient identities

**Files:**
- Create: `compute/campaign686/short_window_quotient_attack.py`
- Test: `compute/campaign686/test_short_window_quotient_attack.py`

1. Write tests for the common floor quotient, exact remainders `P_s*y_s`, the pair determinant identities, and the cofactor-overlap gcd divisibilities.
2. Implement independent coefficient and obstruction formulas without importing prior campaign verifiers.
3. Check all six target rows, all ordered distinct owner triples, centers, reflections, owner components `2` and `3`, and the two `d=1` telescopes.
4. Run `python3 -m pytest compute/campaign686/test_short_window_quotient_attack.py -q` and require every test to pass.

### Task 2: Search for a short-window falsifier

**Files:**
- Modify: `compute/campaign686/short_window_quotient_attack.py`
- Modify: `compute/campaign686/test_short_window_quotient_attack.py`

1. Reproduce the known below-threshold short fixture and verify whether it survives the fourth lift.
2. Enumerate exact small component/loss/quotient ranges using the quotient parameterization, retaining only pairwise-coprime components and all cyclic local/composed lifts.
3. Test structured prime-power/Hensel families through target-size exponents and record whether any member retains the short window.
4. If a target-size tuple appears, verify every defining equality, divisibility, nonzero obstruction, window inequality, and direct block-equation failure before labeling it a pseudo-witness.

### Task 3: Derive the quotient-lattice restriction

**Files:**
- Modify: `compute/campaign686/short_window_quotient_attack.py`
- Test: `compute/campaign686/test_short_window_quotient_attack.py`
- Create if proper: `ErdosProblems/Erdos686ShortWindowQuotient.lean`

1. Define `z_s=F_s/P_s^2` and prove the cancelled fourth condition `P_s | 3*a_u*a_v*z_s+J_s`.
2. Prove `gcd(P_s,a_u*a_v)` divides `9*(s-u)*(s-v)` and audit signs/zero offsets exactly.
3. Form the coefficient cross-product annihilating the `abc` and `g^2*d` terms in the three `F_s` equations, yielding one exact three-term lattice identity with a bounded `g^2` right side.
4. Derive an explicit short-window bound on `|z_s|` and retain it only if it is a proper quantitative restriction, not an equivalent restatement of the target.
5. Build any Lean module directly and check its public theorems with `lake env lean` and `#print axioms`.

### Task 4: Report and verify

**Files:**
- Create: `compute/campaign686/short_window_quotient_findings.md`

1. State either the fully verified target-size pseudo-witness or the strongest proved restriction and the exact surviving quantified gap.
2. Include a dependency tree and per-node verdicts, plus explicit coverage of small primes, centers, reflections, and telescopes.
3. Run Python byte-compilation, focused pytest, Lean build if present, forbidden-token scan, and `git diff --check`.
4. Leave shared imports, manifests, dashboards, attestations, and unrelated concurrent files unchanged.
