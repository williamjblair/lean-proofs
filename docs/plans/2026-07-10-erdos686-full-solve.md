# Erdős 686 Full Solve Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove both exact open hypotheses in `ErdosProblems/Erdos686FinalReduction.lean`, or bank the strongest genuinely new theorem with the residual obstruction isolated as one quantified lemma.

**Architecture:** Keep mathematical discovery, exact-arithmetic falsification, and Lean integration as separate gates. Run independent Target 1 and Target 2 portfolios, register every route before investing in it, and allow a candidate into Lean only after it survives the prompt's named counterexamples and a dependency-tree audit.

**Tech Stack:** Lean 4.29.1, mathlib 4.29.1, Python 3 exact integers and `fractions.Fraction`, C scanners already under `compute/structure_hunt_src`, repository manifest and axiom-audit scripts.

---

### Task 1: Freeze the verified baseline and approach registry

**Files:**
- Create: `compute/campaign686/approach_registry.md`
- Reference: `FRONTIER.md`
- Reference: `codex/prompt_686_full_solve.md`
- Reference: `PROGRESS_Erdos686.md`
- Reference: `ErdosProblems/Erdos686FinalReduction.lean`
- Reference: `ErdosProblems/Erdos686PrimeObstruction.lean`

**Step 1: Record the exact target definitions**

Copy the Lean declarations `OddThueTailHypothesis` and `LargeKSmoothHypothesis` into the registry by name and source location. Do not paraphrase their quantifiers.

**Step 2: Record the non-negotiable falsification fixtures**

Register the `k = 9, 15`, `d = 1` telescopes, `(k,n,d) = (984,3177026,4480)`, the `n = 48502` cluster, and the MalekZ all-moduli warning. Mark which hypotheses each fixture does and does not satisfy.

**Step 3: Verify the baseline build**

Run: `lake env lean ErdosProblems/Erdos686FinalReduction.lean`

Expected: exit 0.

**Step 4: Verify the baseline audit surface**

Run: `bash scripts/check_manifest.sh && lake env lean Audit.lean && bash scripts/check_axioms.sh`

Expected: all checks pass and every audited headline theorem uses only `[propext, Classical.choice, Quot.sound]`.

**Step 5: Commit the campaign scaffolding**

Run: `git add docs/plans/2026-07-10-erdos686-full-solve.md compute/campaign686/approach_registry.md && git commit -m "Start auditable Erdos686 full-solve campaign"`

Expected: one scaffolding commit with no theorem claim.

### Task 2: Build exact Target 1 identity diagnostics

**Files:**
- Create: `compute/campaign686/odd_tail_identities.py`
- Create: `compute/campaign686/test_odd_tail_identities.py`
- Create: `compute/campaign686/odd_tail_findings.md`
- Reference: `ErdosProblems/Erdos686ConvergentMachinery.lean`
- Reference: `ErdosProblems/Erdos686FiveThue.lean`
- Reference: `ErdosProblems/Erdos686SevenThue.lean`
- Reference: `ErdosProblems/Erdos686NineThue.lean`
- Reference: `ErdosProblems/Erdos686ElevenThue.lean`
- Reference: `ErdosProblems/Erdos686ThirteenThue.lean`
- Reference: `ErdosProblems/Erdos686FifteenThue.lean`

**Step 1: Write exact centered-polynomial tests**

Test `P_k(X) = X * product(X^2-j^2)` and the exact error identity
`X^k - 4Y^k = -sum_{r<k} a_r (X^r - 4Y^r)` for every target `k`.

**Step 2: Add the telescope regression fixtures**

Assert `P_9(8) = 4 P_9(7)` and the corresponding `k = 15` fixture obtained from the banked module. Assert neither fixture has `d >= k`.

**Step 3: Run the tests before adding route-specific code**

Run: `python3 -m pytest compute/campaign686/test_odd_tail_identities.py -q`

Expected: all identity and telescope fixtures pass exactly.

**Step 4: Implement candidate diagnostics**

For each registered CF-remainder, valuation, Puiseux, or unit-equation route, emit only exact integers or `Fraction` values. Every diagnostic must expose the precise sign, denominator, and exponent range used by a proposed lemma.

**Step 5: Counterexample-search each candidate lemma**

Run: `python3 -m pytest compute/campaign686/test_odd_tail_identities.py -q`

Expected: a candidate is retained only if no named fixture or bounded exact search refutes it.

**Step 6: Update the registry verdicts**

For every route, record `active`, `proved`, `refuted`, or `blocked`, with an exact witness or a single quantified missing estimate.

### Task 3: Build exact Target 2 row and matching diagnostics

**Files:**
- Create: `compute/campaign686/large_k_rows.py`
- Create: `compute/campaign686/test_large_k_rows.py`
- Create: `compute/campaign686/large_k_findings.md`
- Reference: `compute/erdos686_row_smooth_scan.py`
- Reference: `compute/erdos686_prefix_counterexamples.py`
- Reference: `compute/artifacts/structure_hunt/t4_cluster_anatomy.json`
- Reference: `compute/artifacts/structure_hunt/td_deep_census.json`
- Reference: `ErdosProblems/Erdos686.lean`
- Reference: `ErdosProblems/Erdos686PrimeObstruction.lean`

**Step 1: Reproduce every named deep survivor**

Calculate each row interval, the factorization of `n+j`, and the first failing row for the `(984,3177026,4480)` witness and the `n = 48502` cluster using exact integer arithmetic.

**Step 2: Test matching invariants**

For each prime power `p^e > k` in the lower block, compute its unique allowed landing position in every row and build the induced row-factor bipartite graph.

**Step 3: Write adversarial unit tests**

Any proposed Hall deficit, collision count, monotonicity law, or bounded-prefix law must be asserted on both deep clusters before broader scanning.

**Step 4: Run the exact tests**

Run: `python3 -m pytest compute/campaign686/test_large_k_rows.py -q`

Expected: all baseline fixtures pass; false candidate invariants produce a stored witness and are removed from the proof path.

**Step 5: State the strongest surviving unbounded lemma**

Write every quantifier and constant explicitly. Explain why its conclusion is strictly weaker than Target 2 unless it directly closes `LargeKSmoothHypothesis`.

### Task 4: Perform the intake audit on each surviving candidate

**Files:**
- Create: `compute/campaign686/audit.md`
- Reference: `compute730/audit.md`
- Modify: `compute/campaign686/approach_registry.md`

**Step 1: Build a dependency tree**

List every node from banked theorem to target conclusion. Mark each node `banked`, `proved here`, `computed exactly`, or `open`.

**Step 2: Expand qualitative phrases**

Replace every use of `essentially`, `uniformly`, `sufficiently large`, `negligible`, or `by standard estimates` by an explicit quantified inequality.

**Step 3: Audit circular strength**

For each new lemma, show a model or regime where the lemma is strictly weaker than the target, or supply its complete proof. Reject target-equivalent hypotheses.

**Step 4: Replay all exact claims**

Run: `python3 -m pytest compute/campaign686 -q`

Expected: all exact-arithmetic claims in the audit are reproduced from source scripts.

### Task 5: Formalize the strongest audited result

**Files:**
- Create as needed: `ErdosProblems/Erdos686OddTailStructure.lean`
- Create as needed: `ErdosProblems/Erdos686LargeKSmooth.lean`
- Modify as needed: `ErdosProblems/Erdos686FinalReduction.lean`
- Modify as needed: `ErdosProblems.lean`
- Modify as needed: `Audit.lean`
- Modify as needed: `proofs.yaml`

**Step 1: Write the exact Lean theorem statement**

The statement must match the audited quantified lemma. Do not weaken strict inequalities, smoothness bounds, or membership ranges for convenience.

**Step 2: Add the smallest failing Lean proof skeleton**

Run: `lake env lean ErdosProblems/Erdos686OddTailStructure.lean` or `lake env lean ErdosProblems/Erdos686LargeKSmooth.lean`

Expected: failure only at the new proof body, with imports and theorem statement accepted.

**Step 3: Implement the proof without forbidden shortcuts**

No `sorry`, `admit`, `axiom`, `native_decide`, or theorem-strength assumption may enter the dependency tree.

**Step 4: Compile the focused module**

Run the corresponding `lake env lean` command.

Expected: exit 0.

**Step 5: Connect the result to the terminal reduction**

If both hypotheses are discharged, add an unconditional theorem refuting the universal Erdős 686 statement. If only a proper subcase is proved, expose exactly that subcase and leave the terminal theorem conditional.

### Task 6: Run the release-quality proof gates

**Files:**
- Modify: `PROGRESS_Erdos686.md`
- Modify: `FRONTIER.md`
- Modify: `attestations.json`

**Step 1: Check formatting and forbidden tokens**

Run: `git diff --check && rg -n "\bsorry\b|\badmit\b|native_decide|^axiom " ErdosProblems/Erdos686*.lean`

Expected: no new forbidden token; pre-existing commentary is reviewed separately.

**Step 2: Check theorem-manifest consistency**

Run: `bash scripts/check_manifest.sh`

Expected: pass.

**Step 3: Check the kernel axiom surface**

Run: `lake env lean Audit.lean && bash scripts/check_axioms.sh`

Expected: every new headline theorem has axioms contained in `[propext, Classical.choice, Quot.sound]`.

**Step 4: Run the full build**

Run: `lake build`

Expected: exit 0.

**Step 5: Emit and verify attestation**

Use the repository attestation script named by `scripts/README.md`, then validate `attestations.json` and rerun the manifest check.

**Step 6: Commit only verified state**

Run: `git add <audited files> && git commit -m "Prove audited Erdos686 result"`

Expected: the commit message and documentation distinguish a full solve from a banked partial theorem.

### Task 7: Apply the no-partial-return rule

**Files:**
- Modify: `compute/campaign686/audit.md`
- Modify: `compute/campaign686/approach_registry.md`

**Step 1: Continue independent routes for the required time budget**

Do not stop merely because one route is blocked or one bounded range is extended.

**Step 2: Select the return theorem**

Prefer a complete proof of both exact targets. Otherwise select the strongest rigorously proved derivation that is genuinely stronger than the baseline.

**Step 3: State one exact remaining gap**

The final gap must be a single quantified lemma with all dependencies and constants exposed. It must not be advertised as progress if it is equivalent in strength to the original target.
