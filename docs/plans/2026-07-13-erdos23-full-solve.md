# Erdős 23 Full Two-Defect Closure Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Kernel-check the complete Erdős 23 `d = 2s - 2` two-defect graph closure, register its unconditional headline theorem, and pass every repository proof gate.

**Architecture:** Add one final module above `Erdos23GapGBTwoDefectAlignment` that first banks the already CI-certified common geometry helpers, then closes the four remaining canonical shapes with literal BFS threshold cuts and the existing aligned/one-exception arithmetic landings. Finish with a five-shape dispatcher, leaving the two existing pure-mass closures unchanged. Work directly on `main`, stage only explicit Erdős 23 and registration paths, and never read from or modify the concurrent Erdős 686 WIP as proof input.

**Tech Stack:** Lean 4, mathlib `SimpleGraph`, Lake, repository manifest and axiom-audit scripts, YAML proof registry, JSON attestations.

---

## Main-only and concurrency constraints

- Stay on `main`; do not create or switch to a feature branch or worktree.
- Preserve the current untracked Erdős 686 files and `compute/campaign686/agent_gptpro_even_uniform/` directory byte-for-byte.
- Never run `git add -A` or `git add .`; stage only named Erdős 23/registry files.
- Before each scoped commit, run `git diff --cached --name-only` and verify that no path containing `Erdos686` or `campaign686` appears.
- Treat a branch proof as certified only after a targeted build, and the problem as solved only after the complete build, axiom, manifest, and attestation gates pass.

### Task 1: Record the clean baseline and concurrent-work fence

**Files:**

- Inspect: `ErdosProblems/Erdos686*.lean`
- Inspect: `compute/campaign686/agent_gptpro_even_uniform/`
- Inspect: `ErdosProblems/Erdos23GapGB*.lean`

**Step 1: Confirm branch and tracked state**

Run:

```bash
git status --short --branch
git rev-parse HEAD
```

Expected: `main` tracks `origin/main`; any foreign WIP is untracked and limited to Erdős 686 paths.

**Step 2: Snapshot the foreign path list without staging it**

Run:

```bash
git status --porcelain=v1 | rg 'Erdos686|campaign686'
```

Expected: only the known concurrent 686 paths; no staged entries.

**Step 3: Confirm the current registry baseline**

Run:

```bash
bash scripts/check_manifest.sh
```

Expected: success, currently `749 theorem(s)` before the new theorem is registered.

### Task 2: Port and certify only the banked helper layer

**Files:**

- Create: `ErdosProblems/Erdos23GapGBTwoDefectFinal.lean`
- Do not create: `.github/workflows/verify-erdos23-two-defect.yml`
- Do not create: `.github/workflows/apply-two-defect-patch.yml`
- Do not create: `scripts/agent_two_defect_patch.py`

**Step 1: Reproduce the certified helper source**

Copy the 304-line Lean module from commit `2d98b64:ErdosProblems/Erdos23GapGBTwoDefectFinal.lean` into the new main-worktree file. Its initial public surface is exactly:

```lean
theorem activeLevelSet_high_card_le_two ...
theorem IsGeodesic.levelAligned_of_twoSidedAnchors ...
theorem IsGeodesic.pair_spanTwo_geometry ...
```

Do not port the branch-local CI or compressed patch runner. The later pure-overlap payload failed decompression and is not kernel evidence.

**Step 2: Target-build the helper module**

Run:

```bash
lake build ErdosProblems.Erdos23GapGBTwoDefectFinal
```

Expected: success, with each helper reporting only `[propext, Classical.choice, Quot.sound]`.

**Step 3: Check the helper diff**

Run:

```bash
git diff --check -- ErdosProblems/Erdos23GapGBTwoDefectFinal.lean
rg -n '\bsorry\b|\badmit\b|native_decide|approx_bound_for_cuberoot4' ErdosProblems/Erdos23GapGBTwoDefectFinal.lean
```

Expected: clean diff; the forbidden-token scan prints nothing.

### Task 3: Complete the common singleton and level-profile constructors

**Files:**

- Modify: `ErdosProblems/Erdos23GapGBTwoDefectFinal.lean`
- Reuse: `ErdosProblems/Erdos23GapGBTwoDefectAlignment.lean`
- Reuse: `ErdosProblems/Erdos23GapGBTwoDefect.lean`

**Step 1: Add the saturated-singleton normal form**

Prove the smallest common lemma needed by all four branches: if a canonical component is a singleton with interval `Ico a (a + 2)`, its unique vertex has rooted level `a + 1` and is adjacent to `P.getVert a` and `P.getVert (a + 2)`. Reuse `attachment_extrema_of_interval_eq_length`, `Finset.card_eq_one`, and `IsGeodesic.rootDist_getVert`.

**Step 2: Add ordinary endpoint anchors**

Package corridor vertices and saturated singleton vertices into the `hxNext`/`hxPrev` hypotheses of `IsGeodesic.levelAligned_of_twoSidedAnchors`. Keep the result local and shape-parametric rather than duplicating four versions.

**Step 3: Add literal level-cut capacity plumbing**

Define capacity from off-corridor BFS fibers using `levelLayer_card_eq_one_add_offLevelFiber_card`, `cutSize_levelUpperCut_le_layerProduct`, and the existing root/stub identities. Prove the generic relation

```lean
capacity r = x r + x (r + 1) + x r * x (r + 1)
```

for the relevant fiber count `x`.

**Step 4: Compile the shared layer**

Run:

```bash
lake build ErdosProblems.Erdos23GapGBTwoDefectFinal
```

Expected: success before any shape closure is attempted.

### Task 4: Close pure overlap first

**Files:**

- Modify: `ErdosProblems/Erdos23GapGBTwoDefectFinal.lean`

**Step 1: Extract the canonical component family and interval cover**

From `hpure : PureOverlapShape ...`, use the all-nonbridge cover equality and `canonical_pureOverlap_two_double_coordinates` to obtain distinct high coordinates `j` and `k` with multiplicity two and baseline multiplicity one elsewhere.

**Step 2: Prove all legal same-side rows are level-aligned**

For each demand endpoint, split corridor/off-corridor with `IsGeodesic.eq_getVert_or_eq_offVertex_of_level`; use the common singleton anchors, coloring parity, and `IsGeodesic.levelAligned_of_twoSidedAnchors`. Explicitly discharge the duplicated-interval/same-level case using shared corridor neighbors and `hlegal`.

**Step 3: Derive the two-high-column capacity bound**

Translate overlap multiplicity to adjacent off-level fiber counts. At baseline columns the capacity is `1`; at `j,k`, the two nonnegative fiber counts sum to `2`, so their product is at most `1` and capacity is at most `3`.

**Step 4: Apply the banked aligned landing**

Finish the exact requested theorem:

```lean
theorem totalCost_le_rlBudget_of_pureOverlap_allNonbridge_sameSide ...
```

using `totalCost_le_rlBudget_of_aligned_twoHighRootLevelProfile`.

**Step 5: Target-build and inspect axioms**

Run:

```bash
lake build ErdosProblems.Erdos23GapGBTwoDefectFinal
lake env lean ErdosProblems/Erdos23GapGBTwoDefectFinal.lean
```

Expected: theorem compiles and `#print axioms` is exactly the permitted three axioms.

### Task 5: Close mixed mass/span

**Files:**

- Modify: `ErdosProblems/Erdos23GapGBTwoDefectFinal.lean`

**Step 1: Extract the unique size-two span-two component**

Unpack `MassSpanShape`; convert its interval-card fact to `Ico a (a + 2)` and apply `IsGeodesic.pair_spanTwo_geometry` to name `anchor` and `tip` with levels `a+1` and `a+2`.

**Step 2: Prove ordinary alignment and classify tip rows**

Use the common ordinary endpoint lemma for all rows not incident with `tip`. Show every unaligned legal tip row has threshold span at most `d-2` and graph distance at most span plus two.

**Step 3: Prove uniqueness with the corrected suffix cut**

Use `levelUpperCut (G.dist w) (a + 2)`, not the literal singleton `{tip}`. Prove its cut size is at most two even when the optional tip-to-corridor chord is present; apply RFC to show at most one exceptional row.

**Step 4: Build the profile and apply the one-exception landing**

Use at most the two columns adjacent to the tip level as `high`. If no exceptional row exists, apply the aligned landing; otherwise choose the unique row and apply `totalCost_le_rlBudget_of_one_addTwo_levelCuts` with `pureSpan_addTwo_exception_envelope`/the corresponding banked `d-2` envelope.

**Step 5: Target-build**

Run `lake build ErdosProblems.Erdos23GapGBTwoDefectFinal` and expect success.

### Task 6: Close mixed mass/overlap

**Files:**

- Modify: `ErdosProblems/Erdos23GapGBTwoDefectFinal.lean`

**Step 1: Extract the size-two span-three macro-block**

Unpack `MassOverlapShape`, name its two component vertices and rooted levels, and use `canonical_massOverlap_unique_double_coordinate` for the unique overlap coordinate.

**Step 2: Localize every possible unaligned row**

Prove ordinary rows aligned. Show the only candidates are the left-contact and right-contact pairs at level difference two; each has graph distance at most four and hence exactly four under `hlegal`.

**Step 3: Charge the explicit two-edge contact cuts**

Construct the left and right suffix/component cuts from the mathematical proof. In either contact case prove cut size at most two and use RFC to bound the candidate set by one.

**Step 4: Apply the aligned/one-exception landing**

Use the macro-block middle coordinate and the unique overlap coordinate as the at-most-two high columns. Dispatch on whether the exceptional candidate set is empty.

**Step 5: Target-build**

Run `lake build ErdosProblems.Erdos23GapGBTwoDefectFinal` and expect success.

### Task 7: Close pure span, including the terminal stub

**Files:**

- Modify: `ErdosProblems/Erdos23GapGBTwoDefectFinal.lean`
- Reuse: `IsGeodesic.singleton_spanZero_pendant_geometry`
- Reuse: `IsGeodesic.pureSpan_leaf_distance_le_clippedLevelDist_add_two`

**Step 1: Extract the unique pendant singleton**

Unpack `PureSpanShape`, name its unique span-zero component/vertex, and apply the banked pendant geometry to obtain its sole corridor neighbor and rooted level.

**Step 2: Prove all non-leaf rows aligned and leaf exceptions unique**

Use the banked pure-span regular geometry/alignment lemmas. Every unaligned row is incident with the leaf; RFC on `{leaf}` and cut size one gives at most one exceptional row.

**Step 3: Handle an interior attachment**

Use actual BFS levels, at most two high columns, exceptional surcharge `+2`, and exceptional threshold span at most `d-2`; apply `totalCost_le_rlBudget_of_pureSpan_twoHighColumns` or its level-cut wrapper.

**Step 4: Handle attachment at `x₀`**

Keep the actual leaf level `d+1`, define the clipped threshold level `min (G.dist w v) d`, prove all corridor threshold cuts are unchanged, bound the exceptional span by `d-1`, and apply `totalCost_le_rlBudget_of_pureSpan_stubBaselineColumns`.

**Step 5: Target-build**

Run `lake build ErdosProblems.Erdos23GapGBTwoDefectFinal` and expect success in both subcases.

### Task 8: Add the final five-shape dispatcher

**Files:**

- Modify: `ErdosProblems/Erdos23GapGBTwoDefectFinal.lean`

**Step 1: Obtain the canonical five-shape disjunction**

Instantiate `IsGeodesic.canonical_twoDefect_five_shapes color hP` with `hs` and `htwo`.

**Step 2: Dispatch every branch**

Apply, respectively:

```lean
totalCost_le_rlBudget_of_q3PureMass_allNonbridge_sameSide
totalCost_le_rlBudget_of_q2q2PureMass_allNonbridge_sameSide
totalCost_le_rlBudget_of_massSpan_allNonbridge_sameSide
totalCost_le_rlBudget_of_massOverlap_allNonbridge_sameSide
totalCost_le_rlBudget_of_pureSpan_allNonbridge_sameSide
totalCost_le_rlBudget_of_pureOverlap_allNonbridge_sameSide
```

The pure-mass disjunction is nested inside the first canonical shape. Do not use `hpairInjective` to strengthen RFC or assume endpoint-load bounds; it is available only where the existing pure-mass closure requires distinct unordered pairs.

**Step 3: Print and inspect axioms**

Add:

```lean
#print axioms totalCost_le_rlBudget_of_twoDefect_allNonbridge_sameSide
```

Run the targeted build. Expected axioms: `[propext, Classical.choice, Quot.sound]`.

### Task 9: Wire the theorem into the proof manifest

**Files:**

- Modify: `ErdosProblems.lean`
- Modify: `Audit.lean`
- Modify: `proofs.yaml`
- Modify: `README.md`
- Regenerate: `attestations.json`

**Step 1: Add aggregate and audit imports**

Add `import ErdosProblems.Erdos23GapGBTwoDefectFinal` to both `ErdosProblems.lean` and `Audit.lean` in the Erdős 23 import group.

**Step 2: Register the audited theorem**

Inside Audit’s manifest-tracked unconditional section, add:

```lean
#print axioms Erdos23GapGBTwoDefectFinal.totalCost_le_rlBudget_of_twoDefect_allNonbridge_sameSide
```

Add the matching `proofs.yaml` entry for Erdős problem 23, with `axioms_clean: true` and the exact theorem/file names.

**Step 3: Add the README index row**

Describe this as the unconditional `d = 2s - 2` internal-cost closure, not as a broader unresolved row.

**Step 4: Regenerate attestations**

Run:

```bash
python3 scripts/emit_attestations.py
```

Expected: `attestations.json` changes only by the deterministic new registration.

### Task 10: Run the complete proof gate and bank only the verified scope

**Files:**

- Verify all files above
- Preserve every Erdős 686 path

**Step 1: Run static hygiene**

```bash
git diff --check
rg -n '\bsorry\b|\badmit\b|native_decide|approx_bound_for_cuberoot4' ErdosProblems/Erdos23GapGBTwoDefectFinal.lean
```

Expected: no output from either failure scan.

**Step 2: Run the repository gates**

```bash
lake build
bash scripts/check_axioms.sh
bash scripts/check_manifest.sh
python3 scripts/emit_attestations.py
git diff --exit-code -- attestations.json
```

Expected: all commands exit zero; the manifest count increases consistently; the final theorem uses only the permitted standard axioms.

**Step 3: Verify foreign WIP remains untouched**

```bash
git status --short
git diff --name-only
git diff --cached --name-only
```

Expected: no Erdős 686/campaign686 path in the tracked or staged diff.

**Step 4: Make a scoped verified commit on `main`**

Stage only:

```bash
git add docs/plans/2026-07-13-erdos23-full-solve.md \
  ErdosProblems/Erdos23GapGBTwoDefectFinal.lean \
  ErdosProblems.lean Audit.lean proofs.yaml README.md attestations.json
git diff --cached --name-only
git commit -m "Close Erdős 23 two-defect boundary"
```

Expected: the commit contains only the listed paths. Do not push unless separately requested or already included in the active-goal instruction.
