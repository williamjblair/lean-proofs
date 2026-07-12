# Erdős 686 Even k=32 Closure Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove unconditionally that no `k=32`, `d>=32` block-product solution exists, using an exact square-root trap followed by a finite prime-field cover that is tractable in the ordinary Lean kernel.

**Architecture:** Reconstruct the `k=32` square-root polynomial data independently, derive a rigorous global interval for the fixed-divisor multiple `m`, and search exact prime fields for a cover of every trapped quotient. If the cover closes, freeze sharded data and formalize only the generic field bridge, cover, archimedean trap, and final row theorem; if it does not, freeze exact survivors and a hostile obstruction audit.

**Tech Stack:** Python 3 exact integers, NumPy only for bulk residue filtering after masks are computed exactly, pytest, Lean 4/mathlib ordinary `decide` only.

---

### Task 1: Freeze the exact k=32 archimedean trap

**Files:**
- Create: `compute/campaign686/agent_t2_even_k32/even_k32_verify.py`
- Create: `compute/campaign686/agent_t2_even_k32/test_even_k32_verify.py`

**Steps:**
1. Reconstruct `S,T,D`, the scale, and the odd fixed divisor without importing generated tables.
2. Check `T^2=S+D`, `deg D=14`, fixed divisor `3221225472`, and the explicit large-gap bases `v0=5603`, `w0=5859`.
3. Prove `22w<=23v` from the exact power bracket `4*45^32<47^32` and certify `D(w)-4D(v)<0` by shifted coefficient positivity.
4. Compute the least integer `B` for which every coefficient of `D(w)+B*T(w)+2B*T(v)-4D(v)` is positive on `v=5603+a`, `w=5859+a+b`.
5. Freeze the exact trap `-B<m<0`, the quotient count `(B-1)/3221225472`, and all minimum coefficients.

### Task 2: Search and minimize a finite-field subcover

**Files:**
- Create: `compute/campaign686/agent_t2_even_k32/even_k32_cover_search.py`
- Modify: `compute/campaign686/agent_t2_even_k32/even_k32_verify.py`
- Modify: `compute/campaign686/agent_t2_even_k32/test_even_k32_verify.py`

**Steps:**
1. For each prime not dividing the fixed divisor, compute exactly the allowed residues of `t` forced by `S(w)=4S(v)` and `T(w)-2T(v)=-fixed*t` over `F_p`.
2. Filter the complete trapped interval with NumPy and record survivor counts after every prime.
3. Greedily search primes up to a bounded ceiling, then minimize the successful order by reverse deletion and local reorder search.
4. If survivors remain, record their exact values and one local witness pair per tested prime; do not claim a cover.
5. If a cover exists, select a kernel-oriented order balancing prime size, residual density, and shard count.

### Task 3: Formalize only if the cover is kernel-tractable

**Files:**
- Create if justified: `ErdosProblems/Erdos686EvenK32Defs.lean`
- Create if justified: `ErdosProblems/Erdos686EvenK32Core.lean`
- Create if justified: `ErdosProblems/Erdos686EvenK32P*.lean`
- Create if justified: `ErdosProblems/Erdos686EvenK32Cover.lean`
- Create if justified: `ErdosProblems/Erdos686EvenK32.lean`

**Steps:**
1. Reuse the proof architecture of `Erdos686EvenK182024.lean` without modifying it or any shared import surface.
2. Generate bounded per-prime Boolean masks and prove each with ordinary `by decide`; shard tables before any declaration approaches the k=18 memory peak.
3. Prove the exact square identity, fixed divisor, sign trap, quotient range, and field bridge.
4. Compile each module directly with `lake env lean`; reject `native_decide`, `sorry`, and added axioms.
5. Print axioms for the final theorem and require exactly `[propext, Classical.choice, Quot.sound]`.

### Task 4: Freeze findings and hostile audit

**Files:**
- Create: `compute/campaign686/agent_t2_even_k32/findings.md`
- Create: `compute/campaign686/agent_t2_even_k32/hostile_audit.md`

**Steps:**
1. Record the exact dependency tree and every quantified coefficient, trap, candidate count, prime, and survivor count.
2. Replay `d=1`, `d=31`, `d=32`, the center boundary, endpoints of the quotient interval, primes dividing the fixed divisor, and local survivors.
3. Distinguish exact-arithmetic closure from kernel-banked closure; if Lean is infeasible, state the exact computational theorem and kernel obstruction separately.
4. Run focused pytest, direct verifier execution, forbidden-token scan, direct Lean builds if created, and `git diff --check`.
5. Freeze SHA-256 hashes without touching shared manifests, registries, `FinalResidual`, or import aggregators.
