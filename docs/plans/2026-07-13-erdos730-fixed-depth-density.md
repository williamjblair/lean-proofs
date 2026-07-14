# Erdős 730 fixed-depth density implementation plan

> **For Codex:** Execute this plan in order, keeping the analytic majorant independent of the event-counting ledger.

**Goal:** Formalize the fixed-depth analytic passage behind equations (37)--(42): a concrete normalized majorant converging to the expected Mertens mass, with no density or event-count assumptions.

**Architecture:** Use the relaxed full lower-half digit box.  Its exact density is
`4⁻ʳ * (1 + 1 / p)^(2*r)`, whose weighted difference from `4⁻ʳ / p` is bounded by a summable `O_r(p⁻²)` term.  Package the remaining Fourier discrepancy, terminal `p^r` blocks, and per-prime `+1` terms as explicit finite sums over the real-cutoff fixed-depth prime band.  Prove each error tends to zero and combine this with the existing Mertens band theorem.

**Tech stack:** Lean 4, Mathlib asymptotics/summability/Chebyshev, existing `Erdos730PrimeBands` and `Erdos730FixedDepthFourier` surfaces.

---

### Task 1: Define the exact band, relaxed density, and analytic majorant

**Files:**
- Create: `ErdosProblems/Erdos730FixedDepthDensity.lean`
- Create: `ErdosProblems/Erdos730FixedDepthDensityAudit.lean`

1. Reuse the real-cutoff/floor prime band from `Erdos730PrimeBands`.
2. Define the relaxed density and prove its exact closed form.
3. Define explicit density, Fourier, terminal-block, and `+1` error sums.
4. Define their sum as the fixed-depth normalized analytic majorant.

### Task 2: Prove the density correction is summable

1. Prove an explicit bound for `(1 + 1/p)^(2*r) - 1` by `C_r / p`.
2. Deduce the weighted correction is bounded by `C_r / p^2`.
3. Dominate the finite prime-band sum by the tail of `sum n⁻²` and prove convergence to zero.

### Task 3: Prove the Fourier discrepancy tail is negligible

1. Use the final fixed-depth Fourier constant/surface where available.
2. Prove summability of `(1 + log n)^(2*r+1) / n^(3/2)` by comparison with a `p`-series.
3. Bound the band sum by its natural-number tail and prove it tends to zero.

### Task 4: Prove terminal and `+1` errors are negligible

1. Bound the `+1` sum by the band upper cutoff divided by `X`.
2. Bound `sum p^r` by `U^r * primeCounting U`.
3. Apply Mathlib's Chebyshev upper bound to obtain `o(X)` after normalization.

### Task 5: Assemble and audit

1. Rewrite the density main term through `fixedDepthReciprocalPrimeBand`.
2. Apply `tendsto_fixedDepthReciprocalPrimeBand_nat` and combine all error limits.
3. State a generic comparison/limsup consumer theorem whose only external input is the finite event-count inequality against the concrete majorant.
4. Build the audit module and verify every exported theorem uses only `[propext, Classical.choice, Quot.sound]`.
5. Report the exact remaining event-ledger bridge, if any, for `Erdos730SmallPrimeEvents`.
