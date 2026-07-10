# structure_hunt — Erdős 686 (N=4) survivor structure scans

All artifacts in this directory are produced by exact integer arithmetic
(Python big-int / Fraction, or C u64/u128 with certified 2^60 rational
brackets; every ambiguous floor is emitted and later resolved in big-int).
Sources live in `compute/structure_hunt_src/`.

## Conventions

Small-k (T1/T2/T3/T-A/T-B/T-C) point: `(k, d, A)`, `k = 5..15`, `d >= 221`,
`A = n+1` in the exact N=4 ratio window
`(A+d+k-1)^k <= 4*(A+k-1)^k  &&  4*A^k <= (A+d)^k`, which equals
`A in [F-(k-2), F]`, `F = floor(c_k*d)`, `c_k = 1/(4^(1/k)-1)`
(equivalence verified in `groundwork.py` and re-verified in `ta_recount.py`).
`lambda = floor(c_k)+1`, `q = lambda-1`.  Row `t` (`t = 0,1,2`):

* raw:         `(A+t) |            G_t`,  `G_t = prod_{i=0}^{k-1} (d-t+i)`
* q-relaxed:   `(A+t) | q^k      * G_t`
* lam-relaxed: `(A+t) | lambda^k * G_t`

Large-k (T4/T-D) point: `(k, N, d)` with the n-form window
`(N+d+k)^k <= 4*(N+k)^k && 4*(N+1)^k <= (N+d+1)^k`, i.e.
`d in [floor(g_k*(N+1))+1, floor(g_k*(N+k))]`, `g_k = 4^(1/k)-1`, and
`d >= k` (points with `d < k` counted "degenerate", not scanned).
Pure row `a >= 1`: `(N+a) | prod_{i=1..k} (d+i-a)` (block `[d+1-a, d+k-a]`).
Row `a = 0`: `N | prod_{i=1..k}(d+i) - 4*k!`.

Half-decade bucket `b` = largest b with `10^(b/2) <= d` (so bucket 4 =
[100, 316), bucket 12 = [10^6, 10^6.5), ...).

## Files — groundwork

* `c_scaled_small_k.json` — certified `p_lo(k) = floor(c_k * 2^60)` and the
  lambda table for k = 5..15 (`groundwork.py`).
* `gamma_scaled_large_k.txt` — certified `g_lo(k) = floor(g_k * 2^60)`;
  k = 16..3000 from `groundwork.py`, extended to k <= 6500 by
  `td_gamma_extend.py` (25 old entries re-certified on rewrite).

## Files — T1 (two-row survivor scan, k = 5..15)

Scan ranges: d <= 1e8 (k <= 9), 3e8 (k = 10,12,14,15), 1e9 (k = 11,13).
Producer: `t1_scan.c` via `t1_driver.py`; cross-validated against an
independent big-int scan for d <= 3000 (`validate_t1.py`) and independently
re-derived for d <= 1e6 (`ta_recount.py`, see below).

* `t1_surv01_k{5..15}.csv` — every window point passing rows 0 AND 1 in the
  lam- or q-relaxation. Columns: `k,d,A,p01_lam,p01_q,p01_raw,p012_lam,
  p012_q,p012_raw` (`p01_*` = rows {0,1} pass, `p012_*` = rows {0,1,2} pass,
  per variant).  raw ⊆ q, raw ⊆ lam; q and lam are incomparable.
* `t1_counts.json` — merged per-bucket counters.  `buckets[k][b]` is a list
  in the order given by `columns`.  CAVEAT: the leading `bucket_lo` value is
  corrupted by the merge (it was summed across scan chunks); derive the edge
  from the bucket key b as 10^(b/2) instead.  `ambiguous_d` lists the two
  (k=13) d values skipped by the C floor bracket; both are resolved in
  `ta_recount_report.json` (no survivors there).

## Files — T2 (anatomy of the 45 banked three-row survivors)

Input: `../constant_prefix3_survivors.json` (the 45 banked (k,q,d,A)).

* `t2_covering_patterns.json` / `.txt` — per survivor, per row t = 0,1,2:
  factorization of A+t, which window elements cover each prime power, where
  q^k / lambda^k slack is needed (`t2_anatomy.py`).
* `t2_u_coordinate_stats.txt` — u = lambda*d - A coordinate stats, largest
  prime of A+t vs affine terms, greedy covers (`t2_stats.py`).

## Files — T4 (large-k prefix scan, k in [16,3000], N <= 1e7)

Producer: `t4_scan.c` via `t4_driver.py`; cross-validated by `validate_t4.py`.

* `t4_prefix_survivors.csv` — all points whose pure rows 1..7 pass.
  Columns: `k,N,d,a0_pass,first_fail_pure,P_N15,cap15` where
  `first_fail_pure` = first failing pure row in 1..16 (17 = none),
  `P_N15` = largest prime of N+15, `cap15` = d+k-15.
* `t4_firstfail_hist.csv` — per-k histogram of the first failing pure row
  (npoints = 32,363,523,859; degenerate d<k points skipped: 7,740,416).
* `t4_cluster_anatomy.json` — row-by-row anatomy of representatives of the
  N = 48502/48503 cluster + smoothness profile of moduli 48496..48521
  (`t4_cluster_anatomy.py`).

## Files — this session (T-A/T-B/T-C/T-D)

* `ta_recount_report.json` (`ta_recount.py`) — T-A: independent recount of
  all two-row survivors for d <= 1e6, all k.  Fresh implementation path
  (Fraction bracket floors + numpy int64 exact modular products + big-int
  rows 1-2; window formula re-checked against the banked bignum predicate on
  random samples).  Result: exact match with the CSVs, row sets and all
  bucket counters (buckets 4..11), for every k; the two ambiguous k=13
  d values (401710996, 803421992) contain NO two-row survivors.
* `tb_family_report.json` / `tb_survivor_details.json` (`tb_families.py`) —
  T-B on the q-relaxed two-row survivors: certified CF convergents /
  semiconvergents of c_k vs A/d, small linear relations
  (|a|,|b| <= 200, |c0| <= 5000), slack cofactors s_t (the part of A+t the
  q^k slack must cover), full divisor anatomy of A and A+1 with large-prime
  block pattern codes, half-decade growth (cross-checked against
  t1_counts c01_q), consecutive-gap ratios, same-slope families.
* `tb_verdict.json` (`tb_verdict.py`) — T-B verdict data: reduced
  denominator q' = d/gcd(A,d) distributions per half-decade, tail structured
  fractions, per-family window-strip bounds m <= (k-1)/(q'c_k - p') (exact
  rationals) and AP structure of the m-values.
* `tc_row2_gcd.json` (`tc_row2_gcd.py`) — T-C: exact
  gcd(A+2, q^k*G_2) for every q-relaxed two-row survivor, failure ratio
  (A+2)/gcd distributions, near-miss counts, and an unconditioned
  mid-window control sample for comparison.
* `td_deep_survivors_new_regions.csv`, `td_firstfail_hist_new_regions.csv`
  (`td_scan.c` via `td_driver.py`) — T-D extension scan over the regions the
  old T4 scan did not cover: k in [3001,6500] x N <= 1e7 and
  k in [16,6500] x N in (1e7, 3e7].  145,762,074,292 window points; the
  survivor file is EMPTY (no point passes pure rows 1..15); histogram
  columns ff1..ff18 + none.  10 ambiguous (k,N) floor pairs were skipped by
  the C scan and resolved exactly in `td_anatomy.py` (15 points, max
  first-fail 6 — nowhere near deep).
* `td_deep_census.json` / `.txt` (`td_anatomy.py`) — T-D census: ALL 207
  points with k >= 16, N <= 3e7 passing pure rows 1..15 (window and rows
  re-verified in big-int), each with first failing row, failing prime
  anatomy, mechanism class, escape-row census over j in [1,k], and
  P(N+j) for j = 1..18; aggregated per N-cluster.

## Headline results

* T-A: CSVs and counters independently confirmed for d <= 1e6; the two
  skipped d values are empty. No mismatches anywhere.
* T-B: two-row survivors do NOT collapse into finitely many parametrized
  families.  Rational-slope families A/d = p'/q' exist (each PROVABLY
  finite: window strip m <= (k-1)/(q'c_k - p'), bound saturated by the
  observed families, e.g. the perfect-AP k=13 family 6336/713 with
  m = 347+391j, j = 0..5), but the large-d tail is dominated by
  gcd(A,d)-small sporadic divisor coincidences (tail q'<=1e4 fraction ~0 for
  most k) with slowly decaying half-decade counts and NO shared linear
  relations, recurrences, or ratio patterns.
* T-C: row 2 fails HARD on two-row survivors: median gcd(A+2, q^k G_2) is
  2..4 (60-65% have gcd <= 10), median failure ratio ~1e4, statistically
  indistinguishable from unconditioned control points.  Only 2-5% are
  ratio<=100 near misses.  Three-row survivors: exactly the 45 banked ones,
  none beyond d = 7029 despite scans to 1e8..1e9.
* T-D: census complete for k in [16,6500], N <= 3e7: exactly 207 deep
  points, all in clusters N in {48502, 3177026, 3177027}; the first failing
  row is ALWAYS (207/207) a single prime p | N+a with NO multiple of p in
  the row block; 64-69% of ALL rows j in [1,k] of these points have such a
  no-multiple prime.
