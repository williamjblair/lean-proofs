# PROGRESS.md - Erdős Problem #686

Date: 2026-07-07  
Active Lean file: `ErdosProblems/Erdos686.lean`  
Current formal lane: disprove the universal positive statement by proving `N = 4` has no quotient representation.

Repo-local update, 2026-07-07:

- [R] This progress file has been added to the `codex/erdos686-proof-wip` branch as `PROGRESS_Erdos686.md`.
- [R] The local checked Lean file is `ErdosProblems/Erdos686.lean`, not `Erdos686(2).lean`.
- [R] The bounded-prefix bridge from the `a <= 8` escape target to the full `N = 4` counterexample target has been banked:

```lean
theorem no_solution_four_of_polynomial_prefix_eight_escape
theorem erdos686_false_of_polynomial_prefix_eight_escape
```

- [R] The local `a = 8` large-prime support step has been banked:

```lean
theorem polynomial_prefix_eight_escape_of_large_prime_in_n_add_eight
```

  If a prime `p` satisfies `d + k - 8 < p` and `p ∣ n + 8`, then the
  `a = 8` polynomial congruence fails.  The proof is fully elementary: the
  congruence identifies `H_{k,d}(8)` with the row product
  `shiftedDiffProductAt k d 8`, then prime support in that product would force
  `p ≤ d + i - 8 ≤ d + k - 8`, contradiction.

- [R] The next finite-prime reduction wrapper has also been banked:

```lean
theorem polynomial_prefix_eight_escape_of_prefix_seven_failure_or_large_prime
```

  Thus the bounded `a <= 8` escape would follow if either some prefix congruence
  already fails for `a <= 7`, or a prime `p > d + k - 8` divides `n + 8`.

- [R] The `k >= 8` conditional ratio-window reduction has been banked:

```lean
theorem polynomial_prefix_eight_escape_in_ratio_window_of_prefix_seven_large_prime
```

  This proves the bounded `a <= 8` escape from the prefix-seven large-prime
  theorem throughout the ratio window for every `k >= 8`.

- [R] A final two-obligation conditional reduction has been banked:

```lean
theorem erdos686_false_of_small_prefix_escape_and_prefix_seven_large_prime
```

  To refute the universal Erdős 686 statement via `N = 4`, it now suffices to
  prove:

```text
1. direct bounded-prefix escape for 5 <= k <= 7;
2. prefix-seven large-prime forcing for k >= 8.
```

- [R] A sharper small-case version has also been banked:

```lean
theorem erdos686_false_of_small_prefix_three_escape_and_prefix_seven_large_prime
```

  This matches the exact small-`k` scan: for `5 <= k <= 7`, it is enough to
  prove a failed polynomial congruence among `a = 0,1,2,3`, together with the
  same `k >= 8` prefix-seven large-prime theorem.

- [X] The previously recommended bounded-prefix escape is false:

```lean
theorem polynomial_prefix_eight_escape_in_ratio_window
```

  Exact counterexample:

```text
(k,n,d) = (167,34235,286)
```

  This triple satisfies the `N = 4` ratio window and the polynomial
  congruences for `a = 0,...,8`; its first failed congruence is at `a = 9`.

- [X] The proposed support theorem
  `prefix_seven_forces_large_prime_in_n_add_eight` is also false.  Exact
  counterexample:

```text
(k,n,d) = (113,30171,373)
n+8 = 30179 = 103 * 293
d+k-8 = 478
```

  The triple passes congruences `a = 0,...,7`; both prime factors of `n+8`
  are at most the row cap `d+k-8`, so no large prime is available to force the
  `a = 8` escape.

- [C] The repaired polynomial-prefix candidate from the previous pass was:

```lean
theorem polynomial_prefix_fifteen_escape_in_ratio_window
```

  No proof of this theorem is currently banked.  It is no longer the best
  primary target, because the newer row-only evidence points to the cleaner
  row-prefix-sixteen theorem below.

- [R] Generic and prefix-15 bridge wrappers have been banked:

```lean
theorem no_solution_four_of_polynomial_prefix_escape
theorem no_solution_four_of_polynomial_prefix_fifteen_escape
theorem erdos686_false_of_polynomial_prefix_escape
theorem erdos686_false_of_polynomial_prefix_fifteen_escape
```

  These say that any fixed true finite-prefix escape theorem, including the
  repaired `B = 15` candidate, would still refute the universal Erdős 686
  statement via `N = 4`.

- [R] Additional exact ratio-window linear bounds have been banked for the small
  prefix-scan boundary cases:

```lean
lemma k_six_ratio_window_linear_bounds
lemma k_seven_ratio_window_linear_bounds
```

- [R] The repo-local exact verifier for the refuted prefix claims is:

```text
compute/erdos686_prefix_counterexamples.py
```

  It checks the four recorded triples by exact integer arithmetic, including
  the ratio window, the first failed congruence, and the factorization of
  `n+8`.

- [E] GPT Pro's next exact search did not find fixed polynomial-prefix
  counterexamples for `C = 15, 20, 30, 50`.  The stronger useful signal was
  row-only: for `C = 16`, an exact row-prefix scan over `k = 5..1200`,
  `n ≤ 500000` checked `381,194,322` ratio-window triples and found no
  survivors through rows `j = 1,...,16`.

- [X] Row-only prefix `15` is false.  GPT Pro's exact search found 22 row
  survivors through `j = 1,...,15`, all with `n = 48502`; every one fails the
  boundary polynomial congruence `a = 0`.  The first listed survivor is:

```text
(k,n,d) = (244,48502,277)
```

  It dies at row `j = 16` because `n+16 = 48518 = 2 * 17 * 1427`, and the
  prime `1427` is absent from the row interval.

- [C] The current best replacement theorem is now row-prefix-sixteen escape,
  not merely a larger polynomial prefix:

```lean
theorem row_prefix_sixteen_escape_in_ratio_window
    {k n d : ℕ}
    (hk : 5 ≤ k)
    (hd : k ≤ d)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1)^k ≤ (n + d + 1)^k) :
    ∃ j, j ∈ Finset.Icc 1 k ∧ j ≤ 16 ∧
      ¬ n + j ∣ shiftedDiffProductAt k d j
```

  This theorem is not proved.

- [R] The row-prefix-sixteen bridges have been banked in Lean:

```lean
theorem no_solution_four_of_row_prefix_sixteen_escape
theorem erdos686_false_of_row_prefix_sixteen_escape
theorem polynomial_prefix_sixteen_escape_of_row_prefix_sixteen_escape
theorem polynomial_prefix_sixteen_escape_in_ratio_window_of_row_prefix_sixteen_escape
```

  These make the row-prefix theorem a direct target for closing the `N = 4`
  branch, and also recover the polynomial-prefix-sixteen escape if needed.

- [R] The local large-prime support for row-prefix-sixteen has also been banked:

```lean
theorem row_escape_of_large_prime_in_n_add
theorem row_prefix_sixteen_escape_of_large_prime_in_prefix
```

  If a prime divisor of `n+j` is larger than every shifted row factor
  `d+i-j`, then row `j` fails.  The prefix version turns such a prime in one of
  the first sixteen lower terms into the row-prefix-sixteen escape.  This is
  the Lean-bankable local mechanism behind GPT Pro's `j = 16` explanation for
  the first row-prefix-15 survivor.

- [R] The contrapositive smoothness package has now been banked:

```lean
theorem row_dvd_prime_le_row_cap
theorem row_dvd_smooth_up_to_row_cap
theorem row_prefix_sixteen_survivor_smooth
theorem row_smooth_of_four_gap_solution
```

  Thus any surviving row `j` forces every prime divisor of `n+j` to be at most
  the sharper row cap `d+k-j`; in particular, any counterexample to the current
  row-prefix-sixteen target would have all of `n+1,...,n+16` capped-smooth under
  their row-specific caps.  Any genuine cleared `N = 4` gap-form solution has
  this row-specific smoothness for every lower-block row.

- [E] Exact row-cap smoothness scanning shows that smoothness alone is far too
  weak to close the row-prefix-sixteen target.  The repo-local scanner is:

```text
compute/erdos686_row_smooth_scan.py
```

  Exact run:

```text
python3 compute/erdos686_row_smooth_scan.py \
  --kmin 5 --kmax 50 --nmax 100000 --prefix 16 --examples 2 --check-rows
```

  Result:

```text
total ratio-window triples:        6,222,909
row-cap smooth survivors:            128,330
row-prefix divisibility survivors:         0
first-row failure bucket:             126,263
second-row failure bucket:              2,021
third-row failure bucket:                  43
fourth-row failure bucket:                  3
```

  So the current proof target should be treated as a two-filter obstruction:
  first remove nonsmooth candidates using prime-support bounds, then prove that
  the remaining capped-smooth candidates still fail an explicit row congruence.

- [R] The two-filter bridge matching that scan architecture has been banked:

```lean
theorem no_solution_four_of_row_prefix_sixteen_smooth_or_row_escape
theorem erdos686_false_of_row_prefix_sixteen_smooth_or_row_escape
```

  A proof that every ratio-window candidate either has a nonsmooth first-sixteen
  lower term under its row cap, or has a failed row divisibility among
  `j = 1,...,16`, would refute the universal statement via `N = 4`.

- [R] The transition-denominator package suggested by GPT Pro has been banked
  locally in Lean:

```lean
theorem skeletonQuotient_succ_relation_of_row_divisibilities
theorem transitionDenom_dvd_skeletonQuotient_of_adjacent_rows
theorem row_succ_dvd_of_transitionDenom_dvd_skeletonQuotient
theorem transitionDenom_dvd_skeletonQuotient_iff_row_succ_dvd
theorem transitionDenom_not_dvd_skeletonQuotient_of_large_prime_next
theorem row_sixteen_escape_after_rows_fifteen_of_large_prime_n_add_sixteen
theorem row_sixteen_escape_after_rows_fifteen_of_large_prime_n_add_sixteen_uncanceled_edge
theorem row_sixteen_escape_after_rows_fifteen_of_large_prime_n_add_sixteen_large
theorem row_sixteen_escape_after_rows_fifteen_of_n_add_sixteen_not_smooth
theorem row_prefix_sixteen_escape_of_large_prime_boundary_and_small_k_escape
theorem row_prefix_sixteen_escape_of_large_prime_boundary_edge_and_small_k_escape
theorem row_prefix_sixteen_escape_of_large_prime_boundary_large_and_small_k_escape
theorem row_prefix_sixteen_escape_of_n_add_sixteen_not_smooth_boundary_and_small_k_escape
theorem row_prefix_sixteen_escape_of_transition_denominator_escape
theorem row_prefix_sixteen_escape_of_boundary_and_small_k_escape
theorem row_sixteen_escape_after_rows_fifteen_iff_transition_fifteen_escape
theorem row_prefix_sixteen_escape_of_transition_fifteen_and_small_k_escape
```

  Here

```lean
transitionDenom k n d j =
  ((n + j + 1) * (d + k - j)) /
    Nat.gcd ((n + j + 1) * (d + k - j)) ((n + j) * (d - j))
```

  The key formal result is the iff: assuming the current row `j` divides,
  transition-denominator divisibility is equivalent to divisibility of the next
  row `j+1`.  Thus the transition denominator is not a separate global escape
  mechanism; it repackages the next-row obstruction exactly.  The final bridge
  shows that any genuine transition-denominator escape theorem implies the
  existing row-prefix-sixteen escape target.

- [R] The local prime mechanism behind the `j = 15` boundary examples has also
  been banked:

```lean
theorem transitionDenom_not_dvd_skeletonQuotient_of_large_prime_next
```

  If row `j` divides, a prime `p` divides `n+j+1`, `p` is larger than the
  current row cap `d+k-j`, and `p` is not canceled by `(n+j)(d-j)`, then
  `transitionDenom k n d j` cannot divide `skeletonQuotient k n d j`.  Thus the
  `k >= 16` boundary theorem may be attacked by proving the existence of such a
  large uncanceled prime in `n+16` at `j = 15`.  The known survivor
  `(k,n,d) = (244,48502,277)` uses exactly this pattern with
  `p = 1427`.

- [R] The prime mechanism has been specialized to the boundary and connected
  back to the row-prefix target:

```lean
theorem row_sixteen_escape_after_rows_fifteen_of_large_prime_n_add_sixteen
theorem row_sixteen_escape_after_rows_fifteen_of_large_prime_n_add_sixteen_uncanceled_edge
theorem row_sixteen_escape_after_rows_fifteen_of_large_prime_n_add_sixteen_large
theorem row_sixteen_escape_after_rows_fifteen_of_n_add_sixteen_not_smooth
theorem row_prefix_sixteen_escape_of_large_prime_boundary_and_small_k_escape
theorem row_prefix_sixteen_escape_of_large_prime_boundary_edge_and_small_k_escape
theorem row_prefix_sixteen_escape_of_large_prime_boundary_large_and_small_k_escape
theorem row_prefix_sixteen_escape_of_n_add_sixteen_not_smooth_boundary_and_small_k_escape
```

  The first theorem says that, after rows `1,...,15` divide, a prime `p` with
  `p ∣ n+16`, `¬ p ∣ n+15`, `¬ p ∣ d-15`, and `d+k-15 < p` forces row `16` to
  fail.  The sharper version proves `¬ p ∣ n+15` automatically from
  `p.Prime` and `p ∣ n+16`, so the boundary hypothesis only needs to exclude
  cancellation by `d-15`.  The largest-prime version also removes that edge
  condition: since `k >= 16` and `k <= d`, `d-15` is positive and smaller than
  any `p > d+k-15`.  The smoothness versions then repackage the same boundary
  as nonsmoothness of `n+16` above the row-15 cap.  The final bridge packages
  the remaining row-prefix-sixteen problem as exactly:

```lean
-- equivalent boundary target, k >= 16
∀ k n d, 16 ≤ k → k ≤ d →
  (n + d + k)^k ≤ 4 * (n + k)^k →
  4 * (n + 1)^k ≤ (n + d + 1)^k →
  (∀ j, j ∈ Finset.Icc 1 15 → n + j ∣ shiftedDiffProductAt k d j) →
  ¬ SmoothUpTo (d + k - 15) (n + 16)

-- plus the separate finite small-k target, 5 <= k <= 15
```

- [E] GPT Pro's transition search found no exact counterexample:

```text
k = 5..1200, n <= 1,000,000:
  1,080,951,228 exact ratio-window triples
  22 row-prefix-15 survivors
  0 transition counterexamples

k = 1201..1700, n <= 2,000,000:
  327,187,982 exact ratio-window triples
  0 row-prefix-15 survivors
  0 transition counterexamples
```

  More detailed run diagnostics from the same GPT Pro pass:

```text
KMIN=5 KMAX=300 NMAX=1000000
total_window=399490707
rows15=22
transition_counterexamples=0
transition_escapes=22
ambiguous=0

KMIN=301 KMAX=1200 NMAX=1000000
total_window=681460521
rows15=0
transition_counterexamples=0
transition_escapes=0
ambiguous=0

KMIN=1201 KMAX=1700 NMAX=2000000
total_window=327187982
rows15=0
transition_counterexamples=0
transition_escapes=0
ambiguous=0
```

  All 22 row-prefix-15 survivors occur at `n = 48502` and fail at the boundary
  row `j = 16`; for example `(k,n,d) = (244,48502,277)` has
  `n+16 = 48518 = 2 * 17 * 1427`, and the transition denominator at `j = 15`
  contains a `1427` factor absent from the row-15 quotient.

- [E] A local exact transition checker has been added at
  `compute/erdos686_transition_scan.py`.  It has a bounded scan mode and a
  single-triple diagnostic mode.  The diagnostic mode independently verifies
  the first GPT Pro survivor:

```text
python3 compute/erdos686_transition_scan.py \
  --triple 244 48502 277 --row-prefix 15 --transition-prefix 15

triple=(244, 48502, 277) ratio_window=[277,277] in_window=True
rows1..15 first_failed_row=None
transitions1..15 first_escape=15
...
j=15 row=True next_row=False denom=12275054 quotient_mod_denom=10253584
denom_factors=[(2, 1), (11, 1), (17, 1), (23, 1), (1427, 1)]
```

  A narrow exact scan over the known survivor height reproduces the whole
  `n = 48502` cluster without relying on the external run:

```text
python3 compute/erdos686_transition_scan.py \
  --kmin 5 --kmax 300 --nmin 48502 --nmax 48502 \
  --row-prefix 15 --transition-prefix 15 \
  --expect-rows 22 --expect-escapes 22 --expect-counterexamples 0

ALL k=5..300 nrange=48502..48502 total_window=352 \
rows15=22 transition_escapes=22 transition_counterexamples=0
first-transition-escape k=244 n=48502 d=277 j=15
first-transition-escape k=245 n=48502 d=276 j=15
first-transition-escape k=246 n=48502 d=275 j=15
first-transition-escape k=247 n=48502 d=273 j=15
first-transition-escape k=247 n=48502 d=274 j=15
```

- [C] The corrected next targets are now split:

```lean
theorem row_sixteen_escape_after_rows_fifteen_in_ratio_window
theorem row_full_escape_small_k_in_ratio_window
```

  For `k >= 16`, rows `1,...,15` make transitions `j <= 14` automatic by the
  iff, so the real boundary is the `j = 15` valuation defect equivalent to row
  `16` failure.  For `5 <= k <= 15`, row-prefix-sixteen is really full-row
  escape and needs a separate small-`k` proof or certified finite reduction.
  The split bridge above proves formally that these two targets together imply
  row-prefix-sixteen escape.

- [R] The `k >= 16` boundary has now been specialized exactly:

```lean
theorem row_sixteen_escape_after_rows_fifteen_iff_transition_fifteen_escape
theorem row_prefix_sixteen_escape_of_transition_fifteen_and_small_k_escape
```

  After rows `1,...,15` divide, failure of row `16` is equivalent to failure of
  `transitionDenom k n d 15 ∣ skeletonQuotient k n d 15`.  Therefore the
  boundary theorem may be proved as the single valuation-defect target at
  `j = 15`, plus the separate `5 <= k <= 15` full-row theorem.

- [R] Current verification status for the new batch:

```text
lake build ErdosProblems.Erdos686          PASS
bash scripts/check_manifest.sh            PASS (298 theorem(s))
lake env lean Audit.lean                  PASS
bash scripts/check_axioms.sh              PASS (298 theorem(s))
rg native_decide/approx_bound/sorry/admit PASS (no hits)
python3 -m py_compile compute/*.py        PASS
python3 compute/erdos686_prefix_counterexamples.py PASS
python3 compute/erdos686_row_smooth_scan.py ... --check-rows PASS
lake build                                PASS
```

  The new theorems depend only on `[propext, Classical.choice, Quot.sound]`.

Status tags used below:

- `[R]` rigorous, proof-ready, or already banked in the Lean file.
- `[E]` exact computational evidence, integer arithmetic only unless explicitly marked as modular evidence.
- `[C]` conjectural or proof strategy not yet complete.
- `[X]` refuted by an exact counterexample.

---

## 0. Executive verdict

[R] The positive statement for Erdős #686 is fully reduced in the Lean file to square values `N = a^2`.

[R] Every nonsquare `N ≥ 2` is already represented with `k = 2`.

[R] Large infinite families of square roots are already represented with `k = 2`, including the uniform Pell/Chebyshev family and explicit witnesses for `9` and `16`.

[R] The intended counterexample remains `N = 4`.

[R] The file already proves the low `N = 4` branches:

```lean
no_solution_four_two
no_solution_four_three
no_solution_four_four
no_solution_four_le_four
```

So the only remaining `N = 4` branch is:

```text
k ≥ 5.
```

[R] For a hypothetical remaining `N = 4` solution, write `m = n + d`. Then the problem is to exclude:

```lean
blockProduct k (n + d) = 4 * blockProduct k n
```

under:

```lean
5 ≤ k,
k ≤ d.
```

[R] The most useful currently active final bridge is the polynomial-congruence bridge. A true `N = 4` gap solution forces:

```lean
((n + a : ℕ) : ℤ) ∣ fourCongruencePolynomial k d a
```

for every natural `a`.

[X] The former bounded-prefix obstruction is false:

```lean
theorem polynomial_prefix_eight_escape_in_ratio_window
    {k n d : ℕ}
    (hk : 5 ≤ k)
    (hd : k ≤ d)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1)^k ≤ (n + d + 1)^k) :
    ∃ a, a ∈ Finset.Icc 0 8 ∧
      ¬ ((n + a : ℕ) : ℤ) ∣ fourCongruencePolynomial k d a
```

[R] Exact counterexample:

```text
(k,n,d) = (167,34235,286)
first failure a = 9
```

[C] The current repaired bounded-prefix candidate is the analogous `a ≤ 15`
statement.  It is not proved.

[X] The previous `a ≤ 7` version is false. Exact counterexample:

```text
(k,n,d) = (80, 28670, 502)
```

It satisfies the ratio window, passes all congruences `a = 0,...,7`, and fails first at `a = 8`.

[R] Full solution is not yet complete. The remaining proof obligation is now sharply isolated.

---

## 1. Core definitions in the Lean file

The active definitions are:

```lean
def blockProduct (k x : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (x + i)

def intBlockProduct (k : ℕ) (x : ℤ) : ℤ :=
  ∏ i ∈ Finset.Icc 1 k, (x + (i : ℤ))

def fourCongruencePolynomial (k d : ℕ) (a : ℤ) : ℤ :=
  intBlockProduct k ((d : ℤ) - a) - 4 * intBlockProduct k (-a)

def shiftedDiffProduct (k d : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 1 k, ∏ i ∈ Finset.Icc 1 k, (d + i - j)

def shiftedDiffProductAt (k d j : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (d + i - j)

def shiftedDiffProductUpperAt (k d j : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (d + j - i)

def centeredDiffProduct (k d : ℕ) : ℕ :=
  ∏ h ∈ Finset.Icc 0 (2 * k - 2), (d + h - (k - 1))

def lowerBlockLcm (k n : ℕ) : ℕ :=
  (Finset.Icc 1 k).lcm (fun j => n + j)

def upperBlockEssentialLcm (k n d : ℕ) : ℕ :=
  (Finset.Icc 1 k).lcm (fun j => (n + d + j) / Nat.gcd (n + d + j) 4)

def oddPart (n : ℕ) : ℕ :=
  ordCompl[2] n

def oddBlock (k x : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, oddPart (x + i)
```

For `1 ≤ j ≤ k`, the polynomial congruence specializes to a row product:

```lean
lemma fourCongruencePolynomial_eq_shiftedDiffProductAt
    {k d j : ℕ} (hd : k ≤ d) (hj : j ∈ Finset.Icc 1 k) :
    fourCongruencePolynomial k d j = (shiftedDiffProductAt k d j : ℤ)
```

For `a = 0`, the congruence is the boundary condition:

```text
n ∣ P_k(d) - 4*k!
```

where `P_k(x) = ∏_{i=1}^k (x+i)`.

---

## 2. Constructive side already banked

### 2.1 Nonsquares

[R] The file proves every nonsquare `N ≥ 2` is represented with `k = 2`:

```lean
theorem nonsquare_representable_k_two
theorem nonsquare_representable
```

[R] The global positive statement is therefore equivalent to square-root coverage:

```lean
theorem erdos686_iff_square_representable
theorem erdos686_false_iff_square_counterexample
```

### 2.2 Square-root families

[R] The file banks multiple explicit square-root families:

```lean
theorem square_family_representable_k_two
theorem square_minus_one_family_representable_k_two
theorem square_pell_third_family_representable_k_two
theorem square_pell_fourth_family_representable_k_two
theorem k2Pell_family_representable_k_two
theorem square_root_mod_four_two_representable
theorem square_root_mod_four_two_minus_one_representable
```

[R] The file also has explicit witnesses:

```lean
theorem nine_representable
theorem sixteen_representable
```

[R] These are constructive and not part of the current negative branch, except as global context: the remaining obstruction to the positive universal theorem can be witnessed by a single square value that is not representable.

---

## 3. `N = 4` branch status

### 3.1 Low branches closed

[R] The file proves:

```lean
theorem no_solution_four_two_cleared
theorem no_solution_four_two
theorem no_solution_four_three
theorem no_solution_four_four
theorem no_solution_four_le_four
```

[R] Hence a remaining `N = 4` solution must have:

```text
k ≥ 5.
```

### 3.2 Gap reduction

[R] The file contains:

```lean
lemma four_solution_with_gap_of_solution
```

This converts a quotient solution with `m ≥ n+k` into gap form with `m = n+d`, `k ≤ d`, and:

```lean
blockProduct k (n + d) = 4 * blockProduct k n
```

### 3.3 Ratio window and linear consequences

[R] A true `N = 4` gap equality implies the exact natural ratio window:

```lean
lemma ratio_window_four_nat
```

Namely:

```lean
(n + d + k)^k ≤ 4 * (n + k)^k
4 * (n + 1)^k ≤ (n + d + 1)^k
```

[R] The file also proves useful linear consequences:

```lean
lemma twice_gap_lt_n_of_ratio_window
lemma difference_block_below_n_of_ratio_window
lemma twice_gap_lt_n_of_four_solution
lemma difference_block_below_n_of_four_solution
```

In particular, under the `N = 4` ratio window:

```text
2*d < n
```

and a stronger centered-window separation consequence is available through `difference_block_below_n_of_ratio_window`.

---

## 4. Current best final route: row-prefix escape

### 4.1 Banked polynomial-congruence bridge

[R] The file proves:

```lean
theorem polynomial_congruence_family_four {k n d a : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    ((n + a : ℕ) : ℤ) ∣ fourCongruencePolynomial k d a
```

[R] Therefore it also proves the final bridge:

```lean
theorem no_solution_four_of_polynomial_congruence_escape
```

and the global false-`Erdos686` bridge:

```lean
theorem erdos686_false_of_polynomial_congruence_escape
```

The remaining theorem can be stated entirely as an escape theorem over the exact ratio window.

### 4.2 Refuted prefix-eight theorem and repaired bridge

[X] The previously active `a ≤ 8` theorem is refuted:

```lean
theorem polynomial_prefix_eight_escape_in_ratio_window
    {k n d : ℕ}
    (hk : 5 ≤ k)
    (hd : k ≤ d)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1)^k ≤ (n + d + 1)^k) :
    ∃ a, a ∈ Finset.Icc 0 8 ∧
      ¬ ((n + a : ℕ) : ℤ) ∣ fourCongruencePolynomial k d a
```

[R] Exact counterexample:

```text
(k,n,d) = (167,34235,286)
```

[C] The repaired polynomial-prefix candidate was the same statement with prefix
`a ≤ 15`, but the current best proof-facing target is the row-prefix-sixteen
escape theorem.

[R] If a true finite-prefix theorem is proved for any fixed bound `B`, the
`N = 4` branch is closed by the generic bridge now banked in Lean. Then the
universal positive statement is false by taking `N = 4`.

### 4.3 Bridge patch banked locally

[R] The bounded-prefix wrapper is now banked directly in
`ErdosProblems/Erdos686.lean`:

```lean
theorem no_solution_four_of_polynomial_prefix_eight_escape
    (hescape : ∀ k n d : ℕ, 5 ≤ k → k ≤ d →
      (n + d + k) ^ k ≤ 4 * (n + k) ^ k →
      4 * (n + 1) ^ k ≤ (n + d + 1) ^ k →
      ∃ a, a ∈ Finset.Icc 0 8 ∧
        ¬ ((n + a : ℕ) : ℤ) ∣ fourCongruencePolynomial k d a) :
    ¬ ∃ k n m : ℕ,
      2 ≤ k ∧ m ≥ n + k ∧
      (4 : ℚ) =
          (∏ i ∈ Finset.Icc 1 k, (((m + i : ℕ) : ℚ))) /
          (∏ i ∈ Finset.Icc 1 k, (((n + i : ℕ) : ℚ)))
```

[R] It is a direct checked wrapper around already banked file theorems:

```lean
no_solution_four_le_four
four_solution_with_gap_of_solution
ratio_window_four_nat
polynomial_congruence_family_four
```

[R] The global false-`Erdos686` bridge for the same bounded-prefix theorem is
also banked:

```lean
theorem erdos686_false_of_polynomial_prefix_eight_escape
```

---

## 5. Exact evidence for the active `a ≤ 8` theorem

### 5.1 Main by-`n` search

[E] Exact integer search checked:

```text
5 ≤ k ≤ 80
0 ≤ n ≤ 100000
ratio-window triples only
```

Output:

```text
KMAX=80 NMAX=100000 PREF=8 total=10234931 passall=0 elapsed=23.5035
bucket=0 count=9530675 examples=(5,11,5) (5,13,5) (5,14,5) (5,14,6) (5,17,6) (5,17,7) (5,18,7) (5,19,7) 
bucket=1 count=580344 examples=(5,12,5) (5,16,6) (5,24,8) (5,24,9) (5,27,9) (5,30,10) (5,30,11) (5,40,14) 
bucket=2 count=98789 examples=(5,15,6) (5,20,7) (5,32,11) (5,50,17) (5,80,27) (5,113,37) (5,125,41) (5,200,65) 
bucket=3 count=19532 examples=(6,90,24) (7,75,17) (7,90,20) (7,90,21) (7,98,22) (7,548,121) (8,98,19) (9,54,10) 
bucket=4 count=4394 examples=(8,53,11) (8,63,13) (9,63,11) (10,63,10) (10,75,12) (11,75,11) (16,637,58) (16,648,59) 
bucket=5 count=974 examples=(17,340,30) (18,374,31) (19,608,47) (19,780,60) (20,608,44) (20,608,45) (20,780,57) (21,608,42) 
bucket=6 count=151 examples=(26,1330,74) (30,1330,64) (41,1271,44) (41,1271,45) (42,1271,43) (42,1271,44) (43,1271,43) (43,5248,172) 
bucket=7 count=71 examples=(42,5248,177) (48,4896,144) (49,4896,141) (50,2622,74) (50,2622,75) (50,4896,138) (50,4896,139) (51,2622,73) 
bucket=8 count=1 examples=(80,28670,502) 
bucket=9 count=0 examples=
```

Interpretation:

- `bucket=a` means `a` is the first failed polynomial congruence.
- `bucket=9` means all congruences `a=0,...,8` passed.
- `bucket=9 count=0`, so there were no survivors through `a=8`.

Script:

```text
pass8_poly_prefix_fast_by_n.cpp
```

Output file:

```text
pass8_poly_prefix_by_n_K80_N100k_pref8.out
```

### 5.2 First `a = 8` examples

[E] The first examples whose first failure is `a = 8` are:

```text
80 28670 502
81 28670 495
81 28670 496
82 28670 489
82 28670 490
83 16165 273
83 28670 483
83 28670 484
84 16165 270
84 28670 478
```

Script:

```text
pass8_find_first8_examples.cpp
```

Output file:

```text
pass8_find_first8_examples.out
```

### 5.3 Why `a = 8` is genuinely necessary

[X] The `a ≤ 7` theorem is false. Exact counterexample:

```text
k=80 n=28670 d=502
ratio_upper=True
ratio_lower=True
k_le_d=True
a modulus remainder divides gcd(remainder,modulus)
0 28670 0 True 28670
1 28671 0 True 28671
2 28672 0 True 28672
3 28673 0 True 28673
4 28674 0 True 28674
5 28675 0 True 28675
6 28676 0 True 28676
7 28677 0 True 28677
8 28678 4628 False 26
9 28679 1785 False 119
10 28680 25440 False 120
11 28681 0 True 28681
12 28682 17876 False 2
block_equality=False
block_delta_sign=1
block_delta_mod_n_plus_8=4628
```

For this triple:

```text
n + 8 = 28678 = 2 * 13 * 1103
```

At `a = 8`, since `8 ≤ k`, the row product is:

```text
shiftedDiffProductAt 80 502 8 = 495 * 496 * ... * 574
```

But:

```text
1103 > 574
```

So `1103 ∣ n+8` and `1103` divides no row factor. Hence the `a=8` congruence fails.

Script:

```text
pass8_prefix7_counterexample_details.py
```

Output file:

```text
pass8_prefix7_counterexample_details.out
```

---

## 6. Refuted large-prime theorem and surviving local lemma

[X] The attempted global large-prime theorem is false.

[X] Refuted intermediate theorem:

```lean
theorem prefix_seven_forces_large_prime_in_n_add_eight
    {k n d : ℕ}
    (hk : 8 ≤ k)
    (hd : k ≤ d)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1) ^ k ≤ (n + d + 1) ^ k)
    (hprefix : ∀ a, a ∈ Finset.Icc 0 7 →
      ((n + a : ℕ) : ℤ) ∣ fourCongruencePolynomial k d a) :
    ∃ p, p.Prime ∧ d + k - 8 < p ∧ p ∣ n + 8
```

Exact counterexample:

```text
(k,n,d) = (113,30171,373)
n+8 = 30179 = 103 * 293
d+k-8 = 478
```

This triple satisfies the ratio window, passes the prefix congruences
`a = 0,...,7`, and has no prime factor of `n+8` above the row cap.

[R] The row failure is now banked as:

```lean
theorem polynomial_prefix_eight_escape_of_large_prime_in_n_add_eight
```

[R] The disjunction wrapper is now banked as:

```lean
theorem polynomial_prefix_eight_escape_of_prefix_seven_failure_or_large_prime
```

Mathematically, the `a = 8` escape follows as follows:

1. If one of `a = 0,...,7` fails, we are done.
2. Otherwise, the theorem gives `p ∣ n+8` with `p > d+k-8`.
3. If the `a=8` congruence held, then because `8 ≤ k`:

```lean
fourCongruencePolynomial k d 8 = shiftedDiffProductAt k d 8
```

4. Since:

```lean
shiftedDiffProductAt k d 8 = ∏ i ∈ Finset.Icc 1 k, (d+i-8)
```

all factors are `≤ d+k-8`.
5. A prime `p > d+k-8` cannot divide the product. Contradiction.

[X] The remaining issue is no longer proving
`prefix_seven_forces_large_prime_in_n_add_eight`; that statement is false.
Any future use of the banked row lemma needs a different source of the large
prime, or a different finite-prefix strategy.

### 6.1 Small-`k` scan after the two-obligation split

[E] Exact integer scan for the small residual cases `k = 5,6,7` found no
survivors through `a = 8` for:

```text
0 <= n <= 1000000
k in {5,6,7}
ratio-window triples only
```

Repo-local reproducibility script:

```text
compute/erdos686_small_prefix_scan.py
```

Smoke check:

```text
python3 -m py_compile compute/erdos686_small_prefix_scan.py
python3 compute/erdos686_small_prefix_scan.py --kmin 5 --kmax 5 --nmax 100 --prefix 3 --examples 3
```

The failures were much earlier than `a = 8`:

```text
k=5 total=1278018 passall=0 buckets=[1277952, 57, 9, 0, 0, 0, 0, 0, 0, 0]
k=6 total=1299583 passall=0 buckets=[1299447, 129, 6, 1, 0, 0, 0, 0, 0, 0]
k=7 total=1314049 passall=0 buckets=[1313826, 209, 9, 5, 0, 0, 0, 0, 0, 0]
```

Here `bucket=a` means `a` is the first failed polynomial congruence, and
`bucket=9` means all congruences `a=0,...,8` passed.  This is evidence only,
but it suggests the small-`k` obligation may be provable with a much shorter
prefix, namely `a <= 3`, rather than the full `a <= 8`.

[R] This shorter-prefix small-case obligation is now reflected in Lean by:

```lean
theorem erdos686_false_of_small_prefix_three_escape_and_prefix_seven_large_prime
```

---

## 7. Previous routes and current status

### 7.1 Lower-lcm centered obstruction

[R] The file banks the central lcm bridge:

```lean
theorem lower_lcm_dvd_centeredDiffProduct_four
```

A true `N = 4` gap solution with `k ≤ d` forces:

```lean
lowerBlockLcm k n ∣ centeredDiffProduct k d
```

[C] Original obstruction target:

```lean
theorem lower_lcm_escape_in_ratio_window
    {k n d : ℕ}
    (hk : 5 ≤ k)
    (hd : k ≤ d)
    (hlo : 4 * (n + 1)^k ≤ (n + d + 1)^k)
    (hhi : (n + d + k)^k ≤ 4 * (n + k)^k) :
    ¬ lowerBlockLcm k n ∣ centeredDiffProduct k d
```

[E] No exact counterexample was found in extensive searches:

```text
5 ≤ k ≤ 30, 0 ≤ n ≤ 100000
3,504,151 ratio-window triples
0 lcm counterexamples
```

```text
5 ≤ k ≤ 70, 0 ≤ n ≤ 100000
8,909,785 ratio-window triples
0 lcm counterexamples
```

```text
5 ≤ k ≤ 18, 5 ≤ d ≤ 100000
14,698,229 ratio-window triples
0 lcm counterexamples
```

```text
5 ≤ k ≤ 28, 5 ≤ d ≤ 30000
11,153,084 ratio-window triples
0 lcm counterexamples
```

[C] This route remains valid, but it is not currently the best target because
the row-prefix-sixteen route is more direct and has a bounded row-divisibility
shape.

### 7.2 Large-prime-only lower-block route

[X] The simple theorem “some lower term has a prime factor above the centered bound” is false.

Exact first hard triple:

```text
(k,n,d) = (5,47,16)
```

Lower terms:

```text
[48, 49, 50, 51, 52]
```

Centered terms:

```text
[12, 13, 14, 15, 16, 17, 18, 19, 20]
```

Factorizations:

```text
lowerBlockLcm factorization
= 2^4 * 3 * 5^2 * 7^2 * 13 * 17

centeredDiffProduct factorization
= 2^10 * 3^4 * 5^2 * 7 * 13 * 17 * 19
```

So the lcm obstruction holds by a `7^2` valuation gap, not by a missing large prime.

[X] This triple is not a true block equality:

```text
blockProduct 5 (47+16) - 4 * blockProduct 5 47 = 3394560 ≠ 0
```

### 7.3 Residual valuation-sum route

[R] A stronger local certificate theorem was isolated:

```lean
theorem lower_lcm_escape_of_prime_power_residual_factorization_sum
```

Informal statement:

If `p^e ∣ n+j`, and residuals

```text
R_h = (n+j) - q*(d+h-(k-1))
```

satisfy a factorization-sum bound:

```text
∑_h v_p(R_h) < e,
```

then:

```lean
¬ lowerBlockLcm k n ∣ centeredDiffProduct k d
```

[E] Every ratio-window triple in:

```text
5 ≤ k ≤ 70, 0 ≤ n ≤ 100000
8,909,785 triples
```

was certified by either absent lower prime or residual-sum prime-power valuation.

Output:

```text
ALL_CERTIFIED KMAX=70 NMAX=100000
ratio_window_triples_checked=8909785
absent=8874895
residual_sum=34890
first_residual_sum=(5,47,16) j=2 p=7 e=2 cv=1 q=1 sum=1
elapsed_seconds=17.91
```

[C] Good local theorem, but global certificate existence is still open. Superseded as primary route by polynomial-prefix strategy.

### 7.4 Two-sided prime support route

[C] Candidate theorem:

```lean
theorem upper_prime_absent_from_lower_in_ratio_window
    {k n d : ℕ}
    (hk : 5 ≤ k)
    (hd : k ≤ d)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1) ^ k ≤ (n + d + 1)^k) :
    ∃ j p,
      j ∈ Finset.Icc 1 k ∧
      p.Prime ∧ p ≠ 2 ∧ k < p ∧
      p ∣ n + d + j ∧
      ∀ i, i ∈ Finset.Icc 1 k → ¬ p ∣ n + i
```

[R] This plugs into the existing odd-block theorem:

```lean
four_blockProduct_eq_implies_oddBlock_eq
oddBlock_eq_upper_term_prime_dvd_lower_term
odd_prime_dvd_oddPart_iff
```

[E] Exact evidence:

```text
MODE=n KMAX=70 BMAX=100000 total=8909785 fail=0
MODE=d KMAX=30 BMAX=30000 total=12861459 fail=0
```

[C] Still plausible, but now secondary to the bounded polynomial-prefix target.

### 7.5 Large-prime valuation mismatch route

[C] Candidate theorem:

```lean
theorem large_prime_factorization_escape_in_ratio_window
    {k n d : ℕ}
    (hk : 5 ≤ k)
    (hd : k ≤ d)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1) ^ k ≤ (n + d + 1)^k) :
    ∃ p, p.Prime ∧ k < p ∧
      (blockProduct k (n + d)).factorization p ≠
        (blockProduct k n).factorization p
```

[R] A true equality preserves all odd prime valuations because the multiplier is `4`.

[E] No exact counterexample was found in:

```text
5 ≤ k ≤ 70, 0 ≤ n ≤ 100000
8,909,785 ratio-window triples
```

and by gap:

```text
5 ≤ k ≤ 18, 5 ≤ d ≤ 100000
14,698,229 triples

5 ≤ k ≤ 28, 5 ≤ d ≤ 30000
11,153,084 triples
```

[C] Valid route, currently secondary.

### 7.6 Half-gap rough-prime route

[C] Since `twice_gap_lt_n_of_four_solution` is banked, one can target:

```lean
theorem large_prime_factorization_escape_halfgap
    {k n d : ℕ}
    (hk : 5 ≤ k)
    (hd : k ≤ d)
    (hhalf : 2 * d < n) :
    ∃ p, p.Prime ∧ k < p ∧
      (blockProduct k (n + d)).factorization p ≠
        (blockProduct k n).factorization p
```

[E] Modular rough-part equality search found no survivor:

```text
NO_HASH_SURV_FAST KMAX=120 NMAX=500000 elapsed=24.4466
```

[X] But a broader “upper prime above gap row” shortcut under half-gap alone is false.

Exact counterexample:

```text
k = 33
n = 671028
d = 201770
bound = d+k-1 = 201802
```

It satisfies `k ≤ d` and `2*d < n`, but all upper prime factors are `≤ 201802`. It does not satisfy the full ratio window, so it only refutes the half-gap shortcut, not the ratio-window theorem.

### 7.7 Row-prefix route

[X] The bounded row-only target is false.

False target:

```text
∃ j ≤ 8, ¬ n+j ∣ shiftedDiffProductAt k d j
```

Exact counterexample:

```text
(k,n,d) = (41,5245,181)
```

Details:

```text
k=41 n=5245 d=181
ratio_upper=True
ratio_lower=True
row_remainders_j_1_to_10=
1 0
2 0
3 0
4 0
5 0
6 0
7 0
8 0
9 0
10 2850
polynomial_remainders_a_0_to_9=
0 4135
1 0
2 0
3 0
4 0
5 0
6 0
7 0
8 0
9 0
block_equality=False
```

The `a=0` polynomial boundary congruence kills this triple. This is why the polynomial-prefix route is stronger than row-prefix.

### 7.8 Smoothness route

[X] Smoothness alone is false.

Exact counterexample:

```text
(k,n,d) = (5,182,59)
```

It satisfies the ratio window and all prime factors in the lower block, upper block, and reflection number are at most `d+k-1 = 63`, but the lcm obstruction still holds and the block equality is false.

---

## 8. `k = 5` branch progress

[R] The file has extensive `k = 5` infrastructure and finite gap certificates through large ranges:

```lean
no_solution_four_five_gap_lt_125
no_solution_four_five_gap_lt_200
no_solution_four_five_gap_lt_300
no_solution_four_five_gap_lt_400
no_solution_four_five_gap_lt_500
no_solution_four_five_gap_lt_600
no_solution_four_five_gap_lt_700
no_solution_four_five_gap_lt_7703
no_solution_four_five_gap_lt_9584
no_solution_four_five_gap_lt_11555
no_solution_four_five_gap_lt_13480
no_solution_four_five_gap_lt_15406
no_solution_four_five_gap_lt_17332
no_solution_four_five_gap_lt_19257
```

[R] A new exact reduced finite certificate over `2500≤s<2750`, `0≤t<398`
has been kernel-checked, extending the verified `k=5`, `N=4` exclusion to
gap `<28886`.  The `d<7703`, `d<9584`, `d<11555`, `d<13480`, `d<15406`,
`d<17332`, `d<19257`, `d<21183`, `d<23109`, `d<25034`, `d<26960`, and
`d<28886` slices have also been exposed in the direct row-escape shape needed
by the small-`k` row-prefix strategy:

```lean
theorem k_five_gap_lt_7703_divisor_skeleton_escape
theorem k_five_gap_lt_9584_divisor_skeleton_escape
theorem k_five_gap_lt_11555_divisor_skeleton_escape
theorem k_five_gap_lt_13480_divisor_skeleton_escape
theorem k_five_gap_lt_15406_divisor_skeleton_escape
theorem k_five_gap_lt_17332_divisor_skeleton_escape
theorem k_five_gap_lt_19257_divisor_skeleton_escape
theorem k_five_gap_lt_21183_divisor_skeleton_escape
theorem k_five_gap_lt_23109_divisor_skeleton_escape
theorem k_five_gap_lt_25034_divisor_skeleton_escape
theorem k_five_gap_lt_26960_divisor_skeleton_escape
theorem k_five_gap_lt_28886_divisor_skeleton_escape
```

These prove that for `k=5`, `5 ≤ d < 28886`, and the exact `N=4` ratio window,
some localized divisor-skeleton row `j ∈ {1,...,5}` fails.  This is stronger
than the corresponding quotient-exclusion wrapper for these slices, but it is
still only a bounded-gap slice; it does not close the full `k=5` branch.

[R] The file also has the useful final bridge:

```lean
theorem no_solution_four_five_of_first_two_rows_force_gap_lt_125
```

It says that if the first two rows force `d < 125`, the `k = 5` branch closes.

[E] Exact search by gap up to `d ≤ 1,000,000` found no first-two-row survivors with `d ≥ 125`:

```text
NO_FIRST2_SURV_GE125 DMAX=1000000 total=3999984 surv=16 maxd=117 examples=(13,5)(14,5)(14,6)(19,7)(25,9)(34,12)(38,13)(54,18)(55,18)(55,19)(62,21)(64,22)(139,45)(139,46)(278,90)(362,117)
```

All survivors are below `d = 125`, hence already in the closed finite slice.

### 8.1 Exact `s,t` reduction

[R] The file contains exact first-two-row reductions in `s,t` variables:

```lean
def kFiveExactRowOneST
def kFiveExactRowTwoST

theorem k_five_exact_reduced_t_product_divisibility
theorem k_five_exact_reduced_combined_t_product_window
theorem k_five_first_two_rows_linear_reduction
```

[E] Exact reduced search found no survivor for:

```text
s ≤ 2,000,000
2,063,568,199 exact candidate pairs checked
```

Output:

```text
SMAX=2000000 checked=2063568199 surv=0 examples=
```

### 8.2 One-variable `u = 9t - s` compression

[R] A useful necessary condition was found.

Let:

```text
A = 24s + t = n + 1
d = (23s + t) / 3
u = 9t - s
```

Then:

```text
651d = 208A + u
```

The exact row divisibilities imply:

```text
A     ∣ U0(u)
A + 1 ∣ U1(u)
```

where:

```text
U0(u) = u(u+651)(u+1302)(u+1953)(u+2604)
U1(u) = (u-859)(u-208)(u+443)(u+1094)(u+1745)
```

[C] Lean-facing theorem shape:

```lean
def kFiveU0 (u : ℤ) : ℤ :=
  ∏ r ∈ Finset.range 5, (u + 651 * (r : ℤ))

def kFiveU1 (u : ℤ) : ℤ :=
  ∏ r ∈ Finset.range 5, (u - 859 + 651 * (r : ℤ))

theorem k_five_exact_rows_imply_u_divisibilities
    {s t : ℕ}
    (hs13 : 13 ≤ s)
    (hdiv3 : 3 ∣ 23 * s + t)
    (hrow1 : 24 * s + t ∣ kFiveExactRowOneST s t)
    (hrow2 : 24 * s + t + 1 ∣ kFiveExactRowTwoST s t) :
    let A : ℤ := 24 * (s : ℤ) + (t : ℤ)
    let u : ℤ := 9 * (t : ℤ) - (s : ℤ)
    A ∣ kFiveU0 u ∧ (A + 1) ∣ kFiveU1 u
```

[X] The `U0/U1` divisibilities are necessary but not sufficient. Example:

```text
u = -19400
A = 100153664
s = 4153928
t = 459392
```

This satisfies the `U` divisibilities but fails the exact second row.

---

## 9. N = 64 side branch

[R] The file contains a substantial negative route for `N = 64`, including closed cases for several `k` values:

```lean
no_solution_sixtyfour_three
no_solution_sixtyfour_six
no_solution_sixtyfour_eight
no_solution_sixtyfour_sixteen
no_solution_sixtyfour_two_three_four_or_six
no_solution_sixtyfour_two_three_four_six_or_eight
no_solution_sixtyfour_two_three_four_six_eight_or_sixteen
```

[R] It also contains many conditional final bridges around odd-block separation, odd-part row escape, smoothness, and large-prime-power row escape:

```lean
erdos686_false_of_sixtyfour_oddBlock_separation
erdos686_false_of_sixtyfour_oddBlock_ratio_window_escape
erdos686_false_of_sixtyfour_oddPart_row_escape
erdos686_false_of_sixtyfour_oddPart_row_ratio_window_escape
erdos686_false_of_sixtyfour_not_smooth_escape
erdos686_false_of_sixtyfour_not_smooth_ratio_window_escape
erdos686_false_of_sixtyfour_large_prime_factor_escape
erdos686_false_of_sixtyfour_large_prime_factor_ratio_window_escape
erdos686_false_of_sixtyfour_upper_large_prime_power_rows_ratio_window_escape
erdos686_false_of_sixtyfour_upper_large_prime_power_row_ratio_window_escape
```

[C] This remains a viable independent negative route, but the current intended counterexample is `N = 4`, which is cleaner because the low branches are already closed and the polynomial-congruence route is sharper.

---

## 10. Generated patch files and their status

The following patch or target files were generated during the research passes:

```text
unique_residual_patch.lean
Erdos686_pass3_prime_support_bridge.lean
Erdos686_pass3_absent_exception_bridge.lean
Erdos686_pass3_truncated_residual_target.lean
Erdos686_pass4_large_factorization_bridge.lean
Erdos686_pass5_halfgap_rough_bridge.lean
Erdos686_pass6_upper_prime_absent_bridge.lean
Erdos686_pass7_polynomial_prefix_bridge.lean
Erdos686_pass8_polynomial_prefix_eight_bridge.lean
```

[C] These were not kernel-checked in the local container because `lean` and `lake` were unavailable. Most are bridge wrappers around already banked file theorems and should be easy to reconcile manually in the Lean project.

Current highest-priority patch:

```text
Erdos686_pass8_polynomial_prefix_eight_bridge.lean
```

---

## 11. Exact computation files

Important scripts and outputs generated so far:

```text
verify_window_lcm.py
find_first_large_prime_escape_failure.py
pass2_lcm_obstruction_exact.cpp
pass2_lcm_obstruction_K70_N100k_complete.out
certify_absent_or_residual_sum.cpp
certify_absent_or_residual_sum_K70_N100k.out
pass3_lcm_by_d_exact.cpp
pass3_lcm_by_d_K18_D100k.out
pass3_lcm_by_d_K28_D30000.out
pass3_prime_support_combo.cpp
pass3_prime_support_combo_K70_N100k.out
pass3_prime_support_combo_by_d.cpp
pass3_prime_support_combo_by_d_K28_D30000.out
pass3_row_skeleton_by_d.cpp
pass3_row_skeleton_K30_D30000.out
pass3_smooth_combo_search.cpp
pass3_smooth_combo_K70_N100k.out
pass3_smooth_counterexample_details.out
pass4_large_factorization_escape_range.cpp
pass4_large_factorization_escape_K70_N100k_summary.out
pass4_large_factorization_by_d_exact.cpp
pass4_large_factorization_by_d_K18_D100000.out
pass4_large_factorization_by_d_K28_D30000.out
pass4_k5_first2_by_d.cpp
pass4_k5_first2_by_d_D1M.out
pass5_rough_equal_halfgap_hash_fast.cpp
pass5_rough_equal_halfgap_hash_fast_K120_N500k.out
pass5_k5_st_exact_search.cpp
pass5_k5_st_exact_search_S2M.out
pass6_upper_prime_absent_lower_ratio.cpp
pass6_upper_prime_absent_lower_ratio_n_K70_N100k.out
pass6_upper_prime_absent_lower_ratio_d_K30_D30000.out
pass6_upper_prime_power_gap_absent_ratio.cpp
pass6_upper_prime_power_gap_absent_ratio_K70_N100k.out
pass6_exact_rough_equal_search.cpp
pass6_exact_rough_equal_K40_N200k.out
pass6_halfgap_large_prime_shortcut_refutation.py
pass6_halfgap_large_prime_shortcut_refutation.out
pass7_polynomial_prefix_by_n.cpp
pass7_poly_prefix_K70_N100k.out
pass7_polynomial_prefix_by_d.cpp
pass7_poly_prefix_by_d_K30_D30000.out
pass7_row_prefix_counterexample_details.py
pass7_row_prefix_counterexample_details.out
pass8_poly_prefix_fast_by_n.cpp
pass8_poly_prefix_by_n_K80_N100k_pref8.out
pass8_find_first8_examples.cpp
pass8_find_first8_examples.out
pass8_prefix7_counterexample_details.py
pass8_prefix7_counterexample_details.out
```

---

## 12. Recommended next proof pass

Do not continue with the old prefix-seven large-prime theorem or the prefix-eight escape theorem as stated. Both are refuted by exact integer counterexamples.

### 12.1 Refuted targets

[X] The proposed support theorem

```lean
theorem prefix_seven_forces_large_prime_in_n_add_eight
```

is false. Exact counterexample:

```text
(k,n,d) = (113,30171,373)
n+8 = 30179 = 103 * 293
d+k-8 = 478
```

This triple satisfies the ratio window, passes congruences `a = 0,...,7`, and has no prime factor of `n+8` above the `a=8` row cap.

[X] The proposed prefix-eight escape

```lean
theorem polynomial_prefix_eight_escape_in_ratio_window
```

is false. Exact counterexample:

```text
(k,n,d) = (167,34235,286)
```

It satisfies the ratio window and passes `a = 0,...,8`; first failure is `a = 9`.

Further exact survivors:

```text
(184,46759,354) passes a = 0,...,9; first failure a = 10
(245,48503,276) passes a = 0,...,14; first failure a = 15
```

### 12.2 Current row-prefix candidate

[C] The previous repaired polynomial-prefix target was:

```lean
theorem polynomial_prefix_fifteen_escape_in_ratio_window
    {k n d : ℕ}
    (hk : 5 ≤ k)
    (hd : k ≤ d)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1)^k ≤ (n + d + 1)^k) :
    ∃ a, a ∈ Finset.Icc 0 15 ∧
      ¬ ((n + a : ℕ) : ℤ) ∣ fourCongruencePolynomial k d a
```

This is not proved, but it is no longer the primary target.  GPT Pro's newer
exact search found no polynomial-prefix survivors for `C = 15, 20, 30, 50`,
and found a sharper row-only target:

```lean
theorem row_prefix_sixteen_escape_in_ratio_window
    {k n d : ℕ}
    (hk : 5 ≤ k)
    (hd : k ≤ d)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1)^k ≤ (n + d + 1)^k) :
    ∃ j, j ∈ Finset.Icc 1 k ∧ j ≤ 16 ∧
      ¬ n + j ∣ shiftedDiffProductAt k d j
```

This row-prefix theorem is also not proved.

[R] The Lean file now has the generic bridge:

```lean
theorem no_solution_four_of_polynomial_prefix_escape
theorem erdos686_false_of_polynomial_prefix_escape
```

and the `B = 15` specializations:

```lean
theorem no_solution_four_of_polynomial_prefix_fifteen_escape
theorem erdos686_false_of_polynomial_prefix_fifteen_escape
```

The Lean file also now has the row-prefix-sixteen bridges:

```lean
theorem no_solution_four_of_row_prefix_sixteen_escape
theorem erdos686_false_of_row_prefix_sixteen_escape
theorem polynomial_prefix_sixteen_escape_of_row_prefix_sixteen_escape
theorem polynomial_prefix_sixteen_escape_in_ratio_window_of_row_prefix_sixteen_escape
```

So the next proof pass should focus on the row-prefix-sixteen escape theorem
itself; the bridge from that theorem to the full negative `N=4` result is
already banked.

### 12.3 Exact verifier

[R] The repo-local exact verifier is:

```text
compute/erdos686_prefix_counterexamples.py
```

It checks the ratio window, the first failed congruence, and the relevant `n+8` factorization for all four recorded triples.

### 12.4 GPT Pro task

[C] Ask GPT Pro to attack the row-prefix-sixteen target rather than polishing
the refuted prefix-eight route:

```text
Prove or refute row_prefix_sixteen_escape_in_ratio_window:
for every N=4 ratio-window triple (k,n,d), 5≤k≤d, find j≤16 with
¬ (n+j ∣ shiftedDiffProductAt k d j).  Prefer a valuation/absent-prime proof.
If false, give an exact counterexample passing rows j=1,...,16.
```

### 12.5 New bounded k=5 certificate slice

[R] The exact reduced finite search over
`2750 <= s < 3000`, `0 <= t < 426` checked `8415` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_2750_3000_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_23109
theorem k_five_gap_lt_23109_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 23109`; the second
is the direct row-escape form for `d < 23109` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Fresh verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (1065s)
direct #check of the three new names        PASS
bash scripts/check_manifest.sh             PASS (276 theorem(s))
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
git diff --check                           PASS
lake env lean Audit.lean                   PASS
bash scripts/check_axioms.sh               PASS (276 theorem(s))
lake build                                 PASS
```

The audited axiom footprint remains exactly `[propext, Classical.choice,
Quot.sound]`; no `native_decide` or `approx_bound_for_cuberoot4` appears.

### 12.6 Next bounded k=5 certificate slice

[R] The exact reduced finite search over
`3000 <= s < 3250`, `0 <= t < 454` checked `8478` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_3000_3250_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_25034
theorem k_five_gap_lt_25034_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 25034`; the second
is the direct row-escape form for `d < 25034` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Focused verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (1146s)
direct #check of the three new names        PASS
bash scripts/check_manifest.sh             PASS (278 theorem(s))
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
git diff --check                           PASS
lake env lean Audit.lean                   PASS
bash scripts/check_axioms.sh               PASS (278 theorem(s))
lake build                                 PASS
```

### 12.7 Next bounded k=5 certificate slice

[R] The exact reduced finite search over
`3250 <= s < 3500`, `0 <= t < 482` checked `8540` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_3250_3500_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_26960
theorem k_five_gap_lt_26960_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 26960`; the second
is the direct row-escape form for `d < 26960` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Focused verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (1259s)
direct #check of the three new names        PASS
bash scripts/check_manifest.sh             PASS (280 theorem(s))
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
git diff --check                           PASS
lake env lean Audit.lean                   PASS
bash scripts/check_axioms.sh               PASS (280 theorem(s))
lake build                                 PASS
```

### 12.8 Next bounded k=5 certificate slice

[R] The exact reduced finite search over
`3500 <= s < 3750`, `0 <= t < 510` checked `8602` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_3500_3750_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_28886
theorem k_five_gap_lt_28886_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 28886`; the second
is the direct row-escape form for `d < 28886` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Focused verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (1398s)
direct #check of the three new names        PASS
bash scripts/check_manifest.sh             PASS (282 theorem(s))
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
git diff --check                           PASS
lake env lean Audit.lean                   PASS
bash scripts/check_axioms.sh               PASS (282 theorem(s))
lake build                                 PASS
```

### 12.9 Next bounded k=5 certificate slice

[R] The exact reduced finite search over
`3750 <= s < 4000`, `0 <= t < 537` checked `8665` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_3750_4000_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_30811
theorem k_five_gap_lt_30811_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 30811`; the second
is the direct row-escape form for `d < 30811` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Focused verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (1598s)
direct #check of the four new names         PASS
bash scripts/check_manifest.sh             PASS (284 theorem(s))
git diff --check                           PASS
lake env lean Audit.lean                   PASS
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
bash scripts/check_axioms.sh               PASS (284 theorem(s))
lake build                                 PASS
```

### 12.10 Next bounded k=5 certificate slice

[R] The exact reduced finite search over
`4000 <= s < 4250`, `0 <= t < 565` checked `8729` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_4000_4250_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_32737
theorem k_five_gap_lt_32737_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 32737`; the second
is the direct row-escape form for `d < 32737` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Focused verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (1906s)
direct #check of the four new names         PASS
bash scripts/check_manifest.sh             PASS (286 theorem(s))
git diff --check                           PASS
lake env lean Audit.lean                   PASS
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
bash scripts/check_axioms.sh               PASS (286 theorem(s))
lake build                                 PASS
```

### 12.11 Next bounded k=5 certificate slice

[R] The exact reduced finite search over
`4250 <= s < 4500`, `0 <= t < 593` checked `8790` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_4250_4500_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_34663
theorem k_five_gap_lt_34663_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 34663`; the second
is the direct row-escape form for `d < 34663` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Focused verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (2236s)
direct #check of the four new names         PASS
bash scripts/check_manifest.sh             PASS (288 theorem(s))
git diff --check                           PASS
lake env lean Audit.lean                   PASS
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
bash scripts/check_axioms.sh               PASS (288 theorem(s))
lake build                                 PASS
```

### 12.12 Next bounded k=5 certificate slice

[R] The exact reduced finite search over
`4500 <= s < 4750`, `0 <= t < 621` checked `8852` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_4500_4750_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_36588
theorem k_five_gap_lt_36588_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 36588`; the second
is the direct row-escape form for `d < 36588` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Focused verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (2482s)
direct #check of the four new names         PASS
bash scripts/check_manifest.sh             PASS (290 theorem(s))
git diff --check                           PASS
lake env lean Audit.lean                   PASS
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
bash scripts/check_axioms.sh               PASS (290 theorem(s))
lake build                                 PASS
```

### 12.13 Next bounded k=5 certificate slice

[R] The exact reduced finite search over
`4750 <= s < 5000`, `0 <= t < 648` checked `8916` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_4750_5000_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_38514
theorem k_five_gap_lt_38514_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 38514`; the second
is the direct row-escape form for `d < 38514` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Focused verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (2789s)
direct #check of the four new names         PASS
bash scripts/check_manifest.sh             PASS (292 theorem(s))
git diff --check                           PASS
lake env lean Audit.lean                   PASS
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
bash scripts/check_axioms.sh               PASS (292 theorem(s))
lake build                                 PASS
```

### 12.14 Next bounded k=5 certificate slice

[R] The exact reduced finite search over
`5000 <= s < 5250`, `0 <= t < 676` checked `8979` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_5000_5250_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_40440
theorem k_five_gap_lt_40440_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 40440`; the second
is the direct row-escape form for `d < 40440` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Focused verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (3047s)
direct #check of the four new names         PASS
bash scripts/check_manifest.sh             PASS (294 theorem(s))
git diff --check                           PASS
lake env lean Audit.lean                   PASS
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
bash scripts/check_axioms.sh               PASS (294 theorem(s))
lake build                                 PASS
```

### 12.15 Next bounded k=5 certificate slice

[R] The exact reduced finite search over
`5250 <= s < 5500`, `0 <= t < 704` checked `9040` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_5250_5500_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_42365
theorem k_five_gap_lt_42365_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 42365`; the second
is the direct row-escape form for `d < 42365` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Focused verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (3497s)
direct #check of the four new names         PASS
bash scripts/check_manifest.sh             PASS (296 theorem(s))
git diff --check                           PASS
lake env lean Audit.lean                   PASS
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
bash scripts/check_axioms.sh               PASS (296 theorem(s))
lake build                                 PASS
```

### 12.16 Next bounded k=5 certificate slice

[R] The exact reduced finite search over
`5500 <= s < 5750`, `0 <= t < 732` checked `9103` surviving linear-window
and divisibility-filter candidates and found `0` hits.  This has been banked
as a Lean kernel-checked finite certificate:

```lean
theorem k_five_exact_reduced_s_5500_5750_contradiction
```

[R] The certificate extends the bounded `N = 4`, `k = 5` branch:

```lean
theorem no_solution_four_five_gap_lt_44291
theorem k_five_gap_lt_44291_divisor_skeleton_escape
```

The first theorem excludes quotient solutions with `m - n < 44291`; the second
is the direct row-escape form for `d < 44291` inside the exact `N = 4` ratio
window.  This is still a bounded slice and does not close the full `k = 5`
branch.

[R] Focused verification for this slice:

```text
lake build ErdosProblems.Erdos686          PASS (7348s)
direct #check of the four new names         PASS
bash scripts/check_manifest.sh             PASS (298 theorem(s))
git diff --check                           PASS
lake env lean Audit.lean                   PASS
rg native_decide/approx_bound/sorry/admit  PASS (no hits)
python3 -m py_compile selected compute/*.py PASS
bash scripts/check_axioms.sh               PASS (298 theorem(s))
lake build                                 PASS
```

---

## 13. Current bottom line

[R] The Lean file has reduced the negative route to excluding `N = 4`, `k ≥ 5`.

[R] The low `N = 4` cases are closed.

[R] A true remaining solution must satisfy the ratio window and the full polynomial congruence family.

[X] The prefix `a ≤ 7` obstruction is false.

[X] The prefix `a ≤ 8` obstruction is false.

[X] Prefixes through `a ≤ 14` are not enough, by the exact `(245,48503,276)` survivor.

[C] The current primary target is row-prefix `j ≤ 16`, not yet proved.

[C] The full Erdős 686 problem is still not solved.
