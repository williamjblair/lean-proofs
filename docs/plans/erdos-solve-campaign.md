# Erdős full-solve campaign (2026-07-30 → )

Goal (set by Will after the #64 pivot): identify open Erdős problems that are
genuinely fully solvable, and drive at least one to a complete, defensible
resolution of the upstream erdosproblems.com statement — kernel-clean Lean
proof per repo gates where feasible.

## Selection intelligence

- Database: `teorth/erdosproblems` `data/problems.yaml` (regenerated
  2026-07-29): 1,217 problems, 607 open. 410 status changes since 2025-09
  (the AI-assisted wave) — famous/low-numbered problems are picked over;
  freshness checks are mandatory before committing to any target (problem
  page + forum + arXiv, day-of).
- Finding: the "decidable / verifiable / falsifiable" statuses almost always
  hide infeasible finite gaps (surveyed #19, 475, 506, 547, 551, 556, 580,
  647, 672, 742, 848: regularity-lemma n₀'s, real quantifier elimination
  over ℝ^{2n}, Diophantine machinery). Not the hunting ground.
- Hunting ground: high-numbered (≥ 850) unprized open problems, plus
  quiet 600–849 entries; shapes that win: elementary-provable estimates,
  finite/structured computations, ask-about-a-specific-sequence questions,
  and literature-completable statements.

## Acceptance bar

1. The upstream statement (as on erdosproblems.com), resolved in full —
   partials are recorded honestly but don't close the campaign.
2. Adversarial verification by independent skeptic agents before claiming.
3. Lean formalization meeting repo gates (axioms ⊆ kernel set, no
   native_decide), registered in Audit.lean + proofs.yaml, when the
   mathematics is formalizable at session scale; otherwise a rigorous
   writeup + machine-checkable certificates.
4. Freshness check: nobody else solved it first (page/forum/arXiv day-of).

## Target dossier: #848 (Erdős–Sárközy, ab+1 never squarefree)

Statement: is the max size of A ⊆ [N] with ab+1 never squarefree (all
a,b ∈ A, a=b allowed) achieved by {n ≡ 7 mod 25}? DECIDABLE status.
Tao + Alexeev flag "tractable". 48 comments, 0 proof claims, quiet since
2026-04-05.

- Sawhney (Oct 2025, Problem_848.pdf, read in full): true for N ≥ N₀,
  ineffective; binding case margin = 0.04 − 0.0377 = 0.0023·N; equality
  iff A = A₇ or A₁₈.
- Explicit race (Sothanaphan + old-bielefelder GPT-5.x, Mar 2026):
  N₀: exp(682276) → … → 7×10^17 → 3.3×10^17 → ~2.94×10^17, declared
  near-optimal for the current proof shape. GPT-5.4 judged Montgomery–
  Vaughan inapplicable (square moduli); used Prachar 1958 + Hooley 1975.
  Sawhney had suggested MV Cor 1 route, "10^6 easily" — tension unresolved.
- My wall analysis: the cost is #{x ≤ N : ∃ prime p > √N, p²|x²+1}.
  Elementary split (per-class ≤ 1 for p ∈ (√N, N^{2/3}]; Pell-solution
  sparsity for p > N^{2/3}) gives ~N^{2/3}·polylog, vs margin 0.0023N ⟹
  N₀ ~ 10^12–10^17 depending on constants. Breaking the wall needs a new
  idea — candidate: pair-constraint recursion inside the bad set (a large
  bad set is itself a valid set with pairwise square-divisor structure —
  unexploited in the current chain).
- Finite side: honest exact verification only to ~10^4 (Alexeev/Cambie);
  MalekZ's 10^7 run flagged as likely incorrect. Per-N exact verification
  = max-clique-with-structure; witness classes A₇ ∪ A₁₈ ∪ outsiders.
- Resources: Sawhney PDF (cached in scratchpad), Sothanaphan notes (Drive
  links in thread), arXiv:2512.01087 (vDWC growth-rates paper),
  erdosbanger Lean formalization of the asymptotic (3,900 lines,
  0 sorries), sproutseeds/erdos-problems workspace (Apr 2026),
  MV = Mathematika 1973, Prachar BF01301288, Hooley BLMS 7.2.133.
- Verdict: PLAUSIBLE, high-risk, high-reward; crowded-but-stalled.
  Full solve = explicit N₀ within computational reach + verified
  exhaustive check below + certificates (+ Lean where feasible).
- Pell-floor analysis (mine, 2026-07-30): the irreducible error is the
  global negative-Pell count of x ≤ N with a prime-square divisor of
  x²+1 exceeding R ≈ N^{2/3}: density ≈ N^{-1/3}(1 + 2 ln N / ln(2+√3)).
  At N = 10^10 ≈ 0.017, at 10^11 ≈ 0.0087, at 10^12 ≈ 0.0043. Max
  conceivable slack if the witness-class cascade (sieve each A*_p, p ∈
  {13,17,29,37,41}, by an even witness with 2^ω-upgraded Cor-1 errors
  ≈ 2√(ρX) per application) lands near its floor: ≈ 0.04 − (2/25)C_{2,5}
  − Σ(2/p²)(0.39) ≈ 0.017-0.027. ⟹ N₀ ≈ 10^10 is knife-edge possible;
  10^11-10^12 more likely; certified rational arithmetic will decide.
  Finite-side ceiling ≈ 10^9-10^10 ⟹ full closure is genuinely open —
  the honest fallback is a large explicit-threshold improvement
  (2.64×10^17 → ~10^11±1) + verified finite range + documented gap.

## State (2026-07-30 evening)

- Triage: decidable/verifiable sweep DONE (#848 only plausible full-solve;
  #647 lottery; rest hopeless — regularity/QE/Diophantine walls). High-number
  mining agent nudged at 2h mark.
- **#848 campaign LAUNCHED** (compute848/): scope = canonical a=b-allowed
  version (formal-conjectures reading; the distinct-pairs variant is a
  separate unsolved question, best known only limsup ≤ 0.1725).
  - Track 1 (chain-optimizer agent): 23×-Pell-overcount fix + Pell-d
    thinning (no prime factor ≡ 3 mod 4) + ρ ≤ 4·2^ω root-count upgrade +
    R/D re-optimization, certified rational arithmetic → target N₀' ≤ 10^12.
  - Track 2 (case-deepener agent): mod-169/289 casework (169 = 13²,
    x ≡ ±70; 70²+1 = 29·169; same-class A*₁₃ pairs auto-satisfy mod 169) +
    sieving A*₁₃ by an even witness + A*-internal pair structure → enlarge
    the 0.0024 slack (cubes into N₀).
  - Track 3 (finite side, pending N₀'): layered engine — exact clique
    ground truth for small N (verified: f(N) = |A₇(N)| for ALL N ≤ 600;
    N ≤ 5000 running); per-outsider compat-certificate argument for the
    mid range; comfortable to ~10^9, stretch 10^10. The math tracks must
    land N₀' ≤ ~10^10 for the full solve to close.
- **Portfolio expanded after high-number triage** (179 open #850+ problems
  swept; extraction cached in session scratchpad):
  - **#1139** (co-primary, WP8): limsup gap/log k = ∞ for integers with
    ≤ 2 prime factors — split-Rankin attack (2-3 prime classes, per-class
    covering, CRT; cofactor > 1 forces ≥ 3 factors). Tractable-voted, no
    recorded progress, formalized. Solve agent running. Lowest-risk target.
  - **#1144** (WP9): a.s. limsup |Σf(m)|/√N = ∞ for random completely
    multiplicative ±1 — possibly closable by Aymone–Heap–Zhao assembly;
    literature-check agent running.
  - Bench: #1210 (pairwise-coprime harmonic sums, elementary two-direction),
    #963 (dissociated subsets, SAT-able disproof channel), #1212
    (coprime-grid infinite path construction).
- The #64 campaign continues in background (docs/plans/erdos64-campaign.md).


## Results ledger (2026-07-30)

**#848 — VERIFIED THRESHOLD IMPROVEMENT, full solve out of reach.**
Reproduction gate passed: Sothanaphan's constants recomputed in exact
rational arithmetic to the last quoted digit (E₂₅ = 4.6994382 < 4.700,
E₁₀₀ = 5.2750113 < 5.275; Corollary-2 per-class 8.57694e-5, total
1.9727e-3; slack 0.002388501). The 23× Pell-tail overcount I identified is
real — the per-class tail bound (N²+1)/R²·(1+log_{2+√3}N) is derived
globally and the 23 residue classes are disjoint, so it may be counted once
instead of 23 times. Result: **N₀ = 2.636×10¹⁷ → 9.107×10¹⁶** (factor
2.89), certified. Full closure is impossible by constant-tuning: at the new
N₀ the binding term is 23·R(1+log R)/N ≈ N^{−1/3}log N (75.6% of budget),
which alone forces N ≥ 3.69×10¹⁶, and the κ₂₅·N^{−1/4} term forces
N ≥ 9.8×10¹³ even with everything else zero. Reaching a
finite-verifiable 10^9–10^10 needs better EXPONENTS, not constants.
Artifact: `compute848/explicit_chain.py`.

**#1004 — PARTIAL(c<2).** Referee-standard proof that for every fixed
c < 2, almost all n ≤ x have φ(n+1..n+⌊(log x)^c⌋) pairwise distinct.
Barrier at c = 2 is real (GHP structured prime-pair families; Kim's
unconditional T(x,k) ≫ x/(log x)^50 for some even k), and the almost-all
statement is expected false beyond c = 2. `compute1004/proof_1004.md`.

**#1139 — GAP-REMAINS.** Reduction criterion (Theorem A) proved; the
split-Rankin route refuted by a Mertens dimension-1/2 obstruction
(≥0.1·Y/log Y immune survivors), which also invalidates the core lemma of
the public Chojecki note. Price/GPT-Pro claim: plausible-unverified.
`compute1139/proof_1139.md`.

**#1144 — genuinely open**, not closable by citation or routine transfer.

**#64 — frontier extended** (see erdos64-campaign.md): counterexample bound
17 → 19 vertices; vertex-transitive census cleared to order 1280 with
111,705 verified certificates; Markström's counts reproduced at n=24/26/28.
