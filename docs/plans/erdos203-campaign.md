# Erdős #203 campaign — the 2D Sierpiński problem (triage verdict + charter)

Opened 2026-07-31, after the type-scored re-triage of the 1,217-problem
corpus (622 open) using the difficulty-type diagnostic learned from the
#1212 campaign.

## The problem

Is there an integer m with gcd(m, 6) = 1 such that 2^k · 3^ℓ · m + 1 is
composite (never prime) for all k, ℓ ≥ 0? [Erdős–Graham 1980; #203;
generalizes Sierpiński numbers to two prime-power dimensions.]

## Why this target (the diagnostic)

WIN-type features, all present:
- **Finite-witness full solve**: a covering system for the (k,ℓ)-lattice
  plus CRT yields m; verification is finite and Lean-certifiable (compare
  our solved #730 hosting). One find = complete YES resolution of an
  Erdős–Graham problem.
- **Bounded, structured search**: candidate primes are exactly the
  divisors of gcd(2^h − 1, 3^h − 1)-type objects; each prime p covers
  cosets of the lattice Λ_p = {(k,ℓ) : 2^k 3^ℓ ≡ 1 mod p} of index
  |H_p| = lcm(ord_p 2, ord_p 3). Exact-cover search over lattice cosets —
  our #730/#848/#64 muscle exactly.
- **No worst-case-alignment core**: the adversary here is exact-cover
  combinatorics, not Jacobsthal-type integers. This is the anti-#1212.
- **Uncrowded**: 2 casual workers, 0 claimed proofs. State of the art
  (AnimishSharma, June 2026): density necessary condition
  Σ_p 1/|H_p| ≥ 1 proved; coverings with lcm(|H_p|) < 5040 excluded using
  primes ≤ 5×10⁷; candidate families at moduli 5040/10080 reach only
  71–72% coverage. Their prime table is scan-limited; the algebraic
  sourcing (factor 2^h−1, 3^h−1 for smooth h, take common/compatible
  prime factors) is UNTRIED and reaches primes far beyond 5×10⁷.
- **Both directions live**: heuristics split (1D Sierpiński says
  coverings plausible; "CRT frankenstein" skeptics say no). If search
  stalls, the Bugeaud–Corvaja–Zannier bound gcd(2^n−1, 3^n−1) < exp(εn)
  powers a density-obstruction theorem ("no covering with lcm ≤ L
  exists" for explicit growing L) — publishable partial regardless.

## Campaign plan

W1. Reproduce the state of the art: verify |H_p| formula, the density
    condition, and the lcm < 5040 exclusion independently.
W2. Build the algebraic prime table: factor 2^h − 1 and 3^h − 1 for all
    smooth h ≤ 10^4 (Cunningham tables + ECM for stragglers); for each
    prime compute |H_p| and its lattice Λ_p. Target: all usable primes
    with |H_p| ≤ 10^6.
W3. Exact-cover search: staged by lcm L ∈ {5040, 10080, 55440, 720720,
    ...}; SAT/DLX over lattice-coset tiles; prune by the density
    condition per branch. Any exact cover ⟹ CRT ⟹ candidate m ⟹
    verify small (k,ℓ) primality exceptions ⟹ DONE (YES).
W4. In parallel: the obstruction ledger — for each L, either a cover or
    a certified "no cover at this L" (the search is complete per L);
    publishes as a growing exclusion theorem if W3 never lands.
W5. On a find: Lean certificate (finite cover check + CRT witness +
    the small-case primality table), referee round, write-up per
    submission protocol (Will's approval gate; AI disclosure).

## Runners-up (recorded for the next pivot)

- #307 (prime sets, (Σ1/p)(Σ1/q) = 1): NEW structural lemma from this
  triage — coprimality forces numerator(Σ_P 1/p) = ∏Q and
  numerator(Σ_Q 1/q) = ∏P exactly (a bidirectional rigidity nobody has
  posted). Will is registered on it. Constructive search hard
  (|P∪Q| ≥ 60); obstruction direction open.
- #1056: Will's live erdos-frontier execution campaign (interval products
  ≡ 1 mod p) — continue in its own infra.
- #647: crowded (frontier 6.16×10^17, Lean reductions published, gap
  evidence negative). #366: searched to 10^22, ABC against. Decidable
  tags (#19 EFL, #547, #551, #556, #580, #742 Murty–Simon): all hide
  regularity-sized n₀ — infeasible finite checks.
