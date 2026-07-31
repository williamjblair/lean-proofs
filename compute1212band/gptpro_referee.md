# Referee report: GPT Pro's localized desert-counting theorems (2026-07-30)

## Verdict

**Theorem 3 (fixed-moment localization): SURVIVES review — and it is
sufficient for the Erdős #1212 application.** Verified by hand: the
(2h)^{2k}-term moment expansion with per-term Lemma 5 transfer (error budget
2e^{-10}(2h)^{-2k} ≤ 1, checked); the Markov step |S-μ|^{2k} = μ^{2k} on
empty windows; the desert reduction (each maximal desert of length ≥ T yields
≥ T/2 disjoint empty h-windows, h = ⌊T/2⌋). External input: ONLY fixed-k
Montgomery–Vaughan 1986 (bedrock). Numerics: window correlations = Euler
products to ratio 1.000 (r = 2,3); M_2k/(μ+μ^k) ≈ 0.11–0.13 (bounded, as
(7) requires); Markov bounds valid.

**Lemma 4 (large-prime covering): CORRECT** — every step verified (automatic
disjointness of hitting sets since p > diameter; the (22)→(23) free-choice
bound; Bernoulli step (24); ε ≤ 4ℓ/w; the (1−Θ/2)^ℓ endgame).

**Lemma 5 / Corollary 6: architecture SOUND.** Bonferroni is applied to the
union of prime-hit events, whose mean λ ≤ Cr log₂z is SMALL — truncation at
L ≍ λ+R is above the mean, dodging the Bonferroni trap (skeleton §4.1)
correctly. Floor-error accounting (38) checks.

**Theorems 1–2: plausible, NOT verified** — they rest on Banks–Ford–Tao
citations (the W_y lower bound and their Corollary 6.2 checkpoint, including
a "conditional on any fixed small-prime configuration" uniformity claim)
that must be checked against the actual paper before use. Flagged, unneeded.

## Why Theorem 3 suffices for us

In the trajectory application z ≍ η·log X, so Theorem 1's localization
condition T·log z·log₂z ≲ log X caps T at z/polylog — short of the
Jacobsthal scale. But Theorem 3 needs only log X ≥ C_k(log z)² — trivially
true — and gives, for EVERY fixed k,
  N(X;z,T) ≤ D_k·(X/T)·(C log z/T)^k
in every dyadic window. Summing dyadically over T ≥ T₀ = z/log²z with k = 3:
total desert-blocked length ≪ X·polylog(z)/z² — a vanishing fraction of any
window. This is more rarity than the dodge argument needs, unconditionally.

## Status of the full chain for Erdős #1212

PROVED: hub reduction; Theorem D (seed + SCH ⟹ YES); rarity input
(Theorem 3, this report). Skeleton §2's moment-localization program and the
β-framework are SUPERSEDED by the per-period-M–V + transfer route.
REMAINING: exactly one piece — the dodge write-up (rarity ⟹ SCH): a
referee-standard construction showing the component's extent doubles using
chambers/elevators through desert-free territory, with the desert-avoidance
quantified by Theorem 3. All tools exist; this is now a construction
exercise with generous margins, and the LAST open piece of the problem.
