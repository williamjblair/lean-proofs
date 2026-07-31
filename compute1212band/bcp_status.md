# Erdős #1212 — terminal session status (2026-07-30, night)

## Newly PROVED by GPT Pro round 2 (refereed, spot-checked):
1. **Theorem 3′** (prime-cluster rarity via Selberg majorant + Goldston–
   Yıldırım correlations + Gallagher average) — with a genuine catch of my
   prompt's error: the X/L prefactor holds for DISJOINT window families;
   sliding starts cost a factor L. Localization check (moduli ≤ D^m = Y^{1/5})
   is sound and position-uniform.
2. **Corollary 5** — rarity of z/2-windows with < 2 z-rough composites
   (the compositeness patch), disjoint + sliding forms.
3. **Proposition 6 — deterministic chamber spacing** (the big one): EVERY
   interval of length Φ_k(z) = exp(A_k log²(3z)) contains a z-chamber,
   by re-running the localized bound inside any putative gap (its own
   localization condition log Y ≥ C_k log²z is exactly met — verified).
   This converts count-rarity into a worst-case gap bound, killing the
   clustering objection. With z(s) = exp(c√log s): Φ ≤ s^{1/3−δ}.
4. **Lemma 7 (collared bridge)** — a climb-free splice across any bad run
   via the Chamber Lemma alone, given Q-rough composite portal pairs in
   both collars, Q > run + 2ℓ + 2. Verified.
5. **Proposition 8** — BCP(s) ⟹ SCH′ ⟹ (Theorem D) #1212 = YES.
   Scale arithmetic z_{j+1} ≈ exp(A_k log²z_j), J = O(loglog s). Verified.

## The single remaining gap: BCP item 2 (boundary-conditioned portals)
Portal pairs must occur in the collars ADJACENT to bad runs — an adaptively
selected family; the unconditional counts control fixed families only.

## My addition: WHY it is hard (the diameter/supply circularity)
The Chamber Lemma needs anchors of roughness Q within diameter < Q. The only
worst-case supply theorem (fundamental lemma) guarantees rough integers in
windows of length ≥ Q^{9}-ish. Need window ≤ Q but guarantee needs ≥ Q^9:
self-referential at every level; Prop 6's exp(A log²z) sits strictly between
z and the fundamental-lemma scale, and cannot be pushed below z (log²z > log z).
Breaking it needs one of GPT Pro's four routes: joint mixed moments for
boundaries×portals; a conditional sieve after exposing primes ≤ z_j; a
deterministic local semiprime-supply theorem; or component-expansion giving
enough independent collars to beat a positive exceptional fraction — the
last looks most tractable (the seed's 2M+ vertices and the giant component's
32.7% share are exactly expansion-type facts, but no incidence theorem is
proved).

## Bottom line
Erdős #1212 = YES is now proved MODULO one precisely boxed statement
(BCP item 2 / the conditional-sieve form (40)), with every other link
refereed. This is the sharpest state the problem has ever been in.
