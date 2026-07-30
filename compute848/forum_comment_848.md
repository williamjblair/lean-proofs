# Draft comment for erdosproblems.com/848 (for Will to post if desired)

Status: verified in this repo, not yet posted. Per `docs/plans/submission-protocol.md`,
posting is Will's call. AI assistance must be disclosed.

---

> **Explicit threshold: 2.64×10^17 → 9.11×10^16.**
>
> Nat Sothanaphan's note (Mar 24, 2026) proves the conjecture for
> N ≥ 2.64×10^17. One step in it can be tightened without changing anything
> else, and it gives a factor of 2.89.
>
> In Corollary 2, Proposition 2 is applied separately to each of the 23
> admissible residue classes modulo q ∈ {25, 50}, and the *whole* per-class
> error is multiplied by 23 — including the tail term
> T_R ≤ ((N²+1)/R²)(1 + log_{2+√3} N). But that term is not per-class: it is
> derived globally, by writing x²+1 = d·r² with r > R, so d ≤ (N²+1)/R², and
> bounding the number of solutions of the negative Pell equation
> x² − d r² = −1 with x ≤ N by 1 + log_{2+√3} N for each d. Nowhere does the
> argument use the congruence condition on x. Since the 23 classes are
> disjoint subsets of [1,N], the sum of their tail counts is at most the
> single global count, so this term may be counted once rather than 23 times.
>
> Redoing the numerics with that one change (exact rational arithmetic;
> R = ⌈(259/200)N^{2/3}⌉ computed by integer bisection on (200R)³ ≥ 259³N²):
> the slack is 1/25 − (23/25)C_quad − (2/25)C_{2,5} = 0.002388501…, and the
> minimal admissible threshold drops from N₀ = 2.636×10^17 (which confirms
> 2.64×10^17 is essentially tight for the published chain — about 0.05%
> headroom) to
>
>   **N₀ = 91 065 686 969 551 497 ≈ 9.107×10^16.**
>
> As a check on the recomputation, the same script reproduces the note's own
> constants: E₂₅ = 4.6994382 (paper: < 4.700), E₁₀₀ = 5.2750113 (< 5.275),
> Corollary-2 per-class error 8.57694×10^-5 (< 8.577×10^-5), total
> 1.9727×10^-3 (< 1.973×10^-3).
>
> For anyone continuing the descent, the budget at the new threshold is worth
> recording, because the binding constraint has changed. Of the 0.0023885
> slack: 23·R(1+log R)/N accounts for 75.6%, the 2κ₂₅N^{−1/4} term for 22.7%,
> and the Pell tail now for only 1.7%. So the threshold is governed by the
> first Corollary-2 term, which decays like N^{−1/3}log N and on its own
> forces N ≥ 3.69×10^16, and secondarily by the N^{−1/4} squarefree-error
> exponent, which forces N ≥ 9.8×10^13 even if every other error were zero
> (optimizing α₂₅ moves that floor only slightly). Further progress therefore
> needs better exponents — a different treatment of the large-divisor sum —
> rather than better constants. That also means the "finish it by computer"
> route is still far away: exhaustive verification is realistic to about
> 10^9–10^10, not 10^16.
>
> Two further levers, which I have computed but not yet written up as
> proofs (so treat the numbers as a route, not a theorem):
>
> 1. **R is tuned for the 23× tail.** Re-optimizing R = c·N^{2/3} under the
>    corrected tail gives c* ≈ 0.4606 rather than 1.2928 (my recomputation
>    reproduces c* = 1.2950 under the old weighting, which is a check on the
>    reconstruction). This alone takes N₀ to ≈ 1.7×10^16.
> 2. **Splitting A\* by its smallest witness prime.** For p ∈ {13,17,…},
>    A\*_p = {x ∈ A\* : p² | x²+1} occupies two classes mod p², and one of
>    them can be sieved by the even witness b (exactly one of the two can
>    fail the Lemma-2.2 hypothesis, since p² | bt+1 ⟺ b ≡ t (mod p²), and
>    then it genuinely cannot be sieved — so one class is charged trivially).
>    Note the natural greedy here is a trap: minimizing the main term picks
>    q₀ = 25p², which costs 22 extra Corollary-1 applications and makes N₀
>    *worse*. Optimizing N₀ directly stops at S = {13,17}.
>
> Together with the tail correction this reaches **N₀ ≈ 4.9×10^14**, about
> 540× below the published threshold. Three lemmas would need writing out
> first: extending Corollary 1 from q₀ ∈ {25,100} to q₀ = p², restricting
> Proposition 2 to the primes outside S (routine — the proof never uses that
> the family is all of p ≡ 1 mod 4, p ≥ 13), and the tail disjointness
> argument above.
>
> None of this brings a computer finish into range. Even with a hypothetical
> zero main term the chain floors near 10^12, and both dominant terms decay
> only like N^{−1/3}log N, so casework is a cube-root lever. Closing the gap
> to a verifiable 10^9–10^10 needs a better level of distribution — beating
> N^{2/3} in the large-divisor sum Σ_{r≤R}2^{ω(r)} ≤ R(1+log R) — not more
> constants.
>
> Code (exact `Fraction` arithmetic, reproduces the paper's constants before
> applying any change): [link]. AI assistance was used throughout; the
> numbers come from executed runs.
