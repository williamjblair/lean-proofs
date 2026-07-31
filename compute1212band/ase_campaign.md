# ASE campaign — the phase-correlation attack (opened 2026-07-31)

Target: **Arithmetic Staircase Exclusion** (statement in `erdos1212_proof.md`
§19 and `writeup_1212_DRAFT.md` §2). ASE ⟹ #1212 is YES via the certified chain.

## Hard constraints from the 10-round record (do not re-derive)

1. **No counting/marginal arguments.** Window log-mass, per-row event caps, and
   per-column blocked fractions are all *satisfied* by a hypothetical staircase.
   Any argument whose only inputs are cardinalities is dead on arrival.
2. **The graph is static.** A separator pays once per row and once per interface;
   there is no "re-suppression" cost. Any argument charging the adversary
   repeatedly over horizontal position is wrong (this killed round 10).
3. **Position must be treated as space, not time.** The reachable-set language is
   convenient but the object is a min-cut in a fixed graph.

## The live idea: phase incompatibility

A staircase needs, at each interface `i`, that the slab `[c_i, c_{i+1}]` contains
no dockable climb across the gap between packets `P_i` and `P_{i+1}`. Two CRT
structures must therefore align:

* **Block times** of reservoir rows: `a ≡ 0, -1, -2 (mod ℓ)` for `ℓ | r`, with
  `ℓ ≥ Z = Y^{5/2-η}`. Each row contributes ≤ 6 residues mod its own two primes,
  and the primes are *distinct across rows* (factor-disjointness, §1.7).
* **Climb columns** for a gap `I`: integers `a` that are `R`-rough and coprime to
  `∏_{m ∈ I} m`. This is a sieve set defined by the primes dividing the *rows*
  in the gap, i.e. by a different, disjoint set of primes.

The disjointness in §1.7 is the asset nobody has used: the primes defining where
a packet is *cut* are disjoint from the primes defining where the neighbouring
gap is *climbable*. Two candidate formalizations:

**(A) Exponential sums / equidistribution.** Show the climb-column set is
equidistributed in residue classes modulo the reservoir primes `ℓ ≥ Z`, with
error beating the number of interfaces. Since climb columns are a sieve set with
level `R = Y^{o(1)}` and the moduli are `≥ Y^{5/2-η}`, this is a
large-modulus/short-set equidistribution question — likely needs a bilinear or
Bombieri–Vinogradov-type input, but the modulus is *fixed per interface* and only
`K ≈ Y^{1/2-η}` interfaces exist, so even a weak individual bound may suffice
after a union.

**(B) Second-moment / energy.** Count pairs (interface, alignment) with a second
moment over the packet structure; the disjoint supports make the relevant
correlation sums factor, which is exactly what defeated the first-moment
arguments. Target: show the number of interfaces admitting a climb-free slab is
`< K`, so some interface is crossable — that alone breaks every staircase.

**(C) Constructive dodge (weakest sufficient form).** Do not exclude all
staircases; show the *specific* reachable component can choose packets whose
interfaces are provably crossable — e.g. by selecting the reservoir subfamily
adaptively at the left shaft (free choice of starting height) so that the chosen
interfaces have climb columns at prescribed positions. This trades a global
theorem for a selection argument, and selection is where the campaign has
repeatedly found room.

## First concrete tasks

1. Numerics: build a surrogate reservoir at small `Y`, compute the joint
   distribution of (block residues, climb-column positions) per interface, and
   measure whether climb-free slabs at interfaces are as rare as (B) needs.
   Falsification target: if climb-free interfaces are *common* in the surrogate,
   ASE may be false and the whole tier architecture needs rethinking.
2. Literature probe: equidistribution of sieve sets in progressions to large
   moduli (Bombieri–Vinogradov for sifted sequences, Iwaniec's linear sieve in
   APs, Green–Tao-type transference for the specific level `R = Y^{o(1)}`).
3. If (A) or (B) yields a bound, restate ASE with explicit constants and referee.

## Status

Opened. No results yet. Prior probability of success unclear — this is the first
attack aimed at the actual difficulty rather than around it.
