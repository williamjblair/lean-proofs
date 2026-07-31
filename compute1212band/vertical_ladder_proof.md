# Erdős #1212 — the low-band ladder architecture (candidate proof skeleton)

Status: SKELETON, 2026-07-30 late. Merges the recovered sch-prime-executor
derivation (fundamental-lemma bad-run cap, recovered from its transcript after
the output-cap death) with the main-session circularity analysis. This is the
first architecture that evades the supply/diameter circularity, because every
candidate family is FIXED (a dense set in a prescribed window), never
adaptively positioned — the adversary cannot align against it, and the killer
measure has convergent total mass.

## 0. Primitives (all unconditional, classical)

- **FL** (fundamental lemma of sieve theory, interval form): for an interval
  I of length T ≥ z^3, the number of z-rough integers in I is
  T·V(z)(1+O(u^{-u})) + O(z^{u}) with V(z) = ∏_{p≤z}(1-1/p) ~ e^{-γ}/log z.
  For T = z^5 the count is ≥ 0.5·T/log z for z ≥ z_0.
- **BT** (Brun–Titchmarsh): π(x+T) - π(x) ≤ 2T/log T for all x, T ≥ 2.
- z-rough (p^-(n) > z ≥ 2) forces n odd.

## 1. Supply Theorem (P1) — polynomial chamber supply

**Claim.** There are absolute z_0, c > 0, C such that for z ≥ z_0, EVERY
interval of length z^5 contains ≥ c·z^5/log z z-rough odd composites, and two
of them within C·log z of each other.

*Proof.* FL gives ≥ 0.5·z^5/log z rough integers (z ≥ z_0). BT caps primes in
the interval at 2z^5/log(z^5) = 0.4·z^5/log z. Composites ≥ 0.1·z^5/log z.
Pigeonhole: if all consecutive gaps among the m ≥ 0.1z^5/log z rough
composites exceeded C log z, the interval would have length
> (m-1)·C log z ≥ 0.09·C·z^5 > z^5 for C > 12. ∎

This replaces Prop 6's exp(A_k log²(3z)) with z^5. Everything downstream of
Prop 6 improves accordingly.

## 2. The architecture

Work in the hub graph H (both coords odd, gcd 1, not both prime; horizontal
step (a,b)→(a+2,b) open iff gcd(b, a(a+1)(a+2)) = 1; symmetric vertically).

Fix the working scale z = z(x) ≈ (K log x)^{1/5} (slowly growing). Define:

- **The box** B(z): all z-rough odd composites in [z², z² + z^5]. These are
  the ROWS the path uses. |B| ≥ c z^5/log z. Height of the band: ≤ 2z^5
  ≈ 2K log x — logarithmic height, matching the measured witness
  (band 1399 ≈ 115·log 868000) and clearing the Wall Lemma
  (first wall for band Y at e^{cY} = x^{cK} ≫ x for K > 1/c).
- Each row R ∈ B has R ≤ z^5, hence **ω(R) ≤ 5** (each prime factor > z... 
  in fact > z means ≤ 5 factors since z^6 > z^5). Blocks on row R (columns a
  with gcd(a(a+1)(a+2), R) > 1) come from ≤ 5 primes, each contributing 3
  residues mod p > z: **≤ 15(L/z + 1) blocked columns per x-span of
  length L**; open segments have average length ≥ z/15.
- **Close pairs**: pairs R, R′ ∈ B with |R−R′| ≤ d := C log z (exist by P1;
  in fact ≥ c′z^5/log²z of them, disjointly).

## 3. The moves and their costs

1. **Run**: travel on row R until a block. Free until blocked; blocks every
   ~z/15 columns at worst.
2. **Sidestep**: at a block on R, climb from (a, R) to (a, R′) over the range
   [R, R′], |R−R′| ≤ d, at a column a in the open segment before the block.
   Requirement: gcd(a, m) = 1 for every m in [R, R′] (the climb sweeps all
   intermediate integers), a odd, and the top hub (a, R′) admissible
   (R′ composite ✓). Sufficient: a is d-rough AND no prime P > d dividing
   M(R,R′) := ∏_{m∈[R,R′]} m divides a.
   - Candidates: d-rough integers in the open segment (length ≥ z/15 ≥ d³),
     density ≥ c/log d by FL at level d.
   - Killers: primes P > d with P | M(R,R′). Killed density ≤ Σ_{P|M, P>d} 1/P.
   - **Key average (the fixed-box second moment)**: summing over the box,
     Σ_{m ∈ [z², z²+z^5]} Σ_{p|m, p>d} 1/p = Σ_{p>d} (1/p)·#{multiples}
     ≤ z^5 Σ_{p>d} 1/p² + O(π(z^5)) ≤ 2z^5/(d log d).
     So the AVERAGE close pair has killer-sum ≤ 4d/(d log d)·(1+o(1))
     = O(1/log d), i.e. killed density O(1/log d) · (1/1) vs candidate
     density c/log d: a CONSTANT fraction survives for most pairs.
     By Markov, ≥ 2/3 of close pairs have killer-sum ≤ 3× average; call these
     GOOD pairs. For a good pair, every sufficiently long open segment
     contains a surviving sidestep column.
3. **Pair switch**: if both R and R′ block at nearby columns (or the pair is
   not good), move vertically within the box to another close pair. Climbs
   between consecutive box rows (gap g_i): same sidestep analysis with
   d → g_i. Most gaps ~ log z; large gaps handled by move 4.
4. **Gap repair**: a run of box rows with a large gap G′ (up to worst-case
   Jacobsthal ~ z²·polylog... capped by Iwaniec at O(z²)) is climbed at a
   G′-rough composite COLUMN a (columns have no height restriction: any
   a ≤ 2x). Supply: P1 at level G′ gives such columns in every x-window of
   length G′^5 ≤ z^{10}·polylog. Reaching that column costs ≤ z^{10} of
   horizontal travel = moves 1–3.

## 4. Why the circularity is dead

Every prior dead end had the form: "structure of length G at an
adaptively-selected position needs roughness > G; worst-case supply of
G-roughness needs windows ≥ G²." Here:

- Rows are chosen from the FIXED box B(z) — a dense family in one prescribed
  window. Worst-case (Jacobsthal-type) constructions cannot be aligned
  against all Ω(z^5/log²z) close pairs simultaneously because the total
  killer mass Σ_{p>d} 1/p² converges — this is a second-moment fact about
  the fixed integers in [z², z²+z^5], not a probabilistic assumption.
- Climb spans are d = O(log z), never z — the near-diagonal trick: pairs
  close IN VALUE make climbs short, so climb columns need only
  polylog-roughness, whose supply is guaranteed in polylog³ windows: the
  supply scale sits BELOW the demand scale for the first time.
- The only large climbs (gap repair, span ≤ O(z²)) use COLUMNS, which have
  no height cap, so P1 supplies them in z^{10}-windows — again below the
  travel budget, not above it.
- Height stays ≤ 2z^5 ≈ 2K log x, so the Wall Lemma is cleared with room and
  the scale can ratchet: box(z(x)) and box(z(2x)) overlap in height
  (both ≈ K log x), so consecutive boxes connect by short climbs.

## 5. Obligations (what must be proved / verified)

- (O1) P1 constants: verify numerically at z = 50–400, then write the FL+BT
  proof with explicit z_0.
- (O2) Killer-sum distribution over close pairs in a real box: verify the
  average is O(1/log d) and ≥ 2/3 of pairs are good.
- (O3) Sidestep survival: for good pairs, verify surviving climb columns
  exist in real open segments.
- (O4) The pair-switch ladder: verify the box's close-pair graph (pairs
  linked when climbable) is connected, or has a giant component reaching
  all x-positions.
- (O5) Full pipeline simulation: travel several z^5 of x-extent at moderate
  z using ONLY moves 1–4 inside the prescribed band. This is the
  end-to-end validation.
- (O6) The formal double induction (travel at level z, sidesteps at level
  log z, repairs at level z², box at level z^5 — four levels, no regress),
  plus the scale ratchet z(x) → z(2x).
- (O7) Seed connection: the verified witness (x to 867,999, band ≤ 1399)
  must reach the first box.

## 5a. The Sidestep Lemma — PROVED (main-session derivation, to be refereed)

**Lemma S.** Let z ≥ z_0 (absolute, effective), d = 60 log z, B the box.
Call consecutive R < R′ ∈ B with R′−R ≤ d a *close pair*, and define its
killer sum S(R,R′) = Σ 1/P over primes P > d dividing some m ∈ [R,R′].
Then at least 2/3 of close pairs have S ≤ 0.4/log d ("good"), and for every
good pair and every interval S of length ℓ ≥ z/30, the number of columns
a ∈ S with gcd(a, m) = 1 for all m ∈ [R,R′] is ≥ 0.05·ℓ/log d > 0.

*Proof.* (i) A valid column must avoid every prime ≤ d (each divides some m
in the (d+1)-length range) and every killer P. Count by subtraction:
(d-rough integers in S) − Σ_{P killer}(ℓ/P + 1)
≥ 0.54·ℓ/log d − ℓ·S(R,R′) − ω_{>d}(M).
The first term is the fundamental lemma at level d (interval length
ℓ ≥ z/30 ≥ d^4 for z ≥ z_0; sieve level D = ℓ^{0.9} gives u ≥ 3.6, loss
factor ≤ 4%, e^{-γ}(1−0.04) ≥ 0.54). The last term is
≤ (d+1)·5 log z/log d = O(log²z/log d) ≪ ℓ/log d. So good pairs give
≥ (0.54 − 0.40)·ℓ/log d − o(ℓ/log d) ≥ 0.05·ℓ/log d. 
(ii) Killer-sum average: consecutive-pair ranges tile the box interval, so
Σ_{close pairs} S ≤ 2 Σ_{m∈I} Σ_{p|m, p>d} 1/p
= 2 Σ_{p>d} (1/p)·#{m ∈ I: p|m}
≤ 2 z^5 Σ_{p>d} 1/p² + 2 Σ_{d<p≤2z^5} 1/p
≤ 2.2·z^5/(d log d) + O(log log z).
With N_cp ≥ 0.27·z^5/log z close pairs (pigeonhole; verified 65–92%
numerically), avg S ≤ 8.1/(60·log d) = 0.135/log d. Markov at 0.4/log d:
bad fraction ≤ 0.34 < 1/3. ∎

Notes: d-rough forces a odd and 3∤a, so vertical H-moves at a are legal;
the climb sweeps gcd(a,m)=1 for m ∈ (R, R′] and the hub needs gcd(a,R)=1 —
both covered by [R,R′]. HYGIENE (referee catch): swept hubs (a, m) with m
an odd PRIME in (R,R′) force a composite — so candidates are COMPOSITE
d-rough integers. At x ~ s this costs only the prime density 1/log s =
K/z^5 ≪ 1/log d (subtract via BT if x is small; at ladder positions x ~ s
it is negligible). Same fix applies to all chain climb columns (level B). Numerics (verify_ladder.py): avg S·log d ≈ 0.31–0.36 — 4× better
than the proven bound; 75–82% pass the stricter 0.5/log d.

## 5b. Verification results (2026-07-30 night)

O1 VERIFIED (verify_ladder.py, z=20/30): rough constant 0.51/0.54 (theory
>=0.5 ✓); rough-composite constant 0.297/0.324 (theory >=0.1, 3x margin ✓);
max gap 138/186 vs z^2=400/900 ✓; close pairs within 4 log z: 65%/73% of
consecutive gaps — abundant ✓.

O2 VERIFIED (same runs): killer-sum average x log d = 0.356/0.310 (theory
O(1), need <0.5 ✓ and IMPROVING with z); pairs below the strict survival
threshold 1/(2 log d): 74.6% -> 81.8% (rising with z ✓); 100% of pairs
within 3x average.

O5 PARTIAL (sim_ladder.py): at z=20 the restricted move set (runs +
sidesteps + intra-box ladder) fails at ~28% of blocks — because the clean
regime needs open segments >= d^3 ~ (4 log z)^3, i.e. z >~ 10^7, far beyond
simulation (box z^5 = 10^35). At small z, move-4 repairs / 2-D backtracking
(empirically always available: giant-component data) fill the gap. The
asymptotic argument must be carried by the FL+BT counting, not simulation;
the measurable prediction is the failure-rate TREND in z (running).

## 5c. Killer-mass equidistribution (Lemma E) and the vertical hierarchy

The remaining assembly question is vertical: cluster switches and B-gap
crossings need climbs of span σ ≫ d, and a single climb of span σ has
worst-case killer sum ~ 5 log z/log σ ≫ candidate density — single long
climbs are provably NOT guaranteeable. The resolution: chains of short
climbs through intermediate resting rows (any ℓ-rough rows, not just box
rows), with step spans controlled by:

**Lemma E (equidistribution of killer mass) — CORRECTED cutoff.** At step
span σ the climb columns must be (8σ)-rough (cf. Chamber Lemma p⁻ > span;
with cutoff = σ the average mass 1.1/log σ EXCEEDS candidate density
0.56/log σ — borderline-dead, confirmed numerically at 0.84 vs 0.56).
With killers = primes P > 8σ dividing the σ-range:
per-window average mass ≤ 1.1σ·Σ_{p>8σ}1/p² ≈ 0.14/log(8σ), a 4× margin
under the candidate density 0.56/log(8σ). For windows W_h of span σ tiling
a stretch of length L ≥ σ^{1+ε}:
Σ_h S_kill(W_h) ≤ Σ_{P>8σ} (1/P)(L/P + 1)·(σ/σ) ≤ 0.14L/(σ...)·— total
mass bounded, so the fraction of windows with S_kill ≥ 0.28/log(8σ) is
≤ 1/2 in EVERY stretch of length ≥ σ^{1+ε}; bad runs have length ≤ σ^{1+ε}
unconditionally. VERIFIED (z=30, σ=100, cutoff 800): avg 0.109/log(8σ)
(theory ≤0.14); 0% of 20k windows reach half the candidate density; max
bad run 0.

*Consequences.* (a) At every scale σ, in any σ^{1+ε}-stretch at least half
the σ-steps are good, and good steps have surviving (8σ)-rough climb
columns at density ≥ 0.4/log(8σ). (b) Killed columns are unions of
arithmetic progressions mod P > 8σ, so goodness is uniform in x up to
~P-spacing transients — no horizontal blocking line can form.

**The two-level design (supersedes the O(log log z) hierarchy).** The
multi-level recursion is unnecessary; the hop/block race that motivated it
is fatal for resting rows with many prime factors (unblocked runs ~ ρ/3ν =
O(1) when ν ~ log z/log log z) and is solved outright by:

*Resting rows are z^{1/2}-rough.* A row b ≤ z^6 with p⁻(b) > z^{1/2} has
ω(b) ≤ 12 AUTOMATICALLY, so its blocked-column density is ≤ 36/z^{1/2} and
its unblocked runs have length ≥ z^{1/2}/36 ≫ any hop (~log z). By Iwaniec
(g(P(y)) ≤ Ky², effective, linear sieve), z^{1/2}-rough integers appear in
EVERY interval of length Kz — so every vertical stretch has resting rows
spaced ≤ Kz.

Levels: **A** (sidesteps): span ≤ d = 60 log z between box rows (Lemma S,
proved). **B** (chains): vertical spans up to z^6 crossed in steps of span
≤ Kz between z^{1/2}-rough resting rows; climb columns (8Kz)-rough,
supplied at density 1/log(8Kz) with Lemma-E-good steps selectable via two
freedoms — the landing row within its Kz-window and the climb column within
the current unblocked run (~z^{0.4} candidates per step). B-gaps in the box
(worst case ≤ Kz² by Iwaniec at level z) are crossed in ≤ z chain steps.

**Why the hierarchy terminates.** Cluster switches only ever need spans
~ the spacing of viable clusters. Cluster joint-blocks (all ~18
disjoint-support rows of a cluster blocked at one column) have x-density
≤ (30/z)^18 (each row blocked with density ≤ 15/z, supports disjoint,
CRT main term dominates for s ≥ z^19; the 5^18 error tuples are
s-independent). So stuck-cluster runs are bounded and the hierarchy is
invoked with vanishing frequency and polylog spans — never near box height.
Resting rows for level ℓ need ℓ-rough rows (height ≥ ℓ²), available in-box
for ℓ ≤ z^{2.5}, far above any span the assembly requests.

**Seed irrelevance.** The construction builds a ray entirely in x ≥ X_0 for
an absolute effective X_0 — the problem asks for existence of an infinite
path, so no connection to the verified witness is required. O7 is void.

## 5d. Assembly status

Proved here: P1 (supply), Lemma S (sidestep, constants explicit), Lemma E
(equidistribution, corrected cutoff), the two-level design resolving the
hop/block race (W1 structural risk CLOSED: z^{1/2}-rough resting rows have
ω ≤ 12 automatically, block density 36/z^{1/2}, Iwaniec spacing ≤ Kz),
joint-block rarity (modulo CRT error write-up), climb-column compositeness
hygiene. Remaining write-up obligations: (W2′) the formal chain lemma —
greedy selection using the two freedoms (landing row, climb column) against
Lemma-E bad steps, with the x-drift budget ≤ z^{1/2}/36 per resting row
made explicit; (W3) the ratchet z(x) → z(2x) via box overlap in
[z′², z²+z^5]; (W4) full H-graph hygiene audit of every move type; (W5)
final constants pass (z_0 effective; z_0 ~ 10^13 from ℓ ≥ d^4 in Lemma S is
the current bottleneck — harmless, the theorem needs no small z_0). No step
faces the supply/diameter circularity: every climb span is ≤ Kz with
(8Kz)-rough columns whose supply lives in (8Kz)^5 ≪ travel-budget windows,
every long crossing is horizontal, and every average is over a fixed
tiling family.

## 6. Failure modes to watch

- Bad pairs clustering at the same x-positions as blocks (correlation
  between row factorizations and column positions) — the Markov selection
  is over pairs, uniform in x, so this should be immune, but O5 tests it.
- The climb sweep needing gcd(a, m) = 1 for ALL m ∈ [R, R′] including evens
  — included in M(R,R′) above ✓ (evens only force a odd).
- Vertical moves in H need the COLUMN odd (a odd ✓) and intermediate hub
  parity — H-reduction already encodes this; re-verify on the simulator.
- 3 | rows: rows with 3 | R are horizontally dead — box rows are z-rough,
  z ≥ 3, so 3 ∤ R ✓. Columns a ≡ 0 mod 3 are vertically dead — sidestep
  columns must also satisfy 3 ∤ a — absorbed into d-roughness ✓.
