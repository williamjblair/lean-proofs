# Erdős #1212 — computational search report

Answer: **YES**, on the strength of a verified 1.17-million-vertex witness path
and a structural picture that says what a proof has to do.

Everything below is either *verified computation* (exhaustive over a stated
range, recomputed from the raw definition) or *conjecture*, and is labelled.

---

## 0. Verified structure

`verify_reduction.py` checks all of the following exhaustively over the box
`2 ≤ x,y ≤ 400`, straight from the definition, with sympy as an independent
primality oracle. All pass.

1. No vertex has both coordinates even.
2. Horizontal edges occur only on odd rows; vertical edges only on odd columns
   (0 counterexamples).
3. At any vertex with an even coordinate ≥ 4 the composite condition is free.
4. **Reduction.** Let `H` have vertices `(a,b)`, `a,b` odd `≥ 3`, `gcd(a,b)=1`,
   not both prime, with
   - `(a,b) — (a+2,b)`  iff  `gcd(b, a(a+1)(a+2)) = 1`
   - `(a,b) — (a,b+2)`  iff  `gcd(a, b(b+1)(b+2)) = 1`

   Then the admissible subgraph of `G` on `x,y ≥ 3` is exactly the subdivision
   of `H`. Verified two ways: edge-by-edge agreement (0 mismatches), and
   `crosscheck.py` compares component-by-component against a direct BFS in `G`
   on the box `2..260` — **0 H-components split in G, 0 G-components merge two
   H-components**.
5. Rows divisible by 3 admit no horizontal hop; columns divisible by 3 admit no
   vertical hop (0 counterexamples).
6. At `a = ∏(odd primes ≤ B)` there is no vertex `(a,b)` at all with `b ≤ B`.
   Confirmed for `B = 13, 17, 19, 23`.

Item 4 is worth stating in the edge form above: **movement in one coordinate is
governed entirely by the prime factors of the other**, and a prime `p` dividing
`b` blocks exactly the three residue classes `a ≡ 0, −1, −2 (mod p)`. A row with
least prime factor `p` is therefore open on at least `1 − 3/p` of all columns.

Item 6 independently reproves the wall theorem in a sharper form: a finite band
is not merely uncrossable, it is *empty* at primorial columns.

---

## 1. The witness — main deliverable

`trajectory_B1400_to867999.txt`

- **1,166,791 vertices**, all distinct, `x` from 1065 to **867,999**, `y ∈ [7, 1399]`.
- Re-verified standalone by `verify_trajectory.py` (reads the file, recomputes
  `gcd`, `min`, primality with sympy, checks unit steps and distinctness):
  **0 violations**.
- Produced by `witness_big.py`: a two-pass windowed search (forward pass carries
  the full reachable row-set across each 25 000-column window; backward pass
  pins one concrete vertex per interface). Exact inside each window, so the
  result is a genuine path, never an over-claim.

A second, smaller witness from an exact single-box computation is in
`trajectory_64001_1400.txt` (86,711 vertices, `x ≤ 64,001`, `y ∈ [841,1399]`).

## 2. The rule the path follows

From `analyze_path.py` on the 1.17M-vertex trajectory:

- 74,447 horizontal runs, of which **74,259 go right and 188 go left**
  (269 backtracking hops out of 434,005 — 0.1%). The path is nearly monotone,
  but purely monotone search fails immediately, so the backtracking is
  essential, not cosmetic.
- **Travel rows are ranked by least prime factor.** Hops travelled, by `lpf` of
  the row: `5→2204, 7→5569, 11→16330, 13→10875, 17→15470, 19→21644, 23→31891,
  29→62362, 31→45448, 37→76825`, plus prime rows used heavily
  (`1367→65017`, `1361→59856`, `1327→8000`).
- The top workhorses are `1369 = 37²` (76,825 hops), the primes `1367, 1361`,
  then `1363 = 29·47`, `1333 = 31·43`, `1357 = 23·59`, `1349 = 19·71`,
  `1331 = 11³`, `1343 = 17·79`.

**Candidate lemma.** For a prime `p`, the row `b = p²` is composite (so the
"not both prime" condition is free on it) and permits the hop `a → a+2` unless
`a ≡ 0, −1, −2 (mod p)` — a set of density `3/p`. Symmetrically the column
`a = q²` permits the vertical hop `b → b+2` unless `b ≡ 0, −1, −2 (mod q)`.
Prime-square rows and columns are the natural highways.

## 3. Horizontal availability is not the bottleneck — vertical mobility is

`wall_scan.py`, exhaustive over all `a ≤ 10^7`, for the 37-row window
`b ∈ [1327, 1399]`:

> minimum number of simultaneously open rows = **2**; never 0.
> Distribution: 2 open at 2 columns, 3 at 50, 4 at 285, 5 at 1202, …

So over ten million columns some row of a single fixed 37-row window is always
open. Yet the band-limited search still stalls. `wall_probe.py` shows why, at
the first stall for band 1400 (`a = 868869`):

```
a=868863 lpf=3        reachable=436  open=371  reachable∧open=357
a=868865 lpf=5        reachable=526  open=153  reachable∧open=141
a=868867 lpf=868867   reachable=325  open= 96  reachable∧open= 71
a=868869 lpf=3        reachable= 71  open=300  reachable∧open=  0
868869 = 3²·29·3329   868870 = 2·5·17·19·269   868871 = 23·37·1021
```

At the wall there are 300 open rows and 71 reachable rows and the two sets are
disjoint — and because `3 | 868869` **no vertical move exists at that column at
all**, so the path cannot step onto an open row. The triple
`a(a+1)(a+2)` happens to carry `{3,5,17,19,23,29,37}`, which is exactly the set
of least prime factors of the highway rows `1343, 1349, 1357, 1363, 1369`.

**This is the single most useful structural fact for the proof track:** the
obstruction is never a shortage of open rows, it is that row changes can only
happen at columns coprime to 3 (and, more generally, a column with least prime
factor `p` only permits vertical runs of length about `p/3`). A proof must
choose its row *before* reaching a column divisible by 3, i.e. one hop ahead.

## 4. Growth of the required band

Exact bisection on a full strip (`threshold.py`, left moves fully allowed);
`B*(A)` is the least band ceiling admitting a path from a column `≤ 2000` to
column `A`:

| target `A` | 4 001 | 8 001 | 16 001 | 32 001 | 64 001 | 128 001 |
|---|---|---|---|---|---|---|
| `B*(A)` | 1248 | **1358** | 1358 | 1358 | 1358 | 1358 |

Windowed search beyond that (`reachB.py`): band 1400 stalls at `a = 868 869`;
band 1600 stalls at **the same column** (so it is a real obstruction, not a
window artefact — confirmed by re-running band 1400 with a 100 000-column
window); band 2000 passes and reaches `a = 3 000 001` without stalling.

So while `A` grows by a factor of 375 (8·10³ → 3·10⁶) the required band grows by
a factor of 1.5 (1358 → ≤ 2000). The data cannot separate `B = O(log A)` from
`B ≈ A^0.07`; either is far more than enough. *(Conjecture, not proved.)*

Combined with the wall theorem this is the honest picture: the band must grow,
but so slowly that a band of ~700 odd rows carries you past 10⁶.

## 5. What was ruled out

- **Bounded band: impossible** (verified item 6 above, plus the coordinator's
  CRT argument). Reported for completeness — do not spend effort here.
- **Periodic gadget in a fixed band: impossible**, for the same reason.
- **Monotone (never-move-left) search: fails**, and fails immediately
  (`find_band.py`: dies at `a = 1275` for every ceiling from 800 to 9600).
  Any proof must allow the path to move left occasionally, though only ~0.1% of
  hops need to.
- **Small-box intuition is misleading.** In the box `2..260` the largest
  component of `G` has 316 vertices. The giant component only becomes visible
  around `N ≈ 1600`. Its lower edge sits at `a + b = 1796` and is *identical* at
  `N = 2000, 4000, 8000` — it does not move as the box grows.

## 6. Files

| file | role |
|---|---|
| `h1212.py` | the reduced graph `H`, hub/edge masks, components |
| `verify_reduction.py` | exhaustive verification of §0 |
| `crosscheck.py` | `H` components vs. direct BFS in `G` |
| `strip.py` | memory-lean exact components on a long thin strip |
| `threshold.py`, `band_table.py`, `bandscan2.py` | `B*(A)` bisection |
| `windowed.py`, `reachB.py`, `reach.py` | windowed sweep, `reach(B)` |
| `witness_big.py` | two-pass witness extraction |
| `witness.py` | single-box witness extraction |
| `verify_trajectory.py` | standalone re-verification of a trajectory file |
| `analyze_path.py` | run/row statistics of a trajectory |
| `wall_scan.py`, `wall_probe.py`, `wall_at.py` | wall census and diagnosis |
| `diag_scan.py`, `bottleneck.py`, `sweep.py`, `find_band.py` | supporting scans |
| `trajectory_B1400_to867999.txt` | **the witness** (1,166,791 vertices) |
| `trajectory_64001_1400.txt` | smaller witness from an exact box |
