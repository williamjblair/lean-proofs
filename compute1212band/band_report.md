# Erdős #1212 — band-extension measurement

**Headline: YES — the escape cost ΔY stays small enough for band extension to be a
viable proof route.** Across **391 confirmed traps**, **0 were Wall-Lemma columns**;
every one was a local connectivity trap. The minimal upward band extension that carries
the search past a trap and sustains it 1000 further columns has median **ΔY = 148**
overall, and for every base band above the percolation threshold (Y ≥ 800) the median is
**54–215 rows, i.e. 6–15 % of Y**, with observed maximum 564. It does not grow with x
(medians 248 / 102 / 158 / 148 over the decades 10⁴, 10⁵, 10⁶, 10⁷). Riding the ratchet
from Y = 1400, exactly **two** extensions (1399 → 1685 → 1849) carried an exact frontier
from x ≈ 10³ to x = 2 × 10⁷, a rate of ≈ **95 rows per e-fold of x**; band 2000 needed
**zero** extensions to reach x = 10⁷.

---

## 0. Setup, and what is trusted

Everything is rebuilt from scratch here; nothing is imported from `compute1212/`,
`compute1212search/` or `compute1212pct/`.

`verify_reduction.py` re-derives the hub reduction from the **raw** definition of G on
the box [2,300]²:

```
admissible=50414 hubs=14274 links=36140 bad=0
links with even coord 2 having >1 admissible nbr: 0
hub-hub pairs joined by a link: 10474
edge sets equal: True  |raw|=10474 |hub.py|=10474
component agreement on hubs with max coord <= 150: True
```

The admissible subgraph of G is bipartite between hubs (both coordinates odd ≥ 3) and
links (exactly one even coordinate); links with even coordinate ≥ 4 have exactly two hub
neighbours; links with even coordinate 2 are dead ends; the induced hub-to-hub adjacency
is *identical* to the H built by `hub.py`, and components agree on the interior sub-box.
The reduction is exact, not merely sound.

**Bands only grow upward.** b = 3 is the floor of H, so [3,Y] has no downward direction.
Every ΔY below is an upward extension; the "or downward if it helps" branch of the
question is vacuous.

**Method.** Blocks of W = 5000 hub-columns; inside a block the search is exact with free
backtracking (right/left sweeps to a fixpoint, with a vertical closure in every column);
the block interface carries the exact reachable row-set. Every stall is re-confirmed from
the previous checkpoint over a longer span, so block-boundary artefacts are removed.
Escape costs are bisected from a checkpoint ≤ 1200 columns behind the trap; reachability
is monotone in the band (extra rows only add vertices and edges) so the bisection is
valid, and since backtracking beyond 1200 columns is not explored, **every reported ΔY is
an upper bound** on the true escape cost.

Two experiment families:

- **ratchet** — ride band Y to a trap, measure ΔY, keep the enlarged band, continue.
- **flood** — fixed band Y, frontier seeded with *every* vertex of the starting column
  (maximally generous, path-independent), run to a trap, measure ΔY, re-flood just past
  it. Runs measured this way are the longest column-runs band Y can traverse at that
  scale, so their trap density is a **lower bound** on what any path must face.

---

## 1. Trap census

### 1a. Fixed band (flood): how far each band gets, how often it stalls

Lengths in hub-columns (1 column = 2 in x). Decade D*k* = window starting at 10^k.

| Y | decade | cols covered | traps | traps / 10⁵ cols | median run | max run | walls |
|---|---|---|---|---|---|---|---|
| 400 | 10⁴ | 1 146 | 30 | 2618 | 28 | 105 | 0 |
| 400 | 10⁵ | 1 710 | 30 | 1754 | 41 | 161 | 0 |
| 400 | 10⁶ | 2 649 | 30 | 1133 | 66 | 347 | 0 |
| 400 | 10⁷ | 2 586 | 30 | 1160 | 74 | 229 | 0 |
| 800 | 10⁴ | 11 805 | 30 | 254 | 266 | 1 326 | 0 |
| 800 | 10⁵ | 16 830 | 30 | 178 | 411 | 1 747 | 0 |
| 800 | 10⁶ | 35 295 | 30 | 85.0 | 734 | 3 930 | 0 |
| 800 | 10⁷ | 40 254 | 30 | 74.5 | 850 | 5 575 | 0 |
| 1000 | 10⁴ | 45 000 | 9 | 20.0 | 2 829 | 10 064 | 0 |
| 1000 | 10⁵ | 321 591 | 30 | 9.33 | 5 703 | 45 841 | 0 |
| 1000 | 10⁶ | 399 793 | 30 | 7.50 | 7 033 | 59 695 | 0 |
| 1000 | 10⁷ | 500 000 | 22 | 4.40 | 13 952 | 70 146 | 0 |
| 1200 | 10⁴ | 45 000 | 4 | 8.89 | 5 727 | 21 734 | 0 |
| 1200 | 10⁵ | 450 000 | 16 | 3.56 | 21 906 | 107 404 | 0 |
| 1200 | 10⁶ | 500 000 | 16 | 3.20 | 24 080 | 97 882 | 0 |
| 1200 | 10⁷ | 500 000 | 7 | 1.40 | 73 259 | 97 954 | 0 |
| 1400 | 10⁴ | 45 000 | 0 | 0 | — | — | 0 |
| 1400 | 10⁵ | 450 000 | 1 | 0.22 | 384 434 | 384 434 | 0 |
| 1400 | 10⁶ | 500 000 | 2 | 0.40 | 247 140 | 420 877 | 0 |
| 1400 | 10⁷ | 500 000 | 1 | 0.20 | 290 108 | 290 108 | 0 |
| 1600 | 10⁴ | 45 000 | 0 | 0 | — | — | 0 |
| 1600 | 10⁵ | 450 000 | 1 | 0.22 | 384 434 | 384 434 | 0 |
| 1600 | 10⁶ | 500 000 | 0 | 0 | — | — | 0 |
| 1600 | 10⁷ | 500 000 | 0 | 0 | — | — | 0 |

Band 1600 crossed 1.5 million hub-columns spread over four decades with **one** trap.
Band 400 cannot manage 100 columns.

### 1b. Ratchet: how far, how many extensions

| start Y₀ | reached x | traps | final band | wall clock |
|---|---|---|---|---|
| 1400 | 5 000 001 | 2 | 1849 | 682 s |
| 1400 (long run) | **20 000 001** | **2** | 1849 | 2027 s |
| 2000 | 10 000 001 | **0** | 1999 | 1209 s |
| 400 | 3 000 001 | 8 | 1685 | 422 s |

Per-trap detail (ratchet runs):

| a\* | log₁₀ | band at trap | run since last (cols) | ΔY_pass | ΔY_L | open rows | reach rows | wall? | 3\|a\* |
|---|---|---|---|---|---|---|---|---|---|
| 28 445 | 4.45 | 399 | 181 | 10 | 452 | 22 | 4 | no | no |
| 30 669 | 4.49 | 851 | 112 | 48 | 48 | 83 | 6 | no | yes |
| 34 161 | 4.53 | 899 | 746 | 2 | 2 | 255 | 2 | no | yes |
| 37 587 | 4.58 | 901 | 713 | 60 | 346 | 103 | 2 | no | yes |
| 142 599 | 5.15 | 1247 | 51 506 | 26 | 26 | 110 | 22 | no | yes |
| 272 367 | 5.44 | 1273 | 63 884 | 70 | 70 | 200 | 3 | no | yes |
| 556 867 | 5.75 | 1343 | 141 250 | 48 | 54 | 168 | 4 | no | no |
| **868 869** | 5.94 | 1397 / 1399 | 155 001 / 433 902 | 284 / 282 | 288 / 286 | 299 / 300 | 71 | no | yes |
| **4 690 119** | 6.67 | 1685 | 1 909 625 | 164 | 164 | 115 | 4 | no | yes |

The long run repeats both traps identically and then covers a further **7 654 940
columns** to x = 2 × 10⁷ with no third trap.

a\* = 868 869 is reproduced independently by both ratchet runs and by the Y = 1400 and
Y = 1600 flood runs — a genuine band-1400-scale obstruction, and the same stall the
earlier band-1400 search reported. It is **not** a wall: 300 rows of the band are open
there, but only 71 rows are reachable and the two sets are disjoint.

---

## 2. Escape cost ΔY — the key number

`ΔY_pass` = minimal extra rows to get past a\* at all.
`ΔY_L` = minimal extra rows to get past **and sustain 1000 further columns**.
Units of b, so ΔY = 2 is one extra row.

| quantity | n | mean | median | p90 | max |
|---|---|---|---|---|---|
| ΔY_pass | 377 | 99.6 | 74 | 248 | 520 |
| ΔY_L | 377 | 220.5 | 148 | 454 | 682 |

ΔY_L exceeded the cap (4Y) in 14 of 391 cases — **all** at base band Y = 400, which is far
below the percolation threshold.

**By base band. This is where the question is decided:**

| base band Y | n | median ΔY_L | mean | max | median ΔY_L / Y |
|---|---|---|---|---|---|
| 400 | 107 | 452 | 437.7 | 682 | **1.133** |
| 800 | 123 | 54 | 120.6 | 564 | **0.068** |
| 1000 | 91 | 148 | 160.3 | 544 | **0.148** |
| 1200 | 47 | 74 | 111.1 | 486 | **0.062** |
| 1400 | 6 | 215 | 206.7 | 286 | **0.154** |
| 1600 | 3 | 164 | 138.0 | 164 | **0.097** |

Below the threshold (Y = 400) escaping costs more than doubling the band. At and above
Y = 800 the cost collapses to **6–15 % of the band, absolutely in the 54–215 range**, and
shows no upward drift as Y grows.

**By decade of x — the x-dependence, all traps pooled:**

| decade of a\* | n | median ΔY_L | mean | max |
|---|---|---|---|---|
| 10⁴–10⁵ | 68 | 248 | 253.8 | 502 |
| 10⁵–10⁶ | 111 | 102 | 213.4 | 682 |
| 10⁶–10⁷ | 109 | 158 | 231.9 | 608 |
| 10⁷–10⁸ | 89 | 148 | 189.9 | 544 |

**By decade at fixed band** (cleanest, holds Y constant — median ΔY_L):

| Y | 10⁴ | 10⁵ | 10⁶ | 10⁷ |
|---|---|---|---|---|
| 400 | 452 | 502 | 454 | 314 |
| 800 | 102 | 54 | 54 | 54 |
| 1000 | 248 | 111 | 148 | 144 |
| 1200 | 48 | 74 | 74 | 134 |
| 1400 | — | 286 | 119 | 144 |
| 1600 | — | 86 | — | — |

Flat or falling in x. **Nothing here grows even like log x**, let alone like a constant
fraction of the band.

**Band trajectory under the ratchet** — the proof-relevant quantity:

```
Y0=1400:  x=1065     band 1400
          x=868869   band 1685      (dY = 286)
          x=4690119  band 1849      (dY = 164)
          ... no further trap through x = 2e7 (7.65e6 columns clear)
          fit  Y ~ 95*ln(x) + 381        (95 rows per e-fold of x)

Y0=2000:  x=1065 -> x=10000001, band 1999 throughout, no trap at all

Y0=400:   400 -> 851 -> 899 -> 901 -> 1247 -> 1273 -> 1343 -> 1397 -> 1685
          (all by x = 868869), then no trap through x = 3e6
          fit  Y ~ 172*ln(x) - 812
```

Both ratchets converge onto the same trajectory once above the threshold: they agree
exactly at the a\* = 868 869 obstruction and both leave it at band 1685. A band growing
like ≈ 100·ln x is far inside what an induction can afford.

**Is L = 1000 a fair "sustained escape"?** The runs following an escape are far longer
than L: 112, 746, 713, 51 506, 63 884, 141 250, 155 001, 433 902, 1 909 625 columns. Only
the three short ones occur below band 1000. Above the threshold, an escape verified for
1000 columns in practice lasts 10⁵–10⁶ columns.

---

## 3. Is the wall ever the real obstruction? — **No. Not once.**

**3a. Per-trap.** For each trap, count band rows *open* at a\* (horizontal edge
(a\*,b)–(a\*+2,b) present in H). A Wall-Lemma column is exactly `open = 0`.

```
traps                                   391
genuine Wall-Lemma columns (open==0)      0   (0.00 %)
local traps (open>0 but unreachable)    391   (100.00 %)
open rows at a*:      median  98,  mean 120.9,  min 1,  max 382
reachable rows at a*: median   3,  mean  13.0,  min 1,  max 246
row distance frontier -> nearest open row: median 2, mean 3.3, max 28
```

Not one trap in 391. The typical trap has ~98 open rows and a frontier of ~3 rows sitting
**one row** away from the nearest open one, unable to reach it.

**3b. Global scan of every column** (`wallscan.py`, independent of any search):

| Y | range scanned | min over a of open(a,Y) | first wall column | # walls in range |
|---|---|---|---|---|
| 400 | ≤ 10⁷ | **0** | 62 985 | 81 |
| 800 | ≤ 10⁷ | **0** | 1 540 539 | 8 |
| 1000 | ≤ 10⁷ | 3 | — | 0 |
| 1000 | ≤ 10⁸ | **0** | **64 822 393** | 1 |
| 1200 | ≤ 10⁷ | 5 | — | 0 |
| 1400 | ≤ 10⁸ | 1 | — | 0 |
| 2000 | ≤ 10⁸ | 5 | — | 0 |

Walls are not mythical: they genuinely occur for Y ≤ 1000 within 10⁸. But **the searches
never meet one.** Band 800 dies at a local trap every ~800 columns and would need ~2000
consecutive escapes to reach its first wall at 1.5 × 10⁶; band 1000 stalls every ~7 000
columns and its first wall is at 6.5 × 10⁷, four orders of magnitude out. For Y ≥ 1200 no
wall exists below 10⁸ at all, and the margin grows: min open = 1 (Y = 1400) and 5
(Y = 2000).

**The near-wall has exactly the CRT structure the Wall Lemma predicts**, which is why it
can be located and why it is so far away. The worst column for every band is the same
one, a = 64 822 393, and

```
64822393 = prime
64822394 = 2 · 7² · 13 · 17 · 41 · 73
64822395 = 3 · 5 · 11 · 19 · 23 · 29 · 31
```

a is prime, which kills every prime row b for free (the "not both prime" rule), and
**every odd prime up to 31 divides a(a+1)(a+2)**, which kills every composite row whose
least prime factor is ≤ 31. Since every odd composite b ≤ 1000 has a prime factor
≤ √1000 = 31.6, band 1000 is completely walled. Band 1400 needs 37 as well — 37 divides
none of the three — so exactly one row survives (open = 1). Band 2000 needs 37, 41, 43;
only 41 appears, leaving open = 5.

That also gives the scaling. A wall needs either (i) a, a+2 both composite, forcing every
odd prime p ≤ Y to divide a(a+1)(a+2), i.e. a ≳ exp(θ(Y)/3) = 10^193.6 for Y = 1400 and
10^280.7 for Y = 2000; or (ii) a or a+2 prime plus every odd prime p ≤ √Y dividing
a(a+1)(a+2), a CRT condition of modulus ≈ 10^12.6 for Y = 1400 and 10^15.8 for Y = 2000.
Either way the first wall for a band of the size the search actually uses is
astronomically beyond any reachable x. **The Wall Lemma is a red herring at every
reachable scale — hypothesis confirmed.**

---

## 4. Does trap frequency decay?

At fixed band, yes. Traps per 10⁵ hub-columns:

| Y | 10⁴ | 10⁵ | 10⁶ | 10⁷ | ratio 10⁴→10⁷ |
|---|---|---|---|---|---|
| 400 | 2618 | 1754 | 1133 | 1160 | 2.3× |
| 800 | 254 | 178 | 85.0 | 74.5 | 3.4× |
| 1000 | 20.0 | 9.33 | 7.50 | 4.40 | 4.5× |
| 1200 | 8.89 | 3.56 | 3.20 | 1.40 | 6.4× |
| 1400 | 0 | 0.22 | 0.40 | 0.20 | — |
| 1600 | 0 | 0.22 | 0 | 0 | — |

Median run length grows monotonically with x at every band: Y = 800 gives 266 → 411 →
734 → 850; Y = 1000 gives 2 829 → 5 703 → 7 033 → 13 952; Y = 1200 gives 5 727 → 21 906 →
24 080 → 73 259. Decay in x is modest (a factor of a few per three decades); **decay in Y
is violent** — at a fixed decade the density falls by roughly an order of magnitude per
200–400 rows of band, and is effectively zero by Y ≈ 1600.

With the band growing (the ratchet, Y ≈ 95 ln x) the density collapses outright: the
Y₀ = 1400 ratchet met 2 traps in 10⁷ hub-columns, and the gaps between consecutive traps
grew 4.3 × 10⁵ → 1.9 × 10⁶ → **7.65 × 10⁶** columns (the last one trap-free all the way
to the x = 2 × 10⁷ cutoff) — runs lengthening faster than x itself. That is the shape a percolation/induction argument needs.

---

## 5. Mechanism: why reachable rows and open rows are disjoint

Over all 391 traps:

| cause | count | share | share for a random odd column |
|---|---|---|---|
| **3 \| a\*** — column has *no vertical edge at all* | 261 | 66.8 % | 33.3 % |
| frontier had no vertical move available at a\* | 271 | 69.3 % | — |
| … of those, because 3 \| a\* | 261 | 96.3 % | — |
| frontier *could* move vertically but was still stuck | 120 | 30.7 % | — |
| 5 \| a\* | 87 | 22.4 % | 20.0 % |
| 7 \| a\* | 80 | 20.6 % | 14.3 % |

Smallest odd prime factor of the trap column:

```
spf =  3: 261 (66.8 %)     spf =  7: 17 (4.3 %)     spf = 13:  1 (0.3 %)
spf =  5:  55 (14.1 %)     spf = 11:  4 (1.0 %)     spf > 13: 53 (13.6 %)
```

The dominant mechanism is exactly the one the hypothesis named. **3 | a\*** kills every
vertical move in that column: among b, b+1, b+2 one is always divisible by 3, so
gcd(a, b(b+1)(b+2)) ≥ 3 for *every* row. The frontier therefore arrives frozen on whatever
rows it landed on, and each of those must be individually blocked horizontally. Two thirds
of all traps are of this kind — double the 33 % base rate — and they account for 96 % of
the frozen-frontier traps.

It is **not** the only mechanism. In 31 % of traps the frontier *could* move vertically at
a\* and still could not reach an open row: the column's vertical runs are chopped up (5 | a
removes vertical edges for 3 of every 5 rows, 7 | a for 3 of every 7), so the frontier sits
inside a short vertical run whose rows are all horizontally blocked while open rows lie in
a neighbouring run. Columns divisible by 5 and 7 are over-represented among traps by 12 %
and 44 % relative to chance, consistent with this.

The median row distance from the frontier to the nearest open row is **2 — one single
row** — and the maximum is 28. The frontier is nearly always *adjacent* to an escape it
cannot take. That is precisely why a small band extension fixes it: the extra rows above
supply a detour around the blocking run a few columns earlier.

---

## 6. Verified witness of the mechanism

`witness.py` extracts an explicit band-extension path — band [3,1399] to x = 866 001, then
band [3,1685] across the a\* = 868 869 trap and on to x ≈ 10⁶ — and `checkpath.py`
re-checks it independently, straight from the definition of G, with no part of the H
machinery:

```
vertices=1413051 duplicates=0 bad_vertices=0 bad_steps=0
x from 1065 to 1001065; y in [667,1685]
VERIFIED
max y before a=866001: 1399      max y after: 1685
```

1 413 051 vertices, every one satisfying gcd(x,y) = 1, min(x,y) > 1 and at least one
coordinate composite; every consecutive pair a unit step in one coordinate; no repeats.
The band-extension mechanism is not an artefact of the frontier bookkeeping — it produces
a genuine path in G.

---

## Verdict

**Yes.** The deciding numbers: **0 walls in 391 traps**; median ΔY_L = 54–215 rows
(6–15 % of Y) for every base band from 800 to 1600, maximum 564 anywhere above the
threshold; ΔY_L flat in x across four decades at fixed band; a ratchet that carried an
exact frontier from x = 10³ to x = 2 × 10⁷ with two extensions totalling 450 rows
(Y ≈ 95 ln x); and band 2000 reaching x = 10⁷ with no extension at all. The
Jacobsthal/rough-anchor barrier that kills anchored-staircase constructions does not
appear, because the construction never anchors — it only widens by ~100 rows every few
million columns.

**Caveats a careful reader should keep.**

1. All ΔY are **upper bounds** under a 1200-column backtrack budget; true minima can only
   be smaller.
2. The ratchet has only two extension events above Y = 1400, so the *rate* Y ≈ 95 ln x
   rests on two points. The *bound* — ΔY ≤ ~300 per trap above the threshold — is much
   better supported (377 measurements).
3. "Sustained escape" is 1000 further columns. A trap recurring after 1000 columns is
   counted twice, which inflates trap counts rather than hiding them.
4. None of this proves ΔY is bounded. It shows that over 391 traps spanning
   x ∈ [10⁴, 2 × 10⁷] it never exceeded 682, and never exceeded 564 for any band above
   the threshold.
5. Walls **do** exist and were located (Y = 400 at 62 985; Y = 800 at 1 540 539; Y = 1000
   at 64 822 393). Any eventual proof still has to say something about them — but at the
   band sizes the search actually uses (Y ≳ 1400) the nearest wall is beyond 10⁸ and the
   CRT bound puts the general case at 10^12–10^193. They are not the operative obstruction
   at any scale reachable by computation, and a band-extension induction that widens by
   ~100 rows per e-fold outruns them: the wall threshold grows at least like exp(√Y).

---

## Files

| file | what |
|---|---|
| `hub.py` | H from scratch: residue-sieve block builder, column-contiguous exact reach |
| `verify_reduction.py` | proves the H-reduction against raw G on a box |
| `census.py` | ratchet / flood / restart searches, trap confirmation, ΔY bisection |
| `runflood.py` | fixed-band decade sweeps |
| `wallscan.py` | open(a,Y) for every column in a range; wall census + CRT bounds |
| `witness.py` | explicit band-extension path in G |
| `checkpath.py` | independent verifier of that path from the raw definition |
| `analyze.py` | every aggregate table above (output in `analysis.txt`) |
| `r*.json`, `flood_*.json`, `wall_*.txt`, `log_*.txt`, `witness_path.txt` | raw outputs |
