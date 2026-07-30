# FRONTIER.md

The Erdős campaign dashboard moved out with the in-progress work. This repo now
hosts only solved problems (see `README.md`).

- **Erdős 730** — SOLVED here: `Erdos730.FullDensityTheorem.pairSet_infinite`,
  infinitely many consecutive central binomial coefficients with identical prime
  support. Unconditional, kernel-proved (axioms ⊆ `[propext, Classical.choice,
  Quot.sound]`). Provenance in `compute730/`.
- **Erdős 154** — proved Sidon sumset equidistribution lemma.

Open campaigns and their frontier state:

- **686** → [erdos-686](https://github.com/williamjblair/erdos-686)
- **23, 617, 699, 727** → [erdos-frontier](https://github.com/vela-science/erdos-frontier)
- **64** (Erdős–Gyárfás, $1000, open), **848, 1004, 1139, 1212** →
  branch [`erdos-campaign-2026-07-30`](https://github.com/williamjblair/lean-proofs/tree/erdos-campaign-2026-07-30)
  (code, writeups and certificates; none of these problems is solved).
  2026-07-30 on #64: counterexample lower bound raised 17 → **≥ 19 vertices**
  (orders 4–18 exhausted, 834,711,846 graphs at n=18); Potočnik–Spiga–Verret
  cubic vertex-transitive census scanned to order 1280, all 111,705 graphs
  killed with verified cycle certificates; Markström's {C₄,C₈}-free counts
  reproduced exactly at n=24/26/28 (4/23/251); Carr's lemmas and the forum's
  2/3-density lemma verified.
