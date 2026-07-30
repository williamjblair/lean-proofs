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
- **64** (Erdős–Gyárfás, $1000, open) → in-repo campaign:
  [docs/plans/erdos64-campaign.md](docs/plans/erdos64-campaign.md),
  artifacts in `compute64/`. 2026-07-30: general counterexample bound raised
  17 → 18+ (exhaustive, self-contained); Markström's cubic counts reproduced;
  PSV vertex-transitive census scan with per-graph cycle certificates;
  Carr 2026 + jul059 2/3-density lemmas verified.
