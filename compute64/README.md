# Erdős campaign working directories

Unlike the rest of this repository — which hosts only solved problems with
complete, kernel-clean Lean proofs — the `compute<N>/` directories and
`docs/plans/erdos*` hold **in-progress campaign material**: verification code,
writeups, and small certificates for open Erdős problems.

None of these problems is solved. Each writeup states its own status honestly
(SOLVED / PARTIAL / GAP-REMAINS) at the top.

Deliberately **not** committed here, and blocked by `.gitignore`:

- third-party papers (journal PDFs, arXiv PDFs) and scraped web pages — the
  writeups cite them precisely instead;
- compiled binaries (`checkc`) — rebuild with
  `cc -O3 -march=native -o checkc checkc.c`;
- regenerable bulk data (multi-megabyte trajectory dumps, `.npy` arrays,
  per-part sieve outputs) — every script that produced them is here.

Kept: `compute64/witnesses.jsonl.gz` (1.1 MB), the 111,705 cycle certificates
for the vertex-transitive census scan, because re-deriving it requires a 3.3 GB
external database download.
