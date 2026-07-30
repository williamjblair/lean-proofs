# Submission protocol for a solved Erdős problem

Applies to any target in `docs/plans/erdos-solve-campaign.md` that reaches a
complete resolution. Nothing is submitted without Will's explicit approval —
posting to erdosproblems.com is outward-facing publication.

## Gate 1 — internal verification (before anything leaves the repo)

1. **Independent adversarial review.** At least two skeptic passes whose brief
   is to REFUTE, not to confirm: one line-by-line on the argument, one
   attacking the boundary/uniformity/quantifier structure. A proof survives
   only if both fail to break it.
2. **Numerical sanity.** Every asymptotic claim spot-checked computationally
   in the regime where checking is possible; every explicit constant
   recomputed with exact (rational) arithmetic, independently coded.
3. **Freshness re-check, day-of.** Problem page, `/forum/discuss/N`,
   `/forum/thread/N/proof-claims`, arXiv listing for the month, and
   `teorth/erdosproblems` `data/problems.yaml` status. A problem can flip
   in days — during this campaign #1139 acquired an unvetted full-proof
   claim between two triage passes hours apart.
4. **Literature attribution.** Anything assembled from existing theorems is
   labelled as assembly with precise citations (author, title, venue,
   arXiv ID, theorem number). Never present a citation-closable result as
   new mathematics.

## Gate 2 — artifact

- `proof_<N>.md` in `compute<N>/`: complete, self-contained, referee-standard.
  Every lemma either proved in full or cited precisely. Constants numbered.
- Validation code, runnable by a skeptic, with its exact output committed.
- An honest status label at the top: SOLVED / SOLVED-mod-verification /
  GAP-REMAINS (with the gap stated precisely).
- Lean formalization where the mathematics permits it at session scale.
  Realistically: constructive/finite arguments (e.g. #1212) are formalizable;
  sieve-theoretic and Rankin-covering arguments (#1004, #1139) are not —
  say so rather than shipping a `sorry`-laden skeleton.

## Gate 3 — submission (Will's call, never automatic)

- erdosproblems.com: "Submit your own proof claim" on the problem's
  `/forum/thread/N/proof-claims` page, with a link to the writeup.
  Disclose AI assistance explicitly — the site's culture currently absorbs
  AI-assisted work but penalizes undisclosed or sloppy claims (see the
  #647 refutation and the #848 thread's norms).
- Comment on the problem page summarizing the result and linking artifacts.
- If the result is an improvement rather than a resolution (e.g. a threshold
  reduction on #848, or the raised search bound on #64), submit it as a
  comment/partial, not a proof claim.
- Formal Conjectures PR only after the Lean proof builds under the repo gates
  (`scripts/check_axioms.sh`, `scripts/check_manifest.sh`).

## Standing note

The campaign's value does not depend on a full solve landing. Verified
frontier extensions (#64: counterexample bound 17 → 19, vertex-transitive
census cleared to order 1280) and verified lemma reviews (#64's 2/3 density
lemma) are publishable contributions in their own right, and are submitted
as such.
