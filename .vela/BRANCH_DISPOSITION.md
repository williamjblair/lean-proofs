# Native branch disposition inventory

Observed 2026-08-13 against the curated `main` commit
`a8c2872a27cf8d11cf6744ca4a2c5b49ace5fea0`. Counts below are
`behind main / ahead of main`, as reported by `git rev-list --left-right
--count main...<ref>`. This is a non-destructive inventory, not an instruction
to merge, prune, delete, or rewrite any ref.

A Git branch is a native workstream and revision locator. It is not a Vela
Attempt, Decision, or Standing state. A Workspace Attempt, Session, or Research
Block may reference an exact branch commit. Native merge is publication into
the curated corpus, not acceptance or Standing. Only reviewed proof source and
its provenance should be promoted, narrowly. Failed, retracted, conditional,
and exploratory work remains useful exact evidence at its original commit.

## Workspace reference mapping

The portable mapping uses existing Exact Reference and provenance concepts; it
does not add a Branch object to Vela Core:

| Native fact | Portable representation | Workspace use |
| --- | --- | --- |
| Repository identity | Canonical Git remote identity | Identify the source owner without transferring authority. |
| Workstream state | Exact commit revision plus Git tree fixity; selected files additionally use SHA-256 fixity | An Attempt, Session, or Research Block may cite the immutable revision as an Entity. |
| Branch name | Optional mutable selector and provenance label only | Locate continuing native work; never present the name as immutable identity. |
| Performer or tool action | Separate Agent, Activity, Entity, and Role attribution | Record who or what produced, reviewed, or checked the cited revision without treating actor kind as evidence quality. |
| Native merge | New exact commit reference in the curated corpus | Record publication lineage; do not translate merge, review, or CI into a Vela Decision or Standing. |

The Workspace reference is therefore a link to source-owned evidence, not a
copy of the branch, a new protocol object, or an authority-bearing admission.

## Curated and integration refs

| Ref | Exact tip | Behind / ahead | Disposition |
| --- | --- | ---: | --- |
| `main`, `origin/main`, `origin/HEAD` | `a8c2872a27cf8d11cf6744ca4a2c5b49ace5fea0` | 0 / 0 | Curated published proof corpus. |
| `codex/native-repository-integration` | `a8c2872a27cf8d11cf6744ca4a2c5b49ace5fea0` at inventory time | 0 / 0 | Source-owned integration workstream; publish its contract separately from proof-status judgments. |

## Diverged source workstreams

| Ref | Exact tip | Behind / ahead | Disposition |
| --- | --- | ---: | --- |
| `erdos-campaign-2026-07-30`, `origin/erdos-campaign-2026-07-30` | `94fde841ea6ad90437bd66a91953bfeba13dba0f` | 9 / 53 | Long-lived multi-problem campaign containing corrections and retractions. Preserve and reference exactly; **do not merge all**. Review and promote individual proof/provenance packets only. Its breadth makes it a candidate for a separate source-owned campaign repository if it remains active. |
| `origin/codex/erdos23-two-defect-final` | `2d98b64d6a9c26593609260868f6731831bbc850` | 59 / 15 | Problem-specific proof workstream. Preserve exact evidence; review any narrow promotion independently. |
| `origin/codex/erdos686-corrected-bounded-osculation` | `dcd582945fa9fff0197484c1b0785b1f3ca2b668` | 37 / 12 | Corrective proof workstream. Preserve exact lineage; do not replace it with a green-build summary. |
| `origin/codex/erdos686-corrected-package-reconcile` | `800451d2c2dd6624508c0b8525b33a843e30445c` | 36 / 14 | Corrective/reconciliation workstream. Preserve exact lineage and review any promoted files with their provenance. |
| `origin/verify/erdos686-919-checkpoint-20260717` | `6f65676f2a1cdb7c9970be72c7c769239da392a3` | 37 / 2 | Verification checkpoint. Tag or archive only after its evidence is rooted and reference scans are complete. A successful check is not Standing. |
| `reorg-per-problem`, `origin/reorg-per-problem` | `3fb09baea15639565e8e196d4f304c40e4f85bd6` | 22 / 4 | Repository-organization experiment. Keep source-owned and separate from scientific status; review before any selective adoption. |

## Merged-ancestor refs

These tips contain no commit absent from current `main`. They are eligible for
later deletion only after citation, content-root, and exact-reference scans.
This tranche does not perform those scans or delete them.

| Ref | Exact tip | Behind / ahead |
| --- | --- | ---: |
| `add-starfleet-verified`, `origin/add-starfleet-verified` | `48c54b6e5880fad34a74507611d0701915f049bc` | 16 / 0 |
| `solved-only` | `b2babbfc29e505393c7e42453ef94a3f4471e79a` | 20 / 0 |
| `origin/checkpoint/erdos686-919-green-20260717` | `e2cdf712a0a2168f60021b77539c3f0027fbe4a1` | 37 / 0 |
| `origin/codex/erdos686-corrected-package-final` | `aff1d30b3b1c6bd705810fa4d588b03940fb31df` | 35 / 0 |
| `origin/codex/erdos686-proof-wip` | `cc075f3ce488016208d842b111ed45a3a27bc250` | 285 / 0 |
| `origin/codex/erdos727-full-solve` | `0c9f62aefd700af15a84ceca870abf44302ed07d` | 307 / 0 |
| `origin/erdos699/full-solve` | `f2e3db95b3ff0d36441646bb14606132e504f0c3` | 146 / 0 |

## Stash and linked-worktree custody

- `refs/stash` is
  `0f33b0e35182f960c5820da3af2c30c65ffb62d4`, based on
  `4f915a323443bfb1709a6805a013812016dca88a` (8 commits behind current
  `main`). Its index parent has no tracked delta; its untracked parent
  `85006fc4d9018fa353f8c280a8de8ea1be5157ea` retains 405 source, research,
  computation, and reference files. Keep it as exact WIP evidence; do not drop
  or apply it wholesale.
- The primary worktree is this integration branch.
- Three registered temporary worktrees point at
  `94fde841ea6ad90437bd66a91953bfeba13dba0f`: one names
  `erdos-campaign-2026-07-30`, and two are detached. Their private temporary
  paths are deliberately omitted from this public inventory. Git reports all
  three registrations as prunable because their directories are absent. Do
  not prune the registrations until exact citations and rooted evidence have
  been checked.

This inventory is informational and does not participate in the selected
Erdos 154 cold-consumer check.
