# Vela integration

This document holds the repository's Vela integration contract and the doctrine for
bounded results and native branches. It moved here from the README so that the
README can lead with the mathematics; nothing in it changed in the move. The
integration is optional and has `authority_effect: none`; ignoring these files does
not change the Lean project.

## Native Vela integration


`vela.toml` and `.vela/` expose the source-owned proof index through the draft
non-authoritative integration chain:

```text
Manifest -> Profile -> Binding -> Method
```

The integration is optional and has `authority_effect: none`; ignoring these
files does not change the Lean project. It publishes exact references and
verification inputs, never Decisions, Events, acceptance, or Standing. Vela
Core owns the shared rooted waist; the repository validator retains only
`proofs.yaml`, Lean declaration/build/axiom, external-identity, and portable
example semantics. Check both layers with:

```bash
vela integration check . --json
python3 scripts/check_vela_integration.py
```

The optional emitted verification input uses the source-owned, unrooted
`lean-proofs.verification-input.v0.1` schema. INT-00 adds no generic result
document or fifth root domain. The input binds the exact subject, Method, and
artifact closure, but contains no outcome or evidence-availability claim; an
executed check must continue through Vela's existing Verification machinery.

From a fresh clone with no project cache, the cold-consumer gate requires the
signed `vela` 0.977.2 binary from release commit
`c1a34373c2cdd937ed34fd128174a66fa12be71a`:

```bash
bash scripts/cold_consume_erdos94.sh
```

The non-destructive [branch disposition inventory](.vela/BRANCH_DISPOSITION.md)
records the repository's other native workstreams separately. Branches remain
revision locators and evidence custody boundaries; they are not Vela Attempts
or Standing state, and no merge-all or cleanup is part of this integration.

## Native branches and bounded results


`main` contains completed repository work that has passed ordinary review and
repository gates. Scientific work in progress stays on ordinary Git branches
and worktrees; it does not need to be merged for Vela to reference an exact
commit. A branch is an approach and mutable selector, not an authority object.

When an approach yields a bounded result worth carrying forward, retain the
result as a source artifact with its exact commit, files, declaration selector,
toolchain, Method, environment, rights, and provenance. That artifact may later
support an ordinary Vela Submission. Build success, actor kind, branch naming,
or merge status does not itself establish quality, acceptance, or Standing.

Generic agent sessions and checkpoints belong in source-owned tooling such as
Entire when it is available. This repository and Vela store no duplicate
session, attempt, or checkpoint database; portable provenance may link an
Entire checkpoint and the exact Git commit without copying either one.

### Bounded result summary

A reusable result summary may describe a proof, partial lemma, counterexample,
failed route, or other negative result. Keep it small and source-owned, and
include:

- the target question or declaration;
- the approach and the scope actually explored;
- assumptions and unresolved conditions;
- the resource budget and exact toolchain/environment;
- exact artifact and evidence references, including commit, path, selector,
  fixity, and the Method used;
- the scoped outcome, including partial, negative, inconclusive, or proved;
- the condition under which retrying the approach would be informative.

This summary is the reusable artifact; raw search trajectories, agent turns,
and checkpoints stay in Entire or another source-owned activity system. A
proof-state canonicalizer or similarity fingerprint must name its algorithm
and version and remain advisory. Exact identity continues to come from the Git
revision, content root, and declaration selector, so a fingerprint collision,
normalization change, or heuristic match cannot merge two results or override
their exact provenance.

The native repository is the canonical path because a real result may require
many Lean modules, generated certificates, and retained computation files.
The exact subject and its multi-file artifact closure travel together; no
single-file upload is assumed, and private or unavailable bytes are never
silently replaced. A workbench may offer simpler onboarding or parameter-family
and feasibility views, but those views derive scope from the exact target and
report bounded cost rather than inventing free-form status labels.
