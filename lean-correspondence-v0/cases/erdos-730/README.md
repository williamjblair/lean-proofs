# Case A: Erdős 730 affirmative RHS

Relation: `proposition_identity_plus_term_witness`.

Status: `verified_at_pins`, with a bounded claim. The exact set expression on
the right-hand side of `FormalConjectures.ErdosProblems.730.erdos_730` is the
proposition stated by `Palomar.Erdos730.erdos_730_infinite`; the solution is a
direct term using `Erdos730.FullDensityTheorem.pairSet_infinite`.

This packet does **not** claim that the complete Formal Conjectures theorem
`answer(sorry) ↔ S.Infinite` is definitionally equal to the Palomar challenge.
It claims only correspondence to the affirmative `S.Infinite` branch. It also
does not claim Palomar registration, independent mathematical review, or
scientific acceptance.

Witness:

```bash
lake build PalomarSolutions.Erdos730
lake env lean lean-correspondence-v0/cases/erdos-730/Witness.lean
bash scripts/check_axioms.sh
```

The closed fact inventory, dependency edges, triggers, impact closure,
uncertainties, and mutations are in `packet.json`.
