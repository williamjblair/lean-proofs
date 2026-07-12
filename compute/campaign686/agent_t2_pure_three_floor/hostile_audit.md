# Hostile audit: pure three-owner floor elimination

Verdict: **PASS as a proper algebraic reduction; FAIL as closure of the pure
three-owner subcase or Target 2.**

## Dependency tree

```text
exact block equation
|
+- pure center factorization S=PQR and three distinct reflected owners
+- reflected square lift
|  +- even: P^2 | 5S-3(h-2i)
|  `- odd:  P^2 | 3S-5(h-2i)
+- k>=220 product window
|  +- even: t=abc=15S+r, 0<r<S
|  `- odd:  t=abc= 3S+r, 0<r<S
`- reflected third composition at each owner
   +- even: P^2 | 9Ct-108D Delta+180E Delta S
   `- odd:  P^2 | 5Ct+100D Delta-60E Delta S
      |
      `- pure-three floor elimination (this package)
         +- even: P^2 | 5Cr+45Ce+60 Delta(Ee-D)
         `- odd:  P^2 | 3Cr+15Ce+60 Delta(D-Ee)
```

The new Lean module proves only the last two arrows.  It does not construct
the component factorization, derive the floor, derive the square lift, or
recover the exact equation from necessary congruences.

## Per-node verdicts

| Node | Verdict | Reason |
|---|---|---|
| Even floor elimination | PASS | Direct integer divisibility algebra; the cancellation of `9` is guarded by `IsCoprime (P^2) 9`. |
| Odd floor elimination | PASS | Direct integer divisibility algebra; the cancellation of `5` is guarded by `IsCoprime (P^2) 5`. |
| Replacement of `S` | PASS | Uses the displayed square divisibility after multiplying, never an unrecorded modular inverse. |
| Automatic target coprimality | PASS at application boundary | A component supported on prime bases above `k>=220` is coprime to `3`, `5`, and `9`; the generic theorem intentionally asks for this explicitly. |
| Finite square scan | PASS as exact diagnostic | Every enumerated integer candidate is checked exactly; no finite result is promoted to a universal theorem. |
| Floor-plus-third CRT closure | FAIL | Two endpoint-window fixtures satisfy all three original third congruences but fail all three square premises and the equation. |
| Simultaneous square-plus-third system | OPEN | The finite rows are rejected, but no uniform resultant or lattice bound is proved. |
| Pure three-owner subcase | OPEN | The exact simultaneous system remains. |
| Target 2 | OPEN | Small-prime loss, more than three owners, and `16<=k<220` are outside this package in addition to the open pure subcase. |

## Quantified language

- "Pure" means exactly `S=PQR` with no residual loss factor; it does not mean
  that `P,Q,R` are prime.  The Lean theorems allow arbitrary integer
  components.  Only the finite diagnostic specializes to primes.
- "Large support" means every prime base is greater than `k`; the package
  never replaces this by the weaker numerical statement `P>k` in a universal
  theorem.
- "Finite scan" means exactly the `17,296` prime triples for `k=220` and the
  `16,215` prime triples for `k=223` with all components below `501`, and every
  owner/residue representative satisfying the two named weak inequalities.
- "Translated families" means exactly `981` displayed rows for
  `220<=k<=240`; this replay is not an exhaustive scan of all component
  triples at those 21 values of `k`.
- "Endpoint fixtures" means the two exact tuples in `findings.md`, each
  checked by integer exponentiation against both endpoint inequalities.

## Boundary and falsification audit

1. **Prime powers versus primes.**  The formal elimination is stated for an
   arbitrary component `P`.  The verifier's use of primes is labeled finite
   evidence and cannot exclude a prime-power component.
2. **Component order.**  Components are ordered and zipped with owners.  The
   scan starts with the largest component only as an enumeration optimization;
   it retains its owner and checks the other two ordered assignments exactly.
3. **Coincident owners.**  Rejected explicitly in the pure three-owner scan.
   The formal component theorem itself is local and permits any integer
   `delta`, including zero.
4. **Signs.**  `D`, `E`, and `Delta` are signed integers.  The verifier builds
   them by signed polynomial multiplication and reduces only after the exact
   formula is formed.
5. **Factor two.**  The Lean theorem assumes the already-cleared numerator
   divisibility.  It does not silently divide by two.  Target components have
   odd prime support because their bases exceed `k>=220`.
6. **Factors three, five, and nine.**  No cancellation is hidden.  Both
   coprimality conditions are theorem hypotheses.
7. **Floor strength.**  The theorem assumes the exact equalities
   `t=15S+r` or `t=3S+r`; it does not infer them from decimal approximations.
8. **Square/floor fixtures.**  The 73 exhaustive base-grid rows and 981
   translated rows fail the endpoint equation data and every third component.
   They are not counterexamples to the simultaneous equation system.
9. **Third-only fixtures.**  These satisfy the exact endpoint window, pinned
   floor, and all three original third congruences, but all square residues are
   nonzero.  They falsify only a shortcut that drops the square layer.
10. **Affine-only fixtures.**  These satisfy the two newly eliminated affine
    systems but fail the square and original third layers.  They show that the
    final affine forms must not be treated as sufficient conditions.
11. **Full equation.**  Every named fixture has its full block-product error
    reproduced exactly and nonzero.

## Exact remaining lemma

No equivalent-strength lemma is claimed as progress.  The precise remaining
subcase is:

> For every natural `k>=220` and exact solution with `k<=d`, there do not
> exist exactly three pairwise-coprime complete reflection-center components
> `P,Q,R`, all supported on prime bases above `k`, assigned to three distinct
> reflected owners, with `S=PQR`, the three square decompositions, and the
> resulting exact cofactor product `t=abc`.

At the current interface this requires a new proof that the three square
congruences, exact product identity, pinned remainder interval, and three
affine square-modulus congruences have no simultaneous target-row solution.
This statement is a proper subcase of Target 2, but remains unproved.

## Kernel gate and exact reproduction

The two public theorem surfaces print exactly
`[propext, Classical.choice, Quot.sound]`.  No `native_decide` occurs.

```text
4ed1e5fbbd76952c1b34fcda9afd66f90f4bcb37f9a381f776a84162657fbcc0  ErdosProblems/Erdos686PureThreeOwnerFloor.lean
88c321b1c42ab0d8504cea556e06614dcb85b68c6280733826391eac361097c9  compute/campaign686/agent_t2_pure_three_floor/pure_three_floor_verify.py
1128f5553ad186a6b2644db144a03573a71b5a813a6483dbc18881a2c52573f9  compute/campaign686/agent_t2_pure_three_floor/test_pure_three_floor_verify.py
14add42829154821e59e07c76a15f52897c1ca4365f57241f8c0ffe18bbfdd00  compute/campaign686/agent_t2_pure_three_floor/findings.md
```

Reproduction commands and observed results:

```text
lake env lean ErdosProblems/Erdos686PureThreeOwnerFloor.lean
  PASS; both public theorems use only the permitted kernel gate

PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q \
  compute/campaign686/agent_t2_pure_three_floor
  4 passed
```
