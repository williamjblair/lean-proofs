# Hostile audit: exact-window third-obstruction nonvanishing

Verdict: **PASS as a proper restriction; FAIL as a Target 1 closure.**

## Dependency tree

```text
exactly-three cyclic nonvanishing                              PASS
|- exact block equation -> ratio_window_four_nat              PASS (banked)
|- 4*B^k < A^k for six rational brackets                      PASS (Lean/exact)
|- B*d < (A-B)*(n+k)                                          PASS (Lean)
|- target offset absorption                                   PASS (Lean/exact)
|- L_k*d <= localResidual n d i                               PASS (Lean)
|- d=gPQR and three residual decompositions
|  `- L_k^3*g^2*d <= abc                                      PASS (Lean)
|- 6,210 ordered coefficient inequalities                     PASS (decide/Python)
|- absolute-value correction domination                       PASS (Lean)
`- cyclic relabeling                                           PASS (Lean)

complete-grid third nonvanishing                              PASS
|- exact full-grid gap and residual reconstruction            PASS (banked)
|- card in [4,15], rows in [1,15]                             PASS (banked)
|- product cofactor lower bound                               PASS (banked)
|- explicit coefficient bound linear in d                    PASS (Lean)
`- every full-grid third obstruction nonzero                  PASS (Lean)

derive d < 10^120 from simultaneous nonzero obstructions      OPEN
```

## Quantified inequalities

No phrase such as “close to”, “dominates”, or “uniformly” is used without a
displayed bound.  The two exact domination interfaces are:

```text
180 |E delta| < 9 |C| L^3,
108 |D delta| < 10^120(9|C|L^3-180|E delta|),
```

for exactly three components, and

```text
K_3*g^2*d < product_s a_s,
|(12D+20Ed)(-3)^r Delta| < K_3*d,
K_3 = 56*10^12*3^14*15^14+1,
```

for the complete owner family.

## Adversarial fixtures

| Fixture | Verdict | Reason |
|---|---|---|
| `k=9`, `P_9(8)=4P_9(7)`, `d=1` | PASS | Exact equation reproduced; target cutoff is false. |
| `k=15` telescope, `d=1` | PASS | Exact equation reproduced; target cutoff is false. |
| 121-digit three-owner Hensel/CRT family | PASS | Local/composed congruences hold, but equation and upper residual window fail. The theorem never claims a congruence-only obstruction. |
| 130-digit four-owner CRT family | PASS | Local/composed congruences hold, but equation and upper window fail; it is outside the exactly-three wrapper. |
| Empty/unit owner bucket | PASS | The complete-grid proof permits `P_i=1`; nonvanishing comes from the cofactor product, not nontriviality of every bucket. |
| Bases `2` and `3` | PASS | No prime or factor of `3` is cancelled. |
| Center and reflected owners | PASS | All target indices are scanned; structural `C_i != 0` holds at centers. |

## Overclaim traps

1. `T_i != 0` does not bound `P_i` from `P_i^2 | T_i`; `T_i` grows with
   the cofactor product and with `d`.
2. All 1,035 exact sign cells are mixed.  The primitive lattice therefore
   permits large cancellation after the new theorem.
3. The two-small weighted proxy lemma is not proved.  It remains a sufficient
   target-scale landing only after restricting to the new all-nonzero branch.
4. The complete-grid result is not a smaller owner factorization: it retains
   every unit and nonunit bucket and the original bounded loss.

Accordingly, this checkpoint may update the frontier from “zero and nonzero
third branches” to “joint all-nonzero third branch”, but it cannot mark
`OddThueTailHypothesis`, Target 1, or Erdős #686 complete.
