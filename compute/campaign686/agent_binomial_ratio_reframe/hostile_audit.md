# Hostile audit: binomial-ratio reframe

Date: 2026-07-12

## Claim boundary

This artifact makes three claims only:

1. the binomial equation is exactly the original block equation;
2. the cited Erdős--Straus and classical Runge hypotheses do not cover the
   live uniform branch;
3. `d=k` is excluded in ordinary mathematics by Erdős--Selfridge, but is not
   kernel-banked here.

It does **not** claim Target 2 or any `d>k` subcase.

## Dependency tree and per-node verdict

| Node | Statement | Dependency | Verdict |
|---|---|---|---|
| B1 | `A(x,k)=k! * C(x+k,k)` | factorial definition | exact elementary identity |
| B2 | #686 is `A(n+d,k)=4A(n,k)` | B1 | exact equivalence |
| B3 | Erdős--Straus Theorem 2.1 needs fixed `delta>0`, `k>=delta*n` | primary paper, p. 66 | verified; hypothesis unavailable |
| B4 | Erdős--Straus Theorem 3.3 needs a prime in `[n+1,n+k]` | primary paper, pp. 69--70 | verified; premise contradicted by the banked composite-block theorem |
| B5 | At `d=k`, `A(n,2k)=(2A(n,k))^2` | block concatenation and B2 | exact algebra |
| B6 | A product of at least two consecutive positive integers is not a square | Erdős--Selfridge 1975 | valid external theorem; **not formalized here** |
| B7 | Odd-`k` infinity polynomial has one `Q`-irreducible factor | binomial irreducibility criterion | valid route obstruction, not a nonexistence theorem |
| B8 | Even-`k` infinity polynomial has two displayed factors | difference of squares | exact algebra; no quantitative exclusion follows |

No computational assertion, floating-point estimate, private lemma, or
unquantified uniformity claim is used.

## Boundary fixtures

### `d=k`

Erdős--Straus Theorem 3.3 assumes the strict inequality `n+k<m`, so it does
not cover this boundary.  Node B5 handles the algebra, and B6 supplies only an
external natural-language exclusion.  It must not be presented as a Lean
closure.

### `d>k`

Now `n+k<m`.  From the verified `9*d<n`, `m=n+d<2n`, so the bounded-ratio
part of Erdős--Straus Theorem 3.3 is available.  Its prime-in-the-lower-block
premise is not: every target lower term is composite.  Removing that premise
would be a genuinely stronger theorem, not a routine application.

### Small-`k` Pell cases

For `k=2`, `X^k-4Y^k` splits, yet multiplier equations can have Pell families.
Therefore the even factorization in B8 is recorded only as access to Runge,
never as an obstruction by itself.

### Odd telescopes `k=9,15`, `d=1`

These lie outside `d>=k`.  They also show why the one-orbit odd analysis may
not be silently upgraded to a global no-solution statement.

### Square products of disjoint blocks

The equation implies

\[
 A(n,k)A(n+d,k)=(2A(n,k))^2.
\]

For `d>k` this is only a product of two disjoint blocks, and the supplied
falsification record warns that such square products occur in the length-five
setting.  The audit therefore uses the square consequence only at `d=k`, where
the blocks concatenate into one interval and Erdős--Selfridge applies.

### Row-prefix witness `(k,n,d)=(984,3177026,4480)`

No fixed row-prefix assertion is used, so this witness neither supports nor
refutes any node above.  In particular, the audit does not infer a prime in the
lower block from row survival.

### MalekZ modular families

No finite congruence obstruction is asserted.  The Runge-factor discussion is
global algebraic geometry at infinity and does not conflict with local
solvability modulo every modulus.

## Exact remaining gap

For this route the unclosed statement is still the theorem-strength assertion

\[
\forall k,n,d\in\mathbb N,\quad
k\ge16\land d>k\land A(n+d,k)=4A(n,k)\;\Longrightarrow\;\bot.
\]

No weaker new quantified lemma was proved for `d>k`; accordingly this route is
reported as an obstruction audit rather than progress toward the target.
