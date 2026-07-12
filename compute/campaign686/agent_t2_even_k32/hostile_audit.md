# Hostile audit: unconditional k=32 row

## Exact target

For all naturals `n,d`, prove

`32 <= d -> blockProduct 32 (n+d) != 4*blockProduct 32 n`.

This is a complete row theorem.  It has no smoothness premise, no unquantified
uniformity phrase, and no private mathematical lemma outside its transitive
Lean import graph.

## Dependency tree and per-node verdict

1. **Centered identity.**
   `S(2n+33)=2^32*blockProduct(32,n)`.
   Verdict: exact polynomial expansion and the existing generic centered
   product theorem; kernel tactics only.
2. **Square-root identity.**
   `T^2=S+D`, with degrees `16,32,14` for `T,S,D`.
   Verdict: independently reconstructed over the integers and proved by
   kernel `ring`.
3. **Universal fixed divisor.**
   `2^30*3 | T(2a+1)` for every integer `a`.
   Verdict: the `2^30` proof factors `T` into `2^24*H` in each parity mode and
   checks `64|H` over all residues of `ZMod 64`; the factor 3 is checked over
   `ZMod 3`; coprimality is explicit.  The sample gcd in the external verifier
   is not used as the universal proof.
4. **Exact ratio window.**
   Verdict: the three integer comparisons
   `4*22^32<23^32`, `49^32<4*47^32`, and
   `4*45^32<47^32` are normalized in Lean.  No floating logarithm is used.
5. **Finite strip.**
   `32<=d<=127`.
   Verdict: exact arithmetic checks all 14,352 ratio-window candidates.  Lean
   uses 12 exhaustive ordinary-`decide` shards over a slightly larger
   rectangle of `96*222=21,312` points, then restricts it with the proved ratio
   inequalities.  Thus every necessary candidate is included.
6. **Large-gap base.**
   `d>=128` implies `v>=5603`, `w>=v+256`, and `22w<=23v`.
   Verdict: explicit integer arithmetic from the ratio brackets; the split
   boundary is included.
7. **Lower archimedean trap.**
   Verdict: all 153 coefficients of the shifted polynomial are strictly
   positive for the least integer `B=1388955148309984`.  The binding constant
   coefficient is recorded exactly; no phrase such as "sufficiently large"
   remains.
8. **Upper archimedean sign.**
   Verdict: the `22w<=23v` termwise majorant has 15 negative shifted terms,
   with exact minimum after negation
   `1100088810266698413426976585709661840211968`.  Combined with positivity
   of `T(w)+2T(v)`, it proves `m<0`.
9. **Strict finite quotient.**
   `-B<m<0` and `3221225472|m` imply exactly
   `m=-3221225472*t`, `1<=t<=431188`.
   Verdict: kernel integer arithmetic; neither strict endpoint is rounded in.
10. **Prime-field necessity.**
    Verdict: for each of 17 primes, all field pairs satisfying
    `S(w)=4S(v)` are checked and the associated `T(w)-2T(v)` mask is proved by
    ordinary `decide`.  The theorem only uses these masks as necessary
    conditions.
11. **Global quotient cover.**
    Verdict: survivor counts end at zero.  The seven modulus-17 classes and
    all `q<25365` are proved by 13 ordinary-kernel scan shards and a generic
    recursive scan lemma.
12. **Assembly.**
    Verdict: the conditional core consumes nodes 1-9 plus explicit field and
    cover interfaces.  The public module proves both interfaces from nodes
    10-11 and yields the exact unconditional target.

## Boundary audit

- `d=1`: telescoping would require `n+33=4(n+1)`, hence `3n=29`; there is no
  natural solution.  This lies outside the theorem but is replayed because
  the portfolio has genuine `d=1` telescope fixtures in other rows.
- `d=31`: outside the target; its 77 exact ratio-window candidates were
  checked and contain no equality.
- `d=32`: inside finite-strip shard 0; all 78 ratio candidates are included.
- `d=127`: inside finite-strip shard 11; all 221 candidates are included.
- `d=128`: excluded from the finite strip and included by the large-gap
  branch, with `w-v>=256` at equality.
- `v=5603` and `w=5859`: included by non-strict base hypotheses in both
  shifted coefficient certificates.
- trap endpoint `m=-1388955148309984`: excluded by the strict lower bound.
- trap endpoint `m=0`: excluded by the strict upper bound.
- quotient endpoints `t=1` and `t=431188`: both included in the cover.
- primes `2` and `3`: not used in the field cover because they divide the
  fixed divisor.  Their complete contribution is handled in the universal
  fixed-divisor proof; no inverse modulo either prime is taken.
- the four last external survivors are eliminated at `p=409`; the final
  survivor count is exactly zero.

## Audit against the portfolio falsification record

- **Pure congruence is not claimed.**  The field intersection is applied only
  after the exact equation, the row-specific square identity, the explicit
  split `d>=128`, the strict archimedean trap, and the universal fixed divisor
  reduce the problem to 431,188 integers.  It is a finite certificate, not a
  universal congruence obstruction.
- **MalekZ `(N,k)=(4,5)` local families survive.**  They concern another row
  and do not refute a row-32 finite cover conditioned on the square-root trap.
- **The fixed-prefix witness `(k,n,d)=(984,3177026,4480)` survives.**  This
  proof never infers row 32 from a prefix of rows at `k=984`; it proves the
  complete `k=32` equation directly.
- **The `n=48502` and `n=3177026` census clusters survive.**  No smoothness,
  row-prefix, or census claim appears.  If any `n` occurred in the exact row-32
  equation with `d>=32`, it would be covered directly by the quantified Lean
  theorem.
- **Odd-row `d=1` telescopes survive.**  The theorem is only row 32 with
  `d>=32`; its own telescope boundary is separately nonintegral (`3n=29`).
- **Generic irrationality, Baker-Feldman, and Siegel finiteness are unused.**
  Every bound here is an explicit integer inequality or finite kernel
  certificate.
- **Smoothness alone is not invoked.**  The row closure comes from the full
  equation and its centered polynomial identity.

## Mechanical audit

- `lake build ErdosProblems.Erdos686EvenK32`: success, 8,374 jobs;
- theorem axioms: exactly `[propext, Classical.choice, Quot.sound]`;
- focused pytest: `6 passed`;
- verifier payload SHA-256:
  `b257c682bbbe8444b2b215372f5ea5104a2397b0228a1406c688ceb572573af7`;
- public source reachability: `113/113`, no inert Lean source;
- ordinary `by decide`: 91 occurrences;
- source scan: no `native_decide`, `sorry`, `admit`, or declared `axiom`;
- public `.olean`: present after the successful target build;
- trailing-whitespace and final-newline scan on every lane file: clean;
- shared import/manifest/attestation/final-residual files: untouched.
