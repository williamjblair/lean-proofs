# Hostile audit: unconditional k=28 row

## Exact target

For all natural `n,d`, prove

`28 <= d -> blockProduct 28 (n+d) != 4 * blockProduct 28 n`.

No smoothness premise, asymptotic qualifier, or unproved number-theoretic
lemma appears in the target.

## Dependency tree and per-node verdict

1. Centering identity: `S(2x+29)=2^28 blockProduct(28,x)`.
   - Verdict: kernel algebra (`ring`) plus the already banked centered-product
     identity.
2. Square-root identity: `T^2=S+D` with `deg T=14`, `deg D=12`.
   - Verdict: reconstructed independently over the integers; kernel `ring`.
3. Fixed divisor: `50176|T(2a+1)`.
   - Verdict: `1024` divides by an explicit degree-14 integer quotient; `49`
     divides by an exhaustive ordinary-`decide` `ZMod 49` table; coprimality is
     the explicit Bezout identity `-10*1024+209*49=1`.
4. Exact ratio window.
   - Verdict: existing kernel theorem plus the exact power comparisons
     `4*19^28<20^28` and `83^28<4*79^28`, both discharged by normalization.
5. Finite strip `28<=d<=383`.
   - Verdict: all 64,258 ratio-window points are checked exactly.  The Lean
     certificate uses 45 ordinary-`decide` shards with explicit interval
     hypotheses; no point outside the quantified strip is used in the proof.
6. Large-gap lower trap.
   - Verdict: after `v=14567+a`, `w=15335+a+b`, all 120 coefficients of
     `D(w)+B*T(w)+2B*T(v)-4D(v)` are positive for the least integer
     `B=52682724273`; the binding coefficient is the constant term.
7. Large-gap upper sign.
   - Verdict: `10w<=11v`; the exact conservative majorant for
     `10^12(D(w)-4D(v))` has 13 negative shifted coefficients at `v=14567+a`.
8. Strict quotient interval.
   - Verdict: from `-B<m<0` and `m=50176q`, integer arithmetic gives exactly
     `1<=t<=1049958`; `-B` and `0` are not admitted.
9. Prime-field necessity.
   - Verdict: for each listed prime, reducing the two polynomial equalities
     modulo `p` forces the generated bit-mask condition.  Each allowed mask is
     checked over every `w,v : ZMod p` by ordinary kernel `decide`.
10. Global quotient cover.
    - Verdict: exact survivor counts end at zero.  The modulus-29 prefilter has
      exactly the four classes `5,14,15,24`; the remaining scan is split into
      18 ordinary-`decide` blocks and lifted by a proved recursive scan lemma.
      The Lean cover uses only primes at most 353 (51 field shards); the shorter
      11-prime exploratory cover is reproduced separately and is not silently
      substituted for the kernel tables.
11. Assembly.
    - Verdict: the conditional core consumes only nodes 1-8 and two explicit
      certificate interfaces; the final module supplies nodes 9-10 and proves
      the unconditional theorem.

## Boundary audit

- `d=1`: telescoping would require `n+29=4(n+1)`, hence `3n=25`; impossible.
- `d=27`: outside theorem scope; its 47 ratio-strip points were replayed and
  contain no equality.
- `d=28`: included in finite shard 0, with all 47 ratio-window candidates.
- `d=383`: included in finite shard 44, with all 314 candidates.
- `d=384`: excluded from the finite strip and included by the large-gap branch;
  here `v>=14567` and `w-v>=768` hold at equality at the derived lower base.
- trap endpoint `m=-52682724273`: excluded by the strict lower inequality.
- trap endpoint `m=0`: excluded by the strict upper inequality.
- quotient endpoints `t=1` and `t=1049958`: both included in the cover.
- primes `2` and `7`: deliberately excluded because they divide 50,176; no
  modular inverse is taken there.
- local survivor semantics: every survivor satisfies the current local mask;
  every removed integer fails it, and every allowed `m mod p` stores a concrete
  `(w,v)` witness.

## Falsification and prohibited-token audit

- Prompt fixture `(k,n,d)=(984,3177026,4480)`: outside the fixed row `k=28`.
  No fixed-prefix or universal row implication is invoked, so this witness does
  not satisfy or contradict any premise of the certificate.
- Prompt `n=48502` survivor clusters: likewise no census-prefix claim is used.
  The theorem quantifies the full k=28 equation and derives its own exact
  centered identity before applying any field condition.
- Prompt `d=1` telescopes at `k=9,15`: those rows are outside this theorem.  The
  k=28 telescope was checked separately (`3n=25`), and the theorem itself only
  claims `d>=28`.
- MalekZ admissible congruence family for `(N,k)=(4,5)`: the field intersection
  here is not asserted as a universal congruence obstruction.  It is applied
  only after the k=28 square-root identity, the explicit large-gap threshold,
  the strict archimedean interval, and the fixed divisor reduce `m` to the
  finite set `-50176t`, `1<=t<=1049958`.  Thus the route does not make the
  falsified claim that some modulus alone obstructs every related equation.
- The fixed divisor is not inferred from a sample alone: the Lean proof gives
  an explicit 2-primary quotient and a complete `ZMod 49` proof.
- The finite strip uses exact integer polynomial values, not floating roots or
  rounded logarithms.
- The shifted trap uses the least integer constant certified coefficientwise;
  “sufficiently large” has been replaced by the explicit threshold `d>=384`.
- The modular cover is a necessary-condition intersection, not a claim that
  locally allowed residues lift globally.
- Source scan finds no `native_decide`, `sorry`, `admit`, or declared axiom in
  the k=28 graph.  All finite computations use ordinary `by decide`.
