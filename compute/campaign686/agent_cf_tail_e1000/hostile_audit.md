# Hostile audit: Erdős 686 e1000 Farey artifacts

Audit date: 2026-07-12.

## 0. Claim under audit

For each `k in {5,7,9,11,13,15}`, the file

```text
compute/artifacts/erdos686_k{k}_farey_cert_e1000.lean
```

is exactly the deterministic output of
`compute/erdos686_thue_gen_lean.py` at exponent 1000, and its tree passes the
generator's exact semantic verifier.  Combined with the already-banked Lean
machinery, the intended domain is the strict tail handoff

```text
d >= 221 and d < 10^1000.
```

The audit does not promote that conditional statement into a standalone
full proof.  In particular, it does not claim the equality boundary
`d=10^1000`.

## 1. Dependency tree and verdicts

```text
N0  Six e1000 artifacts are authentic deterministic certificates       PASS
├─ N1  Generator source and artifact bytes are fixed by SHA-256         PASS
├─ N2  Per-k constants agree with the hand-written Lean interfaces      PASS
├─ N3  Exact tree construction terminates with the frozen statistics    PASS
├─ N4  Separate fareyCheck-semantics replay accepts every tree          PASS
├─ N5  Independent tree traversal reproduces structure/statistics       PASS
├─ N6  Applicable CF convergents occur as tree mediants                 PASS
├─ N7  Strict boundary d<10^1000 implies Y<=Ymax with positive slack    PASS
│  └─ N7e Equality d=10^1000 residual is excluded                       NOT CLAIMED;
│                                                                        EXACT GAP LISTED
├─ N8  Named d=1 telescopes remain exact and lie outside the tail       PASS
└─ N9  Lean consumer + general fareyCheck soundness                     EXTERNAL BANKED
```

### N1: byte provenance. Verdict: PASS

The verifier freezes the generator hash, all six artifact hashes, each byte
length, and a hash of the ordered six-hash manifest.  It renders each rebuilt
tree to UTF-8 in memory and requires literal byte equality.  No whitespace,
chunk-order, numeral, or header drift can pass this node.

Quantified coverage: 6/6 artifacts, 2,781,732/2,781,732 bytes.

### N2: configuration constants. Verdict: PASS

For every one of the six configurations the generator's
`check_lean_constants()` succeeds using integer or rational arithmetic.  The
audit separately checks

```text
Ylo = Qlo*221 + (k+1)/2 - 1.
```

There is no approximate comparison of constants: every literal is taken from
the frozen generator and the fully rendered result is hash-compared.

### N3: construction and statistics. Verdict: PASS

The exact construction produced 337,666 total nodes, comprising 168,830
splits, 168,814 kill leaves, and 22 high leaves.  It exactly refuted 32,007
in-range candidate multiples and skipped 81 out-of-range multiples.

The per-k frozen values are asserted in the verifier, and their exact sum is
recomputed by the test suite.  No floating
point, randomized order, timeout shortcut, or cached Lean result occurs.

### N4: semantic replay. Verdict: PASS

After construction, `verify` walks the finished tree with control flow
separate from `build`.  For each leaf it re-evaluates the exact high or kill
condition.  For each split it re-evaluates the multiple bound and checks all
in-range `1 <= g <= gmax` candidates against the centered equality.  All six
returned true.

The represented band is inclusive: `Ylo<=Y<=Ymax`.  A high leaf needs the
strict inequality `Ymax<b+d`; a candidate with `b+d=Ymax` is not discarded.
Candidate skipping likewise uses only `gB<Ylo` or `Ymax<gB`, so equality at
either endpoint is checked.  A node's `(gmax+1)^2` residual inequality is
strict.  The exact residual is the natural-number absolute difference, so a
zero residual cannot satisfy that node condition.  Nodes with `gmax=0` are
therefore meaningful; the k=5 root is one such node.

This is not claimed to be an independent proof of the general mathematical
machinery.  It is an independent replay of the Boolean semantics represented
by the generated tree.  The kernel-checked soundness theorem remains N9.

### N5: independent structural traversal. Verdict: PASS

A second traversal, implemented in the audit script rather than the
generator, reconstructs endpoint pairs and reproduces node counts, leaf
counts, maximum depth, candidate/skipped counts, `gmax` sum and maximum,
maximum integer bit length, and the distinct mediant set.  For every `k` it
also proves by exact counts:

```text
nodes = 2*splits+1
kills+highs = splits+1
nodes = splits+kills+highs.
```

### N6: continued-fraction cross-check. Verdict: PASS

All 341 rows in each of the six `thue_convergents_k{k}.json` artifacts are
checked for exact `p^k-4q^k`, nonzero alternating sign, and adjacent
determinant.  Every non-root row with `q<=Ymax` is required to appear in the
mediant set.  The exact applicable counts are 339, 339, 340, 339, 340, and
339 for `k=5,7,9,11,13,15`; all were present.

### N7: boundary handoff. Verdict: PASS for strict inequality only

Let `P=10^1000`, `h=(k+1)/2`, and use the banked strict upper bound
`n+1<Qhi*d`.  If `d<P`, integer arithmetic gives

```text
Y=n+h <= Qhi*(P-1)-1+h-1
        = Qhi*P-(Qhi-h+2).
```

The six exact positive slacks `Qhi-h+2` are respectively
`3,3,4,4,4,5`.  Thus every strict-domain row is below the certificate
endpoint.

At `d=P`, put `n+1=Qhi*P-r`.  The certificate covers exactly `r>=h-1`.
The exact rows left by this handoff are:

```text
k=5:  r=1
k=7:  r=1..2
k=9:  r=1..3
k=11: r=1..4
k=13: r=1..5
k=15: r=1..6.
```

They exceed `Ymax` by `h-1-r`, respectively.  This is the single quantified
boundary gap; no equality-domain conclusion is returned.

### N8: telescopes. Verdict: PASS as hostile fixtures

The audit evaluates both actual centered and original block products:

```text
k=9:  (n,d,X,Y)=(2,1,8,7),   residuals 0 and 0
k=15: (n,d,X,Y)=(4,1,13,12), residuals 0 and 0.
```

Both pairs are primitive.  They are excluded only for the stated quantified
reasons: `d=1<221`, and their `Y` values lie below `Ylo` by 1102 and 2205.
Any audit that instead reported the centered equation as globally root-free
would be false.

### N9: Lean soundness. Verdict: external banked dependency

This audit consumes no Lean output.  It therefore cannot become circular by
parsing a successful Lean trace, but it also does not by itself establish
that a Lean module imports the artifacts or that the generic checker theorem
has the intended proposition.  Those checks belong to the kernel gate in the
parent integration lane.

## 2. Adversarial attacks

| Attack | Result |
|---|---|
| Modify a numeral or whitespace in an artifact | Detected by byte length, SHA-256, and bytewise regeneration. |
| Modify the generator and regenerate matching artifacts | Detected by the frozen generator SHA-256. |
| Change tree shape while preserving a headline count | Detected by bytewise render identity and full semantic replay. |
| Hide a malformed chunk reference | Deterministic renderer identity and exactly one final public definition are checked; private chunk counts are frozen. |
| Depend on current working directory | The verifier changes only temporarily to the repository root for the generator's JSON lookup and restores the caller directory. |
| Use floating-point root approximations | Impossible in this lane; all proof checks use Python integers, with generator sanity checks using exact `Fraction` where needed. |
| Treat `<10^1000` as `<=10^1000` | Detected; the exact equality residual is listed for every `k`. |
| Accidentally reject the known d=1 roots | Detected by two exact zero-residual telescope fixtures. |
| Count all CF rows as mediants, including root endpoints | Avoided; applicable non-root counts are reported separately from the 341 checked rows. |
| Trust generator construction without replay | Avoided by `verify` plus the independently written structural traversal. |
| Infer the full Erdős 686 theorem from these data | Rejected as outside N0; N9 and the other widths/bands remain separate dependencies. |

## 3. Shared-code caveat

Deterministic regeneration necessarily reuses the generator that originally
emitted the artifacts.  A defect common to `build` and `render` could
therefore reproduce itself.  The audit limits this risk in three distinct
ways:

1. `verify` replays the finished tree through separate control flow;
2. the audit's own traversal independently reconstructs endpoints and all
   frozen statistics;
3. the intended final consumer is the Lean kernel's generic soundness theorem,
   not this Python script.

Accordingly, the valid conclusion is artifact authenticity plus exact
semantic replay, not an independent replacement for the Lean proof.

The artifact files themselves are raw fragments, not theorem modules.  Their
headers are comments, followed by private chunks and one public `FareyTree`
definition.  The comments are not machine-binding; a separate Lean checker
must instantiate matching constants.  That matching and the import surface
belong to N9, not to the artifact hash audit.  Likewise, the JSON convergent
comparison is finite auxiliary hygiene, not a completeness theorem up to the
1000-digit `Ymax`.

## 4. Reproduction verdict

The exact regression suite passes only if all six artifacts, the generator,
the tree statistics, the continued-fraction cross-checks, the strict boundary
semantics, and both telescope fixtures agree simultaneously.  The generated
artifacts and shared Lean modules are read-only inputs to this lane.
