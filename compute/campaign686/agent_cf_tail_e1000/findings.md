# Erdős 686: exact audit of the six e1000 Farey certificates

Audit date: 2026-07-12.

## Result

PASS as a generated-certificate audit.  For each odd
`k in {5,7,9,11,13,15}`, the verifier rebuilt the Farey/Stern-Brocot tree
with exact Python integers, replayed the separate semantic checker,
cross-checked every applicable continued-fraction row, rendered the Lean
source in memory, and obtained byte-for-byte identity with the current
`e1000` artifact.

This lane did not invoke Lean and did not edit any generated artifact.  Its
claim is deliberately narrower than the kernel claim: it authenticates and
reproduces the six data certificates and their boundary semantics.  The Lean
consumer and its machinery remain separate dependencies.

The reproducer and regression tests are:

- `compute/campaign686/agent_cf_tail_e1000/e1000_cert_verify.py`
- `compute/campaign686/agent_cf_tail_e1000/test_e1000_cert_verify.py`

## 1. Fixed source hashes

Generator:

`compute/erdos686_thue_gen_lean.py`

SHA-256:

`112ba748aa90e8688f7320ce3418e3b5a6430551bceaf3178e319da48209ddba`

| k | bytes | artifact SHA-256 |
|---:|---:|---|
| 5 | 474690 | `e3c69ece7adc08f321897faf01b869f5503a5eb5c126181e34f5e8d019c45a0b` |
| 7 | 311799 | `f6f62ae65dd587bf1d310639666ca71224fdfd3f77a94b531c1106ebed283100` |
| 9 | 796285 | `e9b99425f9d190053da1f5a8a107c3bb5579c9577855bdf6d3508994f2c96eb1` |
| 11 | 416396 | `7f948ee46662034e86f449a1045acea5f418df45899571ce97b38cab30ad9f74` |
| 13 | 334419 | `036e65784bd4696ff44136a1082ac260e01687911a109bad986c1ec1fe1bbf58` |
| 15 | 448143 | `f94ea813afb100ad5299fa9abbc491b808c64c4b11364241cb5378aa77e6d836` |

The six files total 2,781,732 bytes.  Hashing the ASCII manifest
`k:artifact_sha256\n` in increasing `k` order gives the artifact-set hash

`05615d9932db7c21a0954af9baf18ace8b6136d84f89f85c29a91867e2eac670`.

At audit time all six artifact paths were untracked in Git.  The hashes above
refer to the current workspace bytes, not to an already published commit.

The regenerated header/configuration metadata is:

| k | strict root pair | exact Thue window | inclusive Y band |
|---:|---|---|---|
| 5 | `1/1 < 4^(1/5) < 4/3` | `5*abs(X^5-4Y^5) <= 44Y^3` | `[665,4*10^1000]` |
| 7 | `1/1 < 4^(1/7) < 5/4` | `5*abs(X^7-4Y^7) <= 93Y^5` | `[887,5*10^1000]` |
| 9 | `1/1 < 4^(1/9) < 6/5` | `5*abs(X^9-4Y^9) <= 162Y^7` | `[1109,7*10^1000]` |
| 11 | `1/1 < 4^(1/11) < 8/7` | `abs(X^11-4Y^11) <= 50Y^9` | `[1552,8*10^1000]` |
| 13 | `1/1 < 4^(1/13) < 8/7` | `abs(X^13-4Y^13) <= 72Y^11` | `[1774,9*10^1000]` |
| 15 | `1/1 < 4^(1/15) < 11/10` | `abs(X^15-4Y^15) <= 97Y^13` | `[2217,11*10^1000]` |

## 2. Exact regenerated tree statistics

| k | nodes | splits | kills | highs | max depth | candidates | skipped | max g | sum g | max bits |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 5 | 57537 | 28768 | 28764 | 5 | 27203 | 2606 | 6 | 77 | 2612 | 16621 |
| 7 | 37857 | 18928 | 18927 | 2 | 16796 | 3601 | 9 | 36 | 3610 | 23263 |
| 9 | 96555 | 48277 | 48274 | 4 | 45246 | 4893 | 15 | 166 | 4908 | 29918 |
| 11 | 50557 | 25278 | 25273 | 6 | 21688 | 5846 | 14 | 57 | 5860 | 36573 |
| 13 | 40677 | 20338 | 20336 | 3 | 16232 | 6949 | 18 | 35 | 6967 | 43223 |
| 15 | 54483 | 27241 | 27240 | 2 | 22319 | 8112 | 19 | 55 | 8131 | 49871 |

Here `candidates` counts multiples whose centered `Y` lies in
`[Ylo,Ymax]`; `skipped` counts the exact complementary multiples among
`1 <= g <= gmax`.  Thus `candidates + skipped = sum g` in every row.
The largest integer measured by the generator has the displayed exact bit
length.

The independent tree traversal re-established all three full-binary-tree
identities for every `k`:

```text
nodes = 2*splits + 1
kills + highs = splits + 1
nodes = splits + kills + highs
```

| k | distinct mediants | applicable CF rows / total rows | private chunks |
|---:|---:|---:|---:|
| 5 | 28768 | 339 / 341 | 229 |
| 7 | 18928 | 339 / 341 | 141 |
| 9 | 48277 | 340 / 341 | 381 |
| 11 | 25278 | 339 / 341 | 183 |
| 13 | 20338 | 340 / 341 | 137 |
| 15 | 27241 | 339 / 341 | 188 |

The private chunks are contiguous `C0,...,C(m-1)`.  Every chunk identifier
occurs exactly twice, once at its declaration and once at its unique parent
reference, so chunk hoisting introduces no DAG sharing.

All 341 JSON rows were checked for the declared exact power difference,
side alternation, and adjacent determinant.  The middle column counts the
non-root rows with denominator at most `Ymax` that the cross-check requires
to occur as tree mediants.  Every required row occurred.

## 3. Exact boundary semantics

Put

```text
P = 10^1000
h = (k+1)/2
Y = n+h
Ymax = Qhi*P.
```

The banked upper confinement used by the handoff is the strict integer
inequality

```text
n+1 < Qhi*d.
```

For the target `d < P`, integrality gives `d <= P-1` and
`n+1 <= Qhi*d-1`.  Consequently

```text
Y <= Qhi*(P-1)-1+(h-1)
  = Ymax-(Qhi-h+2).
```

The certificate therefore has positive slack, not an endpoint ambiguity.

| k | h | Qlo | Qhi | Ylo = Qlo*221+h-1 | strict Y slack |
|---:|---:|---:|---:|---:|---:|
| 5 | 3 | 3 | 4 | 665 | 3 |
| 7 | 4 | 4 | 5 | 887 | 3 |
| 9 | 5 | 5 | 7 | 1109 | 4 |
| 11 | 6 | 7 | 8 | 1552 | 4 |
| 13 | 7 | 8 | 9 | 1774 | 4 |
| 15 | 8 | 10 | 11 | 2217 | 5 |

The equality boundary `d=P` is not silently covered.  Write its allowed
upper rows as

```text
n+1 = Qhi*P-r,  r >= 1.
```

Then `Y <= Ymax` holds exactly when `r >= h-1`.  The rows not supplied by
this certificate/handoff are therefore exactly:

| k | uncovered r | corresponding Y-Ymax |
|---:|---|---|
| 5 | `1` | `1` |
| 7 | `1,2` | `2,1` |
| 9 | `1,2,3` | `3,2,1` |
| 11 | `1,2,3,4` | `4,3,2,1` |
| 13 | `1,2,3,4,5` | `5,4,3,2,1` |
| 15 | `1,2,3,4,5,6` | `6,5,4,3,2,1` |

This is a quantified handoff statement only.  It does not assert that these
rows are actual solutions; it says precisely which equality-boundary rows
are not excluded by the `Y <= Ymax` certificate.

## 4. Telescope fixtures

The two known exact `d=1` telescopes were preserved rather than filtered out
of the audit:

| k | n | d | (X,Y) | gcd(X,Y) | centered residual | block residual | Ylo-Y |
|---:|---:|---:|---|---:|---:|---:|---:|
| 9 | 2 | 1 | (8,7) | 1 | 0 | 0 | 1102 |
| 15 | 4 | 1 | (13,12) | 1 | 0 | 0 | 2205 |

They are genuine identities:

```text
product(4,...,12) = 4*product(3,...,11)
product(6,...,20) = 4*product(5,...,19).
```

They do not contradict the tail certificate because both have `d=1<221`
and `Y<Ylo`.  Their exact zero residuals make them useful adversarial tests
for accidental overclaiming or a reversed inequality.

## 5. Reproduction

From the repository root:

```bash
python3 compute/campaign686/agent_cf_tail_e1000/e1000_cert_verify.py
python3 -m pytest -q \
  compute/campaign686/agent_cf_tail_e1000/test_e1000_cert_verify.py
```

The first command is intentionally compute-heavy: it reconstructs all six
1000-digit-bound trees rather than trusting Lean output or cached summaries.

## 6. Scope

What is established here:

1. the six current artifact byte strings have the fixed hashes above;
2. deterministic regeneration produces those exact byte strings;
3. every generated tree passes the generator's separate semantic replay;
4. an independent traversal reproduces the frozen tree statistics and
   structural identities;
5. the continued-fraction cross-checks, strict `d<P` handoff, equality
   residual, and telescope fixtures all pass exact arithmetic.

What is not established by this Python lane alone:

1. that the Lean consumer imports each artifact and closes its theorem;
2. that the general `fareyCheck` soundness theorem is correct independently
   of the Lean kernel;
3. any claim at `d=10^1000` or `d>10^1000`;
4. the full Erdős 686 theorem outside the six odd widths and the stated tail
   band.
