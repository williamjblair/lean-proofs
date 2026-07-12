# Erdős 686 row k=32: exact unconditional closure

## Outcome

The row is closed without a smoothness or asymptotic premise.  The public Lean
theorem is

```lean
Erdos686.Erdos686Variant.no_gap_solution_four_even_thirtytwo
  {n d : ℕ} (hd : 32 ≤ d) :
  blockProduct 32 (n + d) ≠ 4 * blockProduct 32 n
```

`lake build ErdosProblems.Erdos686EvenK32` completed all 8,374 jobs and
printed exactly the permitted axiom set
`[propext, Classical.choice, Quot.sound]`.  The proof uses ordinary kernel
`decide`; it contains no `native_decide`.

The independent exact verifier reconstructs its data from integer arithmetic
and reports payload SHA-256
`b257c682bbbe8444b2b215372f5ea5104a2397b0228a1406c688ceb572573af7`.

## Centered square-root trap

Let

`S(W) = product_{j=1}^{16} (W^2-(2j-1)^2)`.

The reconstructed integral polynomial `T` has degree 16 and satisfies
`T(W)^2=S(W)+D(W)`, where `D` has degree 14.  The centered bridge is

`S(2n+33) = 2^32 * blockProduct(32,n)`.

At every odd integer center,

`3221225472 = 2^30 * 3 | T(W)`.

Lean proves the `2^30` factor by two parity modes for an explicit degree-eight
polynomial modulo 64, proves the factor 3 over `ZMod 3`, and combines the
coprime factors with an explicit Bezout certificate.

The exact ratio brackets are

- `4*22^32 < 23^32`;
- `49^32 < 4*47^32`;
- `4*45^32 < 47^32`.

For `32 <= d <= 127`, the first two brackets leave exactly 14,352 `(d,n)`
pairs.  Exact integer evaluation gives no zero of `S(w)-4S(v)`.  The row
`d=32` contributes 78 candidates and `d=127` contributes 221.  The smallest
absolute nonzero error occurs at `(d,n)=(33,729)` and is

`67054135290468716213543058140175190182924460322589595096735493127091363202000814363031633920000000`,

with negative sign.

For `d>=128`, set `v=2n+33`, `w=v+2d`, and
`m=T(w)-2T(v)`.  The ratio bounds imply

`v>=5603`, `w>=v+256`, and `22w<=23v`.

The least coefficientwise lower-trap constant is

`B = 1388955148309984`.

After substituting `v=5603+a`, `w=5859+a+b`, all 153 coefficients of

`D(w)+B*T(w)+2B*T(v)-4D(v)`

are positive; the minimum coefficient is exactly `B`, the binding degree is
`a^0*b^0`, and the constant coefficient is

`3788786803183719109480074442313100090321007920842572226887680`.

The conservative upper polynomial obtained from `22w<=23v` has 15 strictly
negative shifted terms.  The least positive coefficient after negation is

`1100088810266698413426976585709661840211968`.

Consequently

`-1388955148309984 < m < 0`.

Since `3221225472|m`, there is a natural `t` with

`m=-3221225472*t` and `1<=t<=431188`.

Both inequalities are strict; neither `m=-B` nor `m=0` enters the finite
cover.

## Exact finite-field cover

For every listed prime `p`, define the necessary local set

`M_p = {T(w)-2T(v) mod p : S(w)=4*S(v) mod p}`.

The verifier enumerates every `(w,v)` in `F_p^2`, stores a witness for every
allowed residue in `M_p`, and retains exactly the integers `t` for which
`-3221225472*t mod p` belongs to `M_p`.  The Lean tables prove the same
universal field implications by ordinary `decide`.

| step | prime | survivors |
|---:|---:|---:|
| 0 | - | 431,188 |
| 1 | 17 | 177,548 |
| 2 | 521 | 86,232 |
| 3 | 509 | 42,235 |
| 4 | 491 | 21,029 |
| 5 | 457 | 10,678 |
| 6 | 463 | 5,404 |
| 7 | 487 | 2,769 |
| 8 | 383 | 1,444 |
| 9 | 449 | 743 |
| 10 | 439 | 375 |
| 11 | 499 | 179 |
| 12 | 443 | 89 |
| 13 | 7 | 47 |
| 14 | 431 | 23 |
| 15 | 397 | 10 |
| 16 | 467 | 4 |
| 17 | 409 | 0 |

Modulo 17, the only retained `t` classes are
`0,3,6,7,10,13,14`.  Writing `t=17q+r` therefore reduces the final ordinary
kernel scan to `q<25365`; 13 recursive scan shards cover that complete range.

## Source graph and reproduction

The public module reaches all 113 `Erdos686EvenK32*.lean` source files
transitively; there are no inert generated Lean certificates.  The graph has
1,963 source lines, 62 prime-table shards, 12 finite-strip shards, 13 quotient
scan shards, and 91 occurrences of ordinary `by decide`.  Its heavy
certificate imports are dependency-chained, so a clean build checks them
serially rather than launching all shards concurrently.

Focused reproduction:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 compute/campaign686/agent_t2_even_k32/even_k32_verify.py
PYTHONDONTWRITEBYTECODE=1 python3 compute/campaign686/agent_t2_even_k32/even_k32_cover_search.py
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider compute/campaign686/agent_t2_even_k32/test_even_k32_verify.py
lake build ErdosProblems.Erdos686EvenK32
```

The focused test result is `6 passed`.  The exact cover search reproduces

`[431188,177548,86232,42235,21029,10678,5404,2769,1444,743,375,179,89,47,23,10,4,0]`.

Frozen SHA-256 values:

- complete sorted Lean source graph: `412facc4ab5d51578108f4a6bf69430fd124df415afeb4bbb4c25e15dda81881`;
- public theorem module: `9da25e352c78d8a582469ad04b9fc2320ae97dea6a96b995650ec0bf93321071`;
- arithmetic core: `6bbdec96881588fc9d954e237f22d677bb18eea9502695b9a906559f2bde9f32`;
- exact verifier: `f7a966d6e0aee7de00af4b5050ebafbb1b633eeaae724922616dd87411e1d965`;
- cover search: `6948444282e1c5ac91037bf3c7a0f13c5d8216383dab3c3b10726bfb0f1d2def`;
- tests: `f2fafd63949166a91cfd52440bc05e7125ef88038474faeb2e670a47cd4b9cc4`;
- Lean generator: `8a53377bdda8cdd0e96d007e3d56ca3d993f2c93f1814f3bf68c2ab587f5a10e`.

No shared import aggregator, manifest, registry, attestation, or
`Erdos686FinalResidual` file was changed by this lane.
