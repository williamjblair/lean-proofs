# Erdős 686 row k=28: exact closure certificate

## Outcome

The row is arithmetically closed: for every `n,d : Nat` with `28 <= d`,

`blockProduct 28 (n+d) != 4 * blockProduct 28 n`.

The independent verifier reconstructs all data from integer arithmetic and
reports payload SHA-256
`ad9612473125746a0a665e659f3b3b61c158aee49a1d3f61ac012a3eee4fb5cf`.

## Exact split

The centered polynomial is

`S(W) = product_{j=1}^{14} (W^2-(2j-1)^2)`.

Its integral square-root polynomial part `T` has degree 14 and satisfies
`T(W)^2 = S(W)+D(W)` with `deg D=12`.  On odd centers,

`50176 = 2^10 * 7^2 | T(2a+1)`.

The ratio brackets are exact:

- `4*19^28 < 20^28`, giving `19d < n+28`;
- `83^28 < 4*79^28`, giving `4(n+1) < 79d`.

For `28 <= d < 384`, these inequalities leave exactly 64,258 pairs.  Direct
integer evaluation gives no zero of `S(w)-4S(v)`; the boundary row `d=28`
contains 47 checked pairs and `d=383` contains 314.

For `d>=384`, put `v=2n+29`, `w=v+2d`, and
`m=T(w)-2T(v)`.  Then `v>=14567`, `w>=v+768`, and `10w<=11v`.  Exact shifted
coefficient expansions give

`-52682724273 < m < 0`.

The lower bound has 120 strictly positive shifted coefficients and its least
valid integer constant is exactly 52,682,724,273, binding at coefficient
`a^0 b^0`.  The upper sign uses 13 strictly negative shifted coefficients in
the conservative `10^12(D(w)-4D(v))` majorant.

Because `50176|m`, one has `m=-50176t` with the strict endpoint bound

`1 <= t <= floor((52682724273-1)/50176) = 1049958`.

## Exact field cover

For a prime `p` not dividing 50,176, the verifier computes the local set

`M_p = {T(w)-2T(v) mod p : S(w)=4S(v) mod p}`

and keeps precisely those `t` satisfying `-50176t mod p in M_p`.  Every
retained local value has an explicit `(w,v)` witness, and every eliminated
integer fails the local predicate at the stated prime.

The lower-peak-memory cover used by Lean is:

| step | prime | survivors |
|---:|---:|---:|
| 0 | - | 1,049,958 |
| 1 | 29 | 144,821 |
| 2 | 349 | 70,952 |
| 3 | 347 | 35,763 |
| 4 | 317 | 18,323 |
| 5 | 331 | 9,881 |
| 6 | 353 | 5,345 |
| 7 | 283 | 2,868 |
| 8 | 337 | 1,616 |
| 9 | 293 | 933 |
| 10 | 281 | 531 |
| 11 | 307 | 302 |
| 12 | 257 | 167 |
| 13 | 271 | 92 |
| 14 | 239 | 52 |
| 15 | 197 | 27 |
| 16 | 313 | 12 |
| 17 | 241 | 6 |
| 18 | 277 | 2 |
| 19 | 5 | 1 |
| 20 | 37 | 0 |

Modulo 29, the only surviving quotient classes are `5,14,15,24`.  This
compresses the ordinary-kernel candidate scan to the 36,206 values of `q`
needed to represent `t=29q+r`.  The verifier also reproduces the shorter
unrestricted greedy cover
`[29,971,991,977,773,853,919,797,827,353,331]`, with survivor counts
`[1049958,144821,48916,16531,5589,1901,642,203,62,17,3,0]`; Lean uses the
20-prime cover above because its maximum field is 353 and its exhaustive table
graph has lower peak memory.

## Reproduction

```sh
PYTHONDONTWRITEBYTECODE=1 python3 compute/campaign686/agent_t2_even_k28/even_k28_verify.py
PYTHONDONTWRITEBYTECODE=1 python3 compute/campaign686/agent_t2_even_k28/even_k28_cover_search.py
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider compute/campaign686/agent_t2_even_k28/test_even_k28_verify.py
lake build ErdosProblems.Erdos686EvenK28
```

The Lean graph uses ordinary `decide` only.  The prime tables, finite strip,
and quotient scans are serially sharded so no source file carries the full
enumeration.
