# Hostile audit: sharp centered ratio

Verdict: **PASS as a kernel-banked strengthening; FAIL as a Target-2 closure**.

Frozen SHA-256 inputs:

```text
43328f2159ea1eec247dc55077323a5aa335abd45c00ae5579ee589e57cf8e4a  ErdosProblems/Erdos686CenteredRatioWindowSharp.lean
2e18053fb6004fcc434a1339ff3d2428ed50b4fc23cc3359100e8e9ccf7ed171  compute/campaign686/agent_t2_centered_ratio_sharp/sharp_centered_verify.py
8144387ce14eddfea7d5b1c675e0a3dc375731af13cfb65b423df793617a2320  compute/campaign686/agent_t2_centered_ratio_sharp/test_sharp_centered_verify.py
2a820b13c47672d17edd9050c0aa44c3265d11ab74b73f549f15fc937b826841  compute/campaign686/agent_t2_centered_ratio_sharp/findings.md
```

## Dependency tree

```text
exact quotient-four equation
├── centered opposite-position product inequality       [Lean PASS]
│   └── W^k < 4*T^k                                  [Lean PASS]
├── seven-term rational binomial bracket from k=16     [Lean PASS]
│   └── 4*(2500k)^k < (2500k+3621)^k               [Lean PASS]
└── exact centered linear comparison                   [Lean PASS]
    ├── maximal fixed-bracket ratio 1218443/1853952      [Lean PASS]
    ├── clean corollary: 23*k*d < 35*n                   [Lean PASS]
    └── maximal owner band 3707904*a<=1218443*k          [Lean PASS]
```

## Per-node verdicts

| Node | Verdict | Exact content |
|---|---|---|
| root bracket | PASS | First seven binomial terms give an exact rational excess `194856715132747962308721 / 512000000000000000000000000`. |
| boundary `k=16` | PASS | The linear comparison has exact positive scaled slack `4609`; no asymptotic monotonicity phrase hides the boundary. |
| centered ratio | PASS | Strongest fixed-bracket theorem is exactly `1218443*k*d<1853952*n`; `23*k*d<35*n` is a readable corollary. |
| cofactor band | PASS | Maximal band is `3707904*a<=1218443*k`, conditional on `n+i=a*p^A`, `p>k`, `A>=1`; the clean corollary is `70*a<=23*k`. |
| proposed `7/10` | FAIL for this route | A required root increment is `>7/5`, while the `k=d=16` linear step requires `<2560/1877<7/5`. |
| closure | FAIL | No theorem supplies a lower term in the certified cofactor band. |

## Boundary falsification

At `(k,n,d)=(16,175,16)`, exact integer arithmetic gives all three power
windows and `10*n<=7*k*d`.  The point is explicitly marked a non-equation.
It therefore falsifies a `7/10` proof that silently upgrades power-window
compatibility to the full block equation, while leaving open whether some
additional equation structure could prove a stronger coefficient.

## Exact remaining gap

To turn the sharp band into a Target-2 closure, prove a supply statement:

> Every target-range quotient-four solution has a lower position `i` and
> integers `a,p,A` with `p` prime, `p>k`, `A>=1`, `n+i=a*p^A`, and
> `3707904*a<=1218443*k`.

No such statement is asserted here; it is a genuine new lemma rather than a
rephrasing of the centered ratio theorem.
