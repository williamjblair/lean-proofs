# Sharp centered ratio window

Status: **kernel-banked strengthening; not a Target-2 closure**.

## Certified theorem

For every `k>=16`, `d>=k`, and exact quotient-four solution,

```text
1218443*k*d < 1853952*n.
```

This improves the previous coefficient from `13/20=0.65` to
`1218443/1853952`, with the cleaner corollary `23*k*d<35*n`.  The proof uses
the already kernel-banked centered window, with `T=2n+k+1` and `W=T+2d`:

```text
W^k < 4*T^k.
```

The sharper exact rational root bracket is

```text
4*(2500*k)^k < (2500*k+3621)^k.
```

It is uniform from `k=16`.  Expanding
`(1+3621/(2500k))^k`, retaining terms `j=0,...,6`, and replacing every
normalized falling factor `(k-r)/k` by `(16-r)/16` gives the exact lower
bound

```text
2048194856715132747962308721 / 512000000000000000000000000
  = 4 +
    194856715132747962308721 / 512000000000000000000000000
  > 4.
```

For the clean `23/35` corollary, assuming `35*n<=23*k*d` and multiplying by
exact integers gives

```text
253470*n <= 166566*k*d,
126735*(k+1) < 8434*k^2 <= 8434*k*d.
```

The boundary slack in the second inequality is `4609` at `k=d=16`.
Together these inequalities say

```text
(2500*k+3621)*T < (2500*k)*W,
```

whose `k`th power contradicts the centered window and root bracket.

The theorem is
`twenty_three_k_mul_gap_lt_thirty_five_mul_n_of_four_solution` in
`ErdosProblems/Erdos686CenteredRatioWindowSharp.lean`.

For the fixed `3621/2500` bracket, the exact maximal coefficient allowed by
the worst centered boundary `k=d=16` is

```text
2500/3621 - 17/512 = 1218443/1853952.
```

At that coefficient the linear comparison is non-strict at the boundary;
the centered window itself remains strict, so the final contradiction still
closes.  This stronger theorem is
`maximal_sharp_bracket_ratio_of_four_solution`.

## Cofactor consequence

The any-position large-prime owner obstruction now excludes

```text
n+i = a*p^A,  p prime, p>k, A>=1,
3707904*a <= 1218443*k.
```

Indeed `d+k-1<2d`, so the doubled cofactor coefficient composes directly
with the maximal ratio.  The cleaner but slightly narrower corollary is

```text
35*a*(d+k-1) < 70*a*d <= 23*k*d < 35*n.
```

These are kernel-banked as
`no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_maximal_sharp_band`
and
`no_four_solution_lower_term_cofactor_prime_power_base_gt_length_of_sharp_band`.
It is not a supply theorem for a term of this form.

## Why `7/10` is not certified

The proposed `7*k*d<10*n` coefficient is incompatible with this rational
root-bracket route already at `k=d=16`.  A root increment `c` must exceed
`7/5`, since

```text
87^16 < 4*80^16.
```

But the linear comparison under `10*n<=7*k*d` requires

```text
c < 2560/1877 < 7/5.
```

More strongly, the exact non-equation point `(k,n,d)=(16,175,16)` satisfies
all three equation-derived power windows:

```text
399^16 < 4*367^16,
4*176^16 <= 192^16,
207^16 <= 4*191^16,
```

while `10*175<=7*16*16`.  This is a counterboundary to any derivation using
only those windows, not a counterexample to the original block equation.

The real centered-window ceiling at `k=d=16` is approximately
`0.6573456066`; that decimal is explanatory only and is not used in either
the Lean proof or verifier.  The strongest exact certified rational returned
by this lane is `1218443/1853952`; `23/35` is retained as the readable
corollary.

## Reproduction

```bash
python3 -m pytest \
  compute/campaign686/agent_t2_centered_ratio_sharp/test_sharp_centered_verify.py -q
lake env lean ErdosProblems/Erdos686CenteredRatioWindowSharp.lean
```

The Lean axiom output is exactly
`[propext, Classical.choice, Quot.sound]`; there is no `native_decide`,
`sorry`, or custom theorem axiom.
