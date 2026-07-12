# Hostile audit: universal even-tail certificate supply

Status: **fully kernel-banked universal supply and unconditional effective
tail theorem**.

Source:
`ErdosProblems/Erdos686EvenTailSupply.lean`

SHA-256:

```text
7784331341c8c8eff14a2c27d7a344e8a130ce6c4f569178bd42a74c1aa54da5
```

## Exact exported surfaces

The module constructs the requested dependent supply:

```lean
noncomputable def universalEvenTailCertificateSupply :
    ∀ r : ℕ, 2 ≤ r → EvenTailCoefficientCertificate r
```

and derives:

```lean
theorem no_even_tail_solution_universal
    {r n d : ℕ} (hr : 2 ≤ r)
    (hd : max (2 * r)
      (universalEvenTailCoefficientCertificate r hr).threshold ≤ d) :
    blockProduct (2 * r) (n + d) ≠ 4 * blockProduct (2 * r) n
```

Thus every even row `k=2r>=4` has an explicit finite coefficient threshold
above which quotient four is impossible.  This theorem does not claim that
the finite strip below its threshold has been checked.

## Dependency tree and per-node verdict

1. **Descending correction.**
   - At stage `j<r`, put
     `a=-(Q^2-S)_{r+j}/2` and `Q'=Q+aX^j`.
   - Exact invariant:
     `deg(Q^2-S)<r+j+1` implies `deg(Q'^2-S)<r+j` while `Q'`
     remains monic of degree `r`.
   - The proof expands
     `Q'^2-S=(Q^2-S)+2aQX^j+a^2X^(2j)`.
     At degree `r+j`, the middle coefficient is `2a` because `Q_r=1`,
     and `2j<r+j`; all higher coefficients vanish by degree bounds.
   - Verdict: proved in `squareRootRefine_step` over `ℚ[X]`.
2. **Finite recurrence.**
   - Start with `Q=X^r`.  Since `Q^2` and `S` are both monic of degree
     `2r`, their difference has degree `<2r`.
   - `Nat.decreasingInduction` applies node 1 for `j=r-1,...,0`.
   - Output: a monic degree-`r` `Q` with `deg(Q^2-S)<r`.
   - Verdict: proved in `exists_monic_rational_square_root_part`.
3. **Centered polynomial.**
   - Definition:
     `S_r=product_{i=1}^{2r}(X+(2i-2r-1))` over `ℤ[X]`.
   - It is monic of degree `2r`, and evaluation at
     `2x+2r+1` is definitionally the existing `centeredBlockProduct`.
   - Verdict: proved for every `r`, without sampled expansion.
4. **Simple root at one.**
   - The factor indexed by `i=r` is `X-1`.
   - Every other factor evaluates at one to `2(i-r)`, which is nonzero.
   - Consequently `S_r(1)=0` and `S_r'(1)!=0`.
   - Verdict: proved with `Finset.prod_ne_zero_iff` and the product rule.
5. **No scaled square.**
   - If `T^2=C^2S_r` with `C!=0`, evaluation at one forces `T(1)=0`.
   - Differentiation at one then forces `C^2S_r'(1)=0`, contradicting
     node 4.
   - Verdict: proved in `evenCenteredPolynomial_ne_scaled_square`.
6. **Positive denominator clearing.**
   - `IsLocalization.integerNormalization (nonZeroDivisors ℤ)` supplies an
     integral polynomial and a nonzero integer multiplier `b`.
   - Multiplying the integral polynomial by `sign(b)` changes the multiplier
     to `C=|b|>=1`.
   - The map to `ℚ[X]`, degree `r`, and leading coefficient `C` are proved
     exactly.
   - Verdict: proved in
     `exists_positive_integral_multiple_of_monic_rational`.
7. **Integral deficit.**
   - Define `D=T^2-C^2S_r` in `ℤ[X]`.
   - Mapping to `ℚ[X]` gives exactly
     `map(D)=C^2(Q^2-map(S_r))`, so injectivity of `ℤ→ℚ` and node 2 give
     `deg D<r`.
   - If `D=0`, node 5 is contradicted.  Hence `D!=0`, and with
     `q=deg D`, its leading coefficient `L=D_q` is nonzero.
   - Verdict: proved inside `universalEvenTailCoefficientCertificate`.
8. **Exact norms and threshold.**
   - Set
     `A=sum_{i<r}|T_i|`, `E=sum_{i<=q}|D_i|`, and
     `F=sum_{i<q}|D_i|`.
   - Set
     `M=max(2r,2A+1,7F+1,10E+1)`, implemented over naturals after proving
     all three norms nonnegative.
   - The strict inequalities `2A<M`, `7F<M`, `10E<M` are proved at the
     exact boundary.
   - Verdict: proved; no asymptotic constant remains.
9. **Certificate assembly and exclusion.**
   - Nodes 2--8 populate every field of
     `EvenTailCoefficientCertificate r`.
   - The previously audited generic coefficient theorem then gives
     `no_even_tail_solution_universal`.
   - Verdict: proved.

## Boundary audit

- `r=0`: recurrence and certificate supply are not claimed.
- `r=1`: the algebraic construction itself would still have the expected
  simple-root behavior, but the exported supply deliberately assumes
  `r>=2` because the downstream centered-ratio theorem uses `r-1`.
- `j=0`: the final recurrence step cancels degree exactly `r`; the term
  `a^2X^(2j)` has degree zero, strictly below `r`.
- `j=r-1`: the first step cancels degree `2r-1`; the starting deficit is
  already below `2r` because both leading coefficients are one.
- zero rational deficit: allowed during the recurrence, but impossible for
  the actual centered polynomial after positive scaling by node 5.
- negative denominator multiplier: normalized by `sign(b)`; the resulting
  leading coefficient is exactly `|b|`, not merely nonzero.
- zero denominator multiplier: excluded by membership in
  `nonZeroDivisors ℤ`.
- `q=0`: accepted.  Nonzero constant deficit has a nonzero leading
  coefficient, and the downstream coefficient certificate has a separate
  exact `q=0` branch.
- threshold equality: `M` contains `2A+1`, `7F+1`, and `10E+1`, so every
  downstream strict inequality holds at `d=M`.
- no smoothness hypothesis is used.
- no finite row scan or unverified computation is used to establish the
  universal quantifier.

## Kernel gate

All exported surfaces print only
`[propext, Classical.choice, Quot.sound]`.  `Classical.choice` enters through
the finite existence choices and `integerNormalization`; it is within the
allowed gate.  The source contains no `sorry`, `admit`, or `native_decide`.

## Remaining gap

There is no remaining construction lemma for the universal even-tail supply.
The remaining mathematical work toward Target 2 is outside this result: it
must control the finite, row-dependent region below the effective threshold
and all odd rows.
