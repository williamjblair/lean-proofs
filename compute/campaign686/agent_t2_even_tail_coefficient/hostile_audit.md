# Hostile audit: generic even-tail coefficient certificate

Status: **kernel-banked conditional tail theorem; universal certificate supply still missing in Lean**.

## Exact proved surface

The isolated module
`ErdosProblems/Erdos686EvenTailCoefficientCertificate.lean` defines the
finite record `EvenTailCoefficientCertificate r` and proves

```lean
theorem no_even_tail_solution_of_coefficient_certificate
    {r : ℕ} (hr : 2 ≤ r) (cert : EvenTailCoefficientCertificate r)
    {n d : ℕ} (hd : max (2 * r) cert.threshold ≤ d) :
    blockProduct (2 * r) (n + d) ≠ 4 * blockProduct (2 * r) n
```

It also proves the quantified wrapper

```lean
theorem no_even_tail_solution_of_coefficient_certificate_supply
    (supply : ∀ r : ℕ, 2 ≤ r → EvenTailCoefficientCertificate r) ...
```

No theorem asserting such a `supply` is present.

## Dependency tree and per-node verdict

1. `coefficientAbsSumBelow P m = sum_{i<m} |P_i|`.
   - Verdict: proved by a finite `Finset.range` definition; nonnegativity is
     proved term by term.
2. Full evaluation bound
   `|P(W)| <= (sum_{i<=q}|P_i|) W^q` for `deg P <= q`, `W>=1`.
   - Verdict: proved coefficientwise using `Polynomial.eval_eq_sum_range'`,
     the triangle inequality, and monotonicity of powers.
3. Lower-part bound
   `|P(W)-P_q W^q| <= (sum_{i<q}|P_i|) W^(q-1)`.
   - Verdict: proved coefficientwise.  The proof has a separate exact
     `q=0` branch, where the lower sum and the remainder both vanish.
4. Polynomial-part dominance.
   - Input: `T_r=C>=1`, `deg T<=r`, `A=sum_{i<r}|T_i|`, `W>2A`.
   - Output: `W^r < 2T(W)`, hence `T(W)>0`.
   - Verdict: proved, with no rational approximation.
5. Deficit dominance.
   - Input: `D_q=L!=0`, `deg D<=q`, `F=sum_{i<q}|D_i|`, `W>7F`.
   - Output:
     `6|L|W^q < 7|D(W)| < 8|L|W^q`.
   - Verdict: proved, including `q=0`.
6. Center window and power ratio.
   - Input: the quotient-four equation, `r>=2`, `d>=2r`, `q<r`.
   - Output: `w^q<3v^q` for the odd centers `v,w`.
   - Verdict: imported from the already kernel-banked
     `Erdos686EvenTailRunge.lean` surface.
7. Integer-trap smallness.
   - Input: `E=sum_{i<=q}|D_i|`, `w>10E`, and `q<r`.
   - Quantified bound: the proof derives
     `|D(w)-4D(v)| <= 5Ew^q < T(w) < T(w)+2T(v)`.
   - Verdict: proved exactly.  This replaces the informal phrase
     "the deficit is essentially lower order" with a displayed bound.
8. Deficit ratio.
   - The two `6/7`--`8/7` bounds and `w^q<3v^q` give
     `7|D(w)|<28|D(v)|`, hence `|D(w)|<4|D(v)|`.
   - Verdict: proved exactly.
9. Polynomial identity and centered bridge.
   - The record contains the exact polynomial equality
     `T^2=C^2 S+D` and a bridge from `S` to `centeredBlockProduct` for every
     natural center.  Evaluation plus the block equation gives
     `S(w)=4S(v)`.
   - Verdict: both uses are checked in Lean; no sampled evaluation is used.
10. Final contradiction.
    - The existing `integral_runge_trap` is applied to nodes 4, 7, 8, and 9.
    - Verdict: proved.

## Boundary audit

- `r=1`: deliberately excluded by `hr : 2 <= r`; the imported ratio-power
  proof uses `r-1`.
- `q=0`: accepted.  The lower coefficient norm is zero, and the dominance
  theorem contains an explicit zero-degree branch.
- `q=r`: rejected by the record field `q_lt : q<r`; the smallness proof needs
  `q+1<=r`.
- `D=0`: rejected by `D_coeff_q=L` and `L!=0`.
- negative or zero leading coefficient of `T`: rejected by `C>=1`.
- `d=2r`: not discarded.  It is included whenever it also exceeds the
  explicit certificate threshold.
- threshold equality: the theorem assumes `d>=M`, while the certificate
  stores strict inequalities `2A<M`, `7F<M`, and `10E<M`; consequently the
  pointwise inequalities remain strict at `d=M`.
- lower center: the proof does not assume `v>=d`; it derives `d<=v` from the
  exact quotient-four window, then obtains `M<=v<=w`.
- zero evaluation of `T`: impossible after node 4, because both centers are
  positive and `r>=2`.
- no smoothness hypothesis occurs anywhere in the theorem.

## Exact remaining construction lemma

The one unbanked statement is the following finite algebraic supply lemma:

```lean
∀ r : ℕ, 2 ≤ r → EvenTailCoefficientCertificate r
```

Expanded without the record abbreviation, for each `r>=2` one must construct
the centered polynomial

```text
S_r(W)=product_{j=1..r}(W^2-(2j-1)^2),
```

the unique monic rational polynomial `Q_r` of degree `r` satisfying
`degree(Q_r^2-S_r)<r`, clear its coefficient denominators by a positive
integer `C_r`, put `T_r=C_r Q_r` and `D_r=T_r^2-C_r^2S_r`, prove `D_r!=0`,
and populate the three exact coefficient norms and

```text
M_r=max(2A_r+1, 7F_r+1, 10E_r+1, 2r).
```

The Python recurrence in `agent_t2_even_tail/even_tail_verify.py` computes
this data exactly, but its arbitrary-`r` correctness and denominator clearing
have not been formalized in Lean.  This is a finite polynomial-construction
lemma independent of `n` and `d`; it is not asserted or hidden as an axiom in
the new module.

## Kernel and source gate

The public theorems print only
`[propext, Classical.choice, Quot.sound]`.  The module contains no
`sorry`, `admit`, or `native_decide`.

Source SHA-256 (recompute after any edit):

```text
09f93f48eba18555d55b25370c266f5becb2912e7a3011c994b97fe1be066c9b
```
