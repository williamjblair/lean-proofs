# Exact Kummer-unit restriction beyond the endpoint delta

This is a genuinely stronger paper-level necessary condition, but it is not
a closure and is not yet a Lean theorem.

Let `q=p^a`, `k=q-1`, `p>=5`, and write

\[
n=qs+r,\qquad n+d=qS+R,
\qquad 0<r,R<q.
\]

The endpoint theorem supplies the two strict residue inequalities.  Put

\[
A=(S+1)r,\qquad B=(s+1)R.
\]

For

\[
F_q(x)=\binom{x+q-1}{q-1},
\]

exact factor permutation modulo `q` gives, when `x=qs+r` and `0<r<q`,

\[
v_p(F_q(x))=a-v_p(r)+v_p(s+1),
\]

and

\[
\operatorname{unit}_p(F_q(x))
 \equiv
 \operatorname{unit}_p(s+1)\,
 \operatorname{unit}_p(r)^{-1}\pmod p.
\]

Indeed the nonzero residues of `x+1,...,x+q-1` permute all nonzero residues
modulo `q` except `r`; the missing factor is replaced by the unique multiple
`q(s+1)`.  Every other factor has the same valuation and p-free unit as its
residue.

Since `p` does not divide four, the exact equation `F_q(n+d)=4F_q(n)` forces

\[
\boxed{v_p(A)=v_p(B)=V}
\]

and

\[
\boxed{
  A/p^V\equiv4(B/p^V)\pmod p.
}
\]

This is strictly stronger than the endpoint theorem.  At

```text
(p,a,n,d)=(5,1,1,5)
```

both endpoint residues are nonzero, but `A=2`, `B=1`, so the new congruence
would require `2=4 (mod 5)`.

It is not a closure.  The tuple

```text
(p,a,n,d)=(5,1,1,7)
```

has `A=2`, `B=3`, hence `2=4*3 (mod 5)`, and survives with `d>=k=4`.
The exact verifier exhausts `s,S in {0,...,24}` and all nonzero `r,R` with
`d>=4`: 774 of 4,728 endpoint-admissible ordered tuples survive.  It also
checks that the compressed condition is exactly equivalent to valuation
equality and the p-free-unit equation computed directly from both binomial
coefficients.

Because hundreds of residue classes survive already for `p=5,a=1`, this
restriction is recorded as a proper equation-facing filter only.  Promoting
it to `FinalResidual686Hypothesis` before a kernel proof would violate the
intake protocol.
