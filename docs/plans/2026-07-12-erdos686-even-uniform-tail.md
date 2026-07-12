# Erdős 686 even uniform Runge tail

**Goal.** Prove an effective, non-asymptotic exclusion for every even row
`k = 2r`: once `d` exceeds a completely explicit coefficient norm depending
only on `r`, the equation `B(k,n+d) = 4 B(k,n)` is impossible.

**Architecture.** For

```text
S_r(W) = product_{j=1..r} (W^2-(2j-1)^2),
```

construct the rational polynomial part of `sqrt(S_r)`, clear its
denominators to an integral polynomial `T_r`, and put
`D_r = T_r^2-C_r^2 S_r`.  The construction gives `deg D_r < r`.  At an
equation point, `S_r(w)=4S_r(v)`, so the integer
`m=T_r(w)-2T_r(v)` satisfies

```text
m(T_r(w)+2T_r(v)) = D_r(w)-4D_r(v).
```

Explicit coefficient norms make the right side smaller than the positive
second factor for large `v`, forcing `m=0`.  The equation would then force
`D_r(w)=4D_r(v)`.  Leading-term dominance and the exact ratio bound
`w/v < 1+1/(r-1)` instead give `|D_r(w)|<4|D_r(v)|`.

## Tasks

1. Implement the polynomial-part recurrence with exact rational arithmetic.
2. Generate the cleared integral polynomials, deficits, coefficient norms,
   and explicit threshold `M_r`.
3. Verify all polynomial identities and inequalities symbolically, without
   floating point.
4. Record a self-contained proof of the uniform theorem and its exact
   dependence on `M_r`.
5. Bank the generic integer-trap core in Lean; do not advertise the uniform
   theorem as kernel-checked until the certificate-construction layer is also
   formalized.
