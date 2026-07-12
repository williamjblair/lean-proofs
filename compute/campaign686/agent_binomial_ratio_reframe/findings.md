# Binomial-ratio reframe: findings

Date: 2026-07-12

Scope: investigate whether the identity

\[
  \binom{n+d+k}{k}=4\binom{n+k}{k},\qquad k\ge 16,\ d\ge k,
\]

falls to a standard theorem or to a uniform Runge argument.  This is a
negative-route audit, not a proof of Target 2.

## 1. Exact translation

Put

\[
  A(x,k)=\frac{(x+k)!}{x!}=(x+1)\cdots(x+k).
\]

Then, identically over the natural numbers,

\[
  A(x,k)=k!\binom{x+k}{k}.
\]

Consequently the #686 equation is exactly

\[
  A(n+d,k)=4A(n,k),
\]

and not merely an approximation or a divisibility consequence.

## 2. The applicable Erdős--Straus theorems stop at the two live walls

Erdős and Straus use precisely this `A(x,k)` notation in
[On Products of Consecutive Integers (1977)](https://users.renyi.hu/~p_erdos/1977-18.pdf).
Their equation (1.1) is `t A(n,k)=A(m,k)`.  The paper explicitly records that
their methods did not prove variable-`k` finiteness even for `t=2`.

Two theorems in that paper are close enough to require an exact hypothesis
check.

1. **Theorem 2.1.**  Given fixed positive `delta` and `Lambda`, if
   `k >= delta*n` and `n+k < m < Lambda*n`, then, above a threshold depending
   on `delta,Lambda`, `A(n,k)` does not divide `A(m,k)`.

   This does not cover #686.  Here `m=n+d`, the verified quotient-four window
   gives `9*d<n`, and `d/k` is unbounded.  Thus no fixed positive lower bound
   for `k/n` follows on the target domain; in fact the exact window has
   `n` of order `k*d`.

2. **Theorem 3.3.**  For fixed `Lambda>1`, there are only finitely many
   divisibility triples with `k>1`, `n+k<m<Lambda*n`, provided the lower
   interval `[n+1,n+k]` contains a prime.

   For a #686 solution with `d>k`, the strict gap and bounded-ratio conditions
   do hold (one may take `Lambda=2`, since `9*d<n`).  The prime premise fails
   in exactly the live branch: the kernel theorem
   `lower_block_composite_of_four_solution` proves that every one of
   `n+1,...,n+k` is composite.

Thus the binomial reframe lands inside the unhandled case isolated by the
1977 paper rather than supplying a theorem that resolves it.

Saradha and Shorey's
[On the ratio of two blocks of consecutive integers (1990)](https://repository.ias.ac.in/67750/1/67750.pdf)
studies the more general equation

\[
 a(x+1)\cdots(x+k)=b(y+1)\cdots(y+k+\ell).
\]

Its general conclusions are effective finiteness or bounds after fixing prime
support data such as `P(x)`, `P(y)`, or `P(x-y)`.  Those are not bounded by the
#686 hypotheses, so none of its stated results gives a uniform explicit
exclusion here.

## 3. The exact diagonal `d=k`

There is a clean natural-language boundary argument.  If `d=k`, then

\[
\begin{aligned}
 A(n,2k)
   &=A(n,k)A(n+k,k)\\
   &=4A(n,k)^2\\
   &=(2A(n,k))^2.
\end{aligned}
\]

The left side is a product of `2k` consecutive positive integers.  The
Erdős--Selfridge theorem
[The product of consecutive integers is never a power (1975)](https://users.renyi.hu/~p_erdos/1975-46.pdf)
therefore excludes `d=k` (indeed already its square case does).

This does **not** enter the kernel bank: the Erdős--Selfridge theorem is not
formalized in this repository.  It is also only the diagonal boundary.  For
`d>k` the two blocks no longer concatenate, so this argument says nothing.

## 4. Exact Runge obstruction

Homogenize the two-block curve as

\[
 F_k(X,Y,Z)=\prod_{i=1}^k(X+iZ)-4\prod_{i=1}^k(Y+iZ)=0.
\]

Its divisor at infinity is

\[
 F_k(X,Y,0)=X^k-4Y^k.
\]

For odd `k`, the binomial `T^k-4` is irreducible over `Q` by the standard
binomial irreducibility criterion: `4` is not a `p`-th power in `Q` for any
prime `p|k`, and the exceptional fourth-power clause is irrelevant because
`k` is odd.  Hence all `k` points at infinity form one rational Galois orbit.
The usual rational Runge criterion, which needs at least two rational factors
at infinity to construct a separating function, is unavailable.

For even `k`, one has the rational factorization

\[
 X^k-4Y^k=(X^{k/2}-2Y^{k/2})(X^{k/2}+2Y^{k/2}),
\]

which is exactly the parity split exploited by the existing square-root
polynomial method.  Factorization alone does not provide uniform constants.

## Verdict

The binomial notation is exact and conceptually useful, but it does not expose
a standard uniform exclusion.  The published divisibility theorem loses
precisely on composite lower blocks of relative length tending to zero, while
classical rational Runge loses precisely on odd `k`.  Apart from the external
`d=k` boundary argument, this route produces no new kernel-bankable theorem.
