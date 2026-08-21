# A positive-density solution of Erdős #730

This is the cleaned, durable paper proof audited in `audit.md`.  It is
self-contained apart from the three imported theorems stated explicitly
below.  All asymptotic cutoffs `X` are positive integers tending to infinity,
and all logarithms are natural.

Put

\[
B(t)=\binom{2t}{t},\qquad
\operatorname{supp}(N)=\{p\text{ prime}:p\mid N\}.
\]

Let

\[
T=3\cdot41\cdot43=5289,
\]

\[
P(x)=42Tx+11,\quad Q(x)=72Tx+13,
\]

\[
R(x)=28Tx+5,\quad S(x)=72Tx+19,
\]

and `n_x=P(x)Q(x)-1`.  We prove

\[
\liminf_{X\to\infty}\frac1X
\#\{1\le x\le X:
\operatorname{supp}B(n_x)=\operatorname{supp}B(n_x+1)\}
>\frac{107}{2500}. \tag{1}
\]

In particular, Erdős #730 has infinitely many consecutive solutions.

## Imported theorems

We use exactly the following results.

1. **Kummer's theorem.** For every prime `p` and nonnegative integers `u,v`,
   the exponent of `p` in `binomial(u+v,u)` equals the number of carries in
   the base-`p` addition of `u` and `v`.
2. **Mertens' reciprocal-prime theorem.** There is a constant `M` such that,
   for every real `z>2`,

   \[
   \sum_{p\le z}\frac1p=\log\log z+M+\varepsilon(z),
   \qquad |\varepsilon(z)|\le\frac4{\log z}. \tag{2}
   \]

3. **PNT in fixed arithmetic progressions.** For every fixed positive
   integer `A`, there are positive constants `K_A,kappa_A,z_A` such that,
   uniformly over reduced residue classes `a mod A`,

   \[
   \left|\pi(z;A,a)-\frac{\operatorname{Li}(z)}{\varphi(A)}\right|
   \le K_Az\exp(-\kappa_A\sqrt{\log z}) \qquad(z\ge z_A). \tag{3}
   \]

We also use the `A=1` consequence `pi(z)=O(z/log z)`.

## 1. Exact transition criterion

For an odd prime `p`, let `D_p` be the set of nonnegative integers all of
whose base-`p` digits are at most `(p-1)/2`.  Kummer applied to `t+t` gives

\[
p\nmid B(t)\quad\Longleftrightarrow\quad t\in D_p. \tag{4}
\]

### Proposition 1

For `n>=1`, the supports of `B(n)` and `B(n+1)` agree if and only if, for
every odd prime `p`, both conditions hold:

\[
p^a\parallel n+1\quad\Longrightarrow\quad (n+1)/p^a\notin D_p, \tag{5}
\]

\[
p^a\parallel2n+1\quad\Longrightarrow\quad
\big((2n+1)/p^a-1\big)/2\notin D_p. \tag{6}
\]

**Proof.** Since

\[
\frac{B(n+1)}{B(n)}=\frac{2(2n+1)}{n+1},\qquad
\gcd(n+1,2n+1)=1,
\]

an odd prime can change support membership only if it divides `n+1` or
`2n+1`.

If `n+1=p^ac` with `p` not dividing `c`, then `n=p^ac-1`; its final `a`
base-`p` digits are all `p-1`, so `p` divides `B(n)`.  The base-`p` expansion
of `n+1` is that of `c` followed by `a` zeros.  By (4), `p` drops precisely
when `c` belongs to `D_p`.  This proves (5).

If `2n+1=p^ac`, then

\[
n=p^a\frac{c-1}{2}+\frac{p^a-1}{2}. \tag{7}
\]

The final `a` digits of `(p^a-1)/2` are `(p-1)/2`, whence

\[
n\in D_p\quad\Longleftrightarrow\quad(c-1)/2\in D_p. \tag{8}
\]

But the units digit of `(p^a+1)/2` is `(p+1)/2`, so `n+1` is not in `D_p`
and `p` always divides `B(n+1)`.  Thus `p` enters precisely when `(c-1)/2`
belongs to `D_p`, proving (6).  Finally,
`B(t)=2 binomial(2t-1,t-1)`, so `2` is always present. ∎

## 2. The four-branch family

Direct expansion gives

\[
2PQ-1=3RS=6048T^2x^2+2676Tx+285. \tag{9}
\]

The six identities

\[
12P-7Q=41,\quad18R-7S=-43,\quad12P-7S=-1, \tag{10}
\]

\[
7Q-18R=1,\quad2P-3R=7,\quad S-Q=6 \tag{11}
\]

are immediate.  Hence

\[
n_x+1=PQ,\qquad 2n_x+1=3RS. \tag{12}
\]

The four branch values are pairwise coprime.  Indeed, (10)-(11) imply that
the six pairwise gcds divide respectively `41,43,1,1,7,6`.  The constants
of `P,Q` are units modulo `41`, those of `R,S` are units modulo `43`,
`P=4` and `R=5 mod 7`, and `Q,S` are odd and `1 mod 3`.

The primes `41,43` divide no branch.  Modulo `3`, `P,R=2` and `Q,S=1`, so
`3 || 3RS`.  Its quotient test is `(RS-1)/2=2 mod 3`, whose least base-3
digit is forbidden; hence `3` is harmless.  The prime `7` is retained as an
ordinary branch prime wherever it can occur.

## 3. Obstruction maps and exact permutation

Suppose `p^a || L(x)` and write `L(x)=p^ac`.  Proposition 1 gives the four
obstruction quantities

\[
\Phi_P(c)=cQ=\frac{12p^ac^2-41c}{7},\qquad
\Phi_Q(c)=cP=\frac{7p^ac^2+41c}{12}, \tag{13}
\]

\[
\Phi_R(c)=\frac{3cS-1}{2}
=\frac{54p^ac^2+129c-7}{14}, \tag{14}
\]

\[
\Phi_S(c)=\frac{3cR-1}{2}
=\frac{7p^ac^2-43c-6}{12}. \tag{15}
\]

The left descriptions establish integrality.

For every branch prime, the branch slope is invertible modulo `p`: any
prime dividing both slope and branch value would divide the branch constant,
which the preceding fixed-prime checks exclude.  Choose the unique root
`x_0 mod p^a` and write

\[
x=x_0+p^ak,\qquad c=c_0+A_Lk,qquad c_0=L(x_0)/p^a,
\]

where `A_L` is the slope of `L`.  Substitution in (13)-(15) gives

\[
G(k)=3024T^2p^ak^2+(p^au_L+b_L)k+v_L, \tag{16}
\]

with integral `u_L,v_L` and

\[
(b_P,b_Q,b_R,b_S)=(-246T,246T,258T,-258T). \tag{17}
\]

The prime factors of `246T` and `258T` are contained in
`{2,3,41,43}`, none a branch prime.  Therefore

\[
G(k_1)-G(k_2)=(k_1-k_2)
\big(3024T^2p^a(k_1+k_2)+p^au_L+b_L\big)
\]

has a `p`-adic-unit second factor, and

\[
v_p(G(k_1)-G(k_2))=v_p(k_1-k_2). \tag{18}
\]

Thus `G` permutes every residue system modulo `p^d`.

Put

\[
H=(p+1)/2,\qquad\rho_p=H/p. \tag{19}
\]

Exact valuation deletes one class of `k mod p`, namely `c=0 mod p`.
Its image is `0` for P,Q and `-1/2=(p-1)/2 mod p` for R,S.  In either case
one endpoint of the `H` permitted units digits is deleted.  Hence the exact
number of classes `k mod p^d` satisfying exact valuation and having their
first `d` output digits permitted is

\[
(H-1)H^{d-1}. \tag{20}
\]

## 4. Events and ranges

Let `E_{L,p,a}(x)` be the event

\[
p^a\parallel L(x),\qquad
\Phi_L(L(x)/p^a)\in D_p. \tag{21}
\]

Let `Bad(X)` count parameters `1<=x<=X` whose two supports differ, and let
`E(X)` count all quadruples `(x,L,p,a)` satisfying (21).  Proposition 1,
branch coprimality, and the fixed-prime checks give

\[
Bad(X)\le E(X). \tag{22}
\]

Set

\[
Y=X^{1/2}(\log X)^2. \tag{23}
\]

Partition `E` disjointly into `E_{>=2}` (`a>=2`), `E_small` (`a=1` and
`p<=sqrt X`), `E_trans` (`a=1` and `sqrt X<p<=Y`), and `E_top` (`a=1` and
`p>Y`).  Thus

\[
E=E_{\ge2}+E_{\rm small}+E_{\rm trans}+E_{\rm top}. \tag{24}
\]

## 5. Higher powers

Let

\[
C_0=72T+19=380827.
\]

For `1<=x<=X`, every branch is at most `C_0X`.  Fix `L,p,a` with `a>=2`
and first suppose `p^a<=X`.  Put

\[
r=\left\lfloor\log_p(X/p^a)\right\rfloor\ge0,
\quad p^r\le X/p^a<p^{r+1}. \tag{25}
\]

The root progression contains at most `X/p^a+1` values of `k`.  Cover it by
complete or padded blocks of `p^r` consecutive values.  On each block,
membership in `D_p` implies that the first `r` digits are permitted; the
permutation property bounds the count by `H^r`.  The argument also applies
when `r=0`, where the digit condition is vacuous.  With `U=X/p^a`,

\[
\#E_{L,p,a}(X)
\le\left(\frac{U+1}{p^r}+1\right)H^r
\le2U\rho_p^r+1. \tag{26}
\]

For every fixed `(p,a)`, `r` tends to infinity, while

\[
0\le\frac2{p^a}\rho_p^r\le\frac2{p^a},\qquad
\sum_p\sum_{a\ge2}\frac1{p^a}<\infty.
\]

Dominated convergence therefore makes the normalized sum of the first term
in (26) tend to zero.  If

\[
M(Z)=\#\{(p,a):a\ge2,\ p^a\le Z\},
\]

then

\[
M(Z)\le Z^{1/2}+Z^{1/3}\log_2Z=o(Z). \tag{27}
\]

This handles the `+1` terms.  If `X<p^a<=C_0X`, invertibility of the branch
slope gives at most one parameter in its root class; (27) again gives
`o(X)`.  Summing four branches,

\[
E_{\ge2}(X)=o(X). \tag{28}
\]

## 6. The fixed-depth Fourier lemma

### Lemma 2

Fix `r>=1`.  Let `p` be odd, `q=p^(2r)`, and

\[
F(t)=p\alpha t^2+\beta t+\gamma,qquad p\nmid\alpha\beta.
\]

Let `A` be a `2r`-digit base-`p` box in which one digit interval has length
`H-1` and the remaining intervals have length `H`.  Uniformly in the integer
start `M` and in `alpha,beta,gamma`,

\[
\left|\#\{0\le t<p^r:F(M+t)\bmod q\in\mathcal A\}
-\frac{|\mathcal A|}{p^r}\right|
\le C_rp^{r-1/2}(1+\log p)^{2r+1}, \tag{29}
\]

where `C_r=(2r+3)3^(2r)`.

**Proof.** Translation replaces `beta` by `beta+2p alpha M`, still a unit,
so take `M=0`.  With unnormalized Fourier transform, inversion writes the
count as

\[
\frac1q\sum_{h\bmod q}\widehat{1_{\mathcal A}}(h)
\sum_{0\le t<p^r}e_q(hF(t)). \tag{30}
\]

The zero frequency is `|A|/p^r`.  For `h!=0`, write
`h=p^(2r-m)u`, with `1<=m<=2r` and `p` not dividing `u`.  The inner sum is

\[
S_m(u)=\sum_{0\le t<p^r}e_{p^m}(uF(t)).
\]

Because `F(x)-F(y)=(x-y)(p alpha(x+y)+beta)`, `F` permutes modulo every
`p^m`.  If `m<=r`, the interval contains complete residue systems, so
`S_m(u)=0`.

Assume `m>r`, put `Q=p^m,N=p^r`, and complete the interval.  The complete
sum

\[
C(s)=\sum_{z\bmod Q}e_Q(up\alpha z^2+(u\beta+s)z+u\gamma)
\]

vanishes unless `s=-u beta mod p`.  On that nonzero class, reduction to a
unit quadratic Gauss sum modulo `p^(m-1)` gives

\[
|C(s)|=p^{(m+1)/2}. \tag{31}
\]

The geometric-sum bound and layer cake, restricted to one nonzero class
modulo `p`, give

\[
\sum_{s=-u\beta\bmod p}
\left|\sum_{0\le v<N}e_Q(-sv)\right|
\le\frac Qp(3+\log N). \tag{32}
\]

Consequently

\[
|S_m(u)|\le p^{(m-1)/2}(3+\log N)
\le(2r+3)p^{r-1/2}(1+\log p). \tag{33}
\]

For any consecutive digit interval `E`, the same geometric bound and layer
cake give

\[
\sum_{j=0}^{p-1}\left|
\sum_{e\in E}e^{2\pi i e(\theta+j/p)}\right|
\le p(3+\log p). \tag{34}
\]

Factoring the Fourier transform digit by digit and inducting yields

\[
\sum_{h\bmod p^{2r}}|\widehat{1_{\mathcal A}}(h)|
\le p^{2r}(3+\log p)^{2r}
\le q\,3^{2r}(1+\log p)^{2r}. \tag{35}
\]

Combine (30), the exact vanishing, (33), and (35) to obtain (29). ∎

## 7. First powers below square root

For `p<=sqrt X`, define the unique `r>=1` by

\[
p^{r+1}\le X<p^{r+2},
\quad X^{1/(r+2)}<p\le X^{1/(r+1)}. \tag{36}
\]

Fix `r`.  For all sufficiently large `X`, every prime in (36) exceeds `43`.
For `a=1`, (16) has the form required by Lemma 2.  By (20), the density of
the first `2r` permitted digits with exact valuation is

\[
\delta_{p,r}=\frac{(H-1)H^{2r-1}}{p^{2r}}
=4^{-r}(1-p^{-1})(1+p^{-1})^{2r-1}. \tag{37}
\]

The `k`-interval has length at most `X/p+1`.  Splitting it into complete
blocks of length `p^r` and one terminal block, Lemma 2 gives

\[
E_{L,p,1}(X)\le(X/p+1)\delta_{p,r}
+2C_rXp^{-3/2}(1+\log p)^{2r+1}+p^r. \tag{38}
\]

Put `U=X^(1/(r+1))`, `V=X^(1/(r+2))`.  For fixed `r`,

\[
X\sum_{n>V}n^{-3/2}(1+\log n)^{2r+1}=o_r(X). \tag{39}
\]

Also, eventually `pi(U)<=2U/log U`, so

\[
\sum_{p\le U}p^r\le U^r\pi(U)
\le\frac{2(r+1)X}{\log X}=o(X), \tag{40}
\]

and the extra `+1` main terms are `o(X)`.  Hence

\[
\frac{E_{L,r}(X)}X
\le\sum_{V<p\le U}\frac{\delta_{p,r}}p+o_r(1). \tag{41}
\]

For fixed `r`, `delta_{p,r}=4^(-r)(1+O_r(1/p))`, and the resulting
`sum p^(-2)` error tends to zero.  Mertens gives

\[
\limsup_{X\to\infty}\frac{E_{L,r}(X)}X
\le4^{-r}\log\frac{r+2}{r+1}. \tag{42}
\]

It remains to justify summation over `r`.  Using only the first `r` digits
and padded `p^r` blocks gives the uniform estimate

\[
E_{L,p,1}(X)\le3\frac Xp\rho_p^r. \tag{43}
\]

Since every relevant odd prime is at least `5`, we may use `rho_p<=2/3`.
Set

\[
J_X=\left\lfloor\frac{\log X}{2\log3}\right\rfloor-2.
\]

For `r<=J_X`, the lower band endpoint is at least `9`; (2) gives

\[
\sum_{X^{1/(r+2)}<p\le X^{1/(r+1)}}\frac1p
\le\log\frac{r+2}{r+1}+\frac{8(r+2)}{\log X}. \tag{44}
\]

After multiplying by `(2/3)^r`, the first terms have a convergent tail and
the second terms tend to zero for each fixed tail cutoff.  For `r>J_X`, the
bands are disjoint and

\[
\sum_{r>J_X}\sum_{p\text{ in band }r}\frac{\rho_p^r}{p}
\le(2/3)^{J_X+1}\sum_{p\le\sqrt X}\frac1p=o(1). \tag{45}
\]

The fixed primes `5,7` eventually lie here and are handled by (43), not by
Lemma 2.  Therefore

\[
\lim_{R\to\infty}\limsup_{X\to\infty}
\sum_{r>R}\sum_{p\text{ in band }r}\frac{\rho_p^r}{p}=0. \tag{46}
\]

Combining finitely many (42), then (46), then four branches gives

\[
\limsup_{X\to\infty}\frac{E_{\rm small}(X)}X\le4\mathcal S,
\quad
\mathcal S=\sum_{r=1}^\infty4^{-r}\log\frac{r+2}{r+1}. \tag{47}
\]

## 8. Transition range

For `sqrt X<p<=Y`, each branch contains at most `X/p+1` multiples of `p`.
Thus

\[
E_{\rm trans}(X)\le4X\sum_{\sqrt X<p\le Y}\frac1p+4\pi(Y). \tag{48}
\]

Mertens gives

\[
\sum_{\sqrt X<p\le Y}\frac1p
=\log\!\left(1+\frac{4\log\log X}{\log X}\right)
+O(1/\log X)=o(1),
\]

while `pi(Y)/X=O(log X/sqrt X)->0`.  Hence

\[
E_{\rm trans}(X)=o(X). \tag{49}
\]

## 9. Top-prime digit classification

Take `X` sufficiently large that `(log X)^4>130C_0` and `Y>43`.  If `p>Y`
and `L(x)=pc`, then

\[
\frac pc=\frac{p^2}{L(x)}>
\frac{Y^2}{C_0X}=\frac{(\log X)^4}{C_0}>130. \tag{50}
\]

In particular `p^2>L(x)`, so `p || L(x)`.

For P, let `r_0` be the least positive residue of `12c^2 mod 7`.  Unit
squares give `r_0` in `{3,5,6}`.  Writing `12c^2=7q+r_0`, the least digit is

\[
d_P=(r_0p-41c)/7.
\]

The inequality `2d_P<=p-1` always holds for `r_0=3` and contradicts (50)
for `r_0=5,6`.  Thus `c=3,4 mod 7` is necessary.

For Q, a unit `c mod 12` has `c^2=1 mod 12`; the least digit is

\[
d_Q=(7p+41c)/12,
\]

and `2d_Q-(p-1)=(p+41c+6)/6>0`.  No Q top obstruction exists.

For R, the least positive residue of `54c^2 mod 14` is in `{6,10,12}` and
the least digit is

\[
d_R=(r_0p+129c-7)/14.
\]

The lower-half inequality follows from (50) for `r_0=6` and is impossible
for `r_0=10,12`.  Exactly `c=5,9 mod 14` give residue `6`.

For S, the least digit is

\[
d_S=(7p-43c-6)/12,
\]

and `2d_S-(p-1)=(p-43c)/6>0`.  No S top obstruction exists.  We have proved

\[
P:c\equiv3,4\pmod7;\quad Q:\varnothing;\quad
R:c\equiv5,9\pmod{14};\quad S:\varnothing. \tag{51}
\]

## 10. Divisor switching

Write a relevant branch as `L(x)=Ax+d` and `Z=AX+d`.  If `Ax+d=pc`, then
`pc=d mod A`.  Since `gcd(d,A)=1`, both factors are units and

\[
p\equiv dc^{-1}\pmod A,qquad c\le Z/Y. \tag{52}
\]

For P, `A_P=42T=222138`; among its `phi(A_P)=60480` unit classes, exactly
`20160=phi(A_P)/3` reduce to `3,4 mod 7`.  For R,
`A_R=28T=148092`; exactly `13440=phi(A_R)/3` of its `40320` unit classes
reduce to `5,9 mod 14`.

We need one elementary summation lemma.  If `C` is a fixed set of classes
modulo fixed `A`, `delta=|C|/A`, `Y->infinity`, `Z/Y->infinity`, and
`log Z/log Y->2`, then

\[
\sum_{\substack{c\le Z/Y\\c\bmod A\in\mathcal C}}
\operatorname{Li}(Z/c)
=\delta Z\log\frac{\log Z}{\log Y}+o(Z). \tag{53}
\]

Indeed, the class counting function is `delta*u+O_A(1)`.  Partial summation
reduces the sum, up to `O_A(Li(Z))=o(Z)`, to
`delta integral_1^(Z/Y) Li(Z/t)dt`.  Uniformly for `Z/t>=Y`, integration by
parts gives

\[
\operatorname{Li}(Z/t)=\frac{Z/t}{\log(Z/t)}
+O\!\left(\frac{Z/t}{\log^2(Z/t)}\right).
\]

The main integral is `Z log(log Z/log Y)` and the error is
`O(Z/log Y)=o(Z)`, proving (53).

For P, every top event is counted by

\[
\sum_{\substack{c\le Z/Y\\c\bmod A_P\in\mathcal C_P}}
\big[\pi(Z/c;A_P,11c^{-1})-\pi(Y;A_P,11c^{-1})\big]. \tag{54}
\]

Dropping the lower cutoff gives an upper bound and introduces at most
`(Z/Y) pi(Y)=O(Z/log Y)=o(Z)` pairs.  Summing the error in (3) over `c`
gives at most

\[
K_{A_P}Z(1+\log(Z/Y))
e^{-\kappa_{A_P}\sqrt{\log Y}}=o(Z). \tag{55}
\]

Using (53) and `|C_P|=phi(A_P)/3`,

\[
E_{{\rm top},P}(X)
\le\frac{Z}{3A_P}\log\frac{\log Z}{\log Y}+o(Z).
\]

Since `Z/(A_PX)->1` and `log Z/log Y->2`,

\[
\limsup_{X\to\infty}\frac{E_{{\rm top},P}(X)}X\le\frac13\log2. \tag{56}
\]

The identical argument for R gives the same bound.  Q and S give zero, so

\[
\limsup_{X\to\infty}\frac{E_{\rm top}(X)}X\le\frac23\log2. \tag{57}
\]

## 11. Exact constant

From (22), (24), (28), (47), (49), and (57),

\[
\limsup_{X\to\infty}\frac{Bad(X)}X
\le4\mathcal S+\frac23\log2. \tag{58}
\]

For `0<x<1`,

\[
\log\frac{1+x}{1-x}
=2\sum_{j\ge0}\frac{x^{2j+1}}{2j+1}
<2\left(x+\frac{x^3}{3}\right)+\frac{2x^5}{5(1-x^2)}. \tag{59}
\]

Define, for `d>=3`,

\[
U(d)=2\left(\frac1d+\frac1{3d^3}\right)
+\frac{2}{5d^5(1-d^{-2})}.
\]

Then `log((d+1)/(d-1))<U(d)`.  Exact reduction gives

\[
(U(5),U(7),U(9),U(11),U(13),U(15))
\]

\[
=\left(\frac{3041}{7500},\frac{3947}{13720},
\frac{97603}{437400},\frac{24267}{133100},
\frac{142241}{922740},\frac{757123}{5670000}\right). \tag{60}
\]

For `r>=7`, `log((r+2)/(r+1))<=1/8`, hence its weighted tail is at most
`1/98304`.  Therefore

\[
\mathcal S<
\frac{11117760449158646497}{89848527388139520000}. \tag{61}
\]

Taking `x=1/3` in (59) gives `log2<1123/1620`.  Consequently

\[
4\mathcal S+\frac23\log2
<\frac{21498408212212214497}{22462131847034880000}. \tag{62}
\]

Finally,

\[
\frac{2393}{2500}
-\frac{21498408212212214497}{22462131847034880000}
=\frac{2344391769572639}{22462131847034880000}>0. \tag{63}
\]

Every rational identity in (60)-(63) is independently reproduced by
`verify.py` using `Fraction` only.

## 12. Conclusion

Let `Good(X)=X-Bad(X)`.  Equations (58) and (63) imply

\[
\liminf_{X\to\infty}\frac{Good(X)}X
=1-\limsup_{X\to\infty}\frac{Bad(X)}X
>1-\frac{2393}{2500}=\frac{107}{2500},
\]

which is (1).  Since `P(x),Q(x)` are positive and strictly increasing for
`x>=1`, so is `n_x=P(x)Q(x)-1`.  Distinct good parameters give distinct
consecutive pairs `(n_x,n_x+1)`.  Thus there are infinitely many consecutive
integers whose central binomial coefficients have identical prime support. ∎
