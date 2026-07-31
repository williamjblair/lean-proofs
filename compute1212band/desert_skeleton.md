# The desert-counting theorem: a complete proof skeleton (2026-07-30)

Status: **strategy with verified numerology, NOT a proof.** Everything reduces
to Lemmas L1–L2 below; both are stated precisely, both feel provable by
elementary (if laborious) methods, neither is proved here. Two traps that
break naive versions are documented (§4) — I fell into both and climbed out.

## 1. Target

For $z$ large, $\delta=\prod_{p\le z}(1-1/p)\sim e^{-\gamma}/\log z$, window
$[X,2X]$ with $\log X\asymp z^{\alpha}$, $0<\alpha<1$ fixed. Let $N_T(x)$
count $z$-rough integers in $(x,x+T]$. Claim to prove:

$$\#\{x\in[X,2X]:N_T(x)=0\}\ \ll\ X^{1-c(\alpha)}\qquad(T\ge z^{\alpha}\,C),$$

in particular at the Jacobsthal-relevant scale $T\asymp z$. This is exactly
the rarity input of `final_reduction.md`, and with it SCH and hence
Erdős #1212 follow via Theorem D.

## 2. The route and its numerology (verified twice, symbolically)

Markov on the $k$-th **central** moment:
$$\#\{N_T=0\}\le\frac1{(\delta T)^k}\sum_{x\in[X,2X]}(N_T(x)-\delta T)^k
\;\le\;X\cdot\Big(\frac{C\,k}{\delta T}\Big)^{k/2}$$
granted the moment bound of L2. Choose
$$k=\Big\lfloor\varepsilon\,\frac{\log X}{\log T}\Big\rfloor\asymp
\varepsilon\,\frac{z^{\alpha}}{\log z}.$$
At $T=z$: $\ \delta T\asymp z/\log z$, so
$k/\delta T\asymp\varepsilon e^{\gamma}z^{\alpha-1}\ll1$ (Gaussian regime,
$k\ll\delta T$, as required), and
$$\Big(\frac{Ck}{\delta T}\Big)^{k/2}
=\exp\Big(-\tfrac{1-\alpha}2(1+o(1))\,\varepsilon z^{\alpha}\Big)
=X^{-\varepsilon(1-\alpha)/2}.$$
**Power saving in $X$** — far more than the dodge argument needs
($\ll X/z$ suffices). The needed moment order is only
$k\asymp\log X/\log z$: this is why localization is compatible with high
moments — the whole point of the skeleton.

Error-side consistency: expanding correlations by inclusion–exclusion over
divisors of $P(z)$ truncated at joint modulus $\le X^{1-\varepsilon}$ forces
per-factor level $y=X^{(1-\varepsilon)/k}=z^{(1-\varepsilon)/\varepsilon}$ — a
**fixed power of $z$**, so fundamental-lemma accuracy per factor is a constant
$e^{-C'}$, and the accumulated relative error over $k$ factors is
$\exp(k e^{-C'})=\exp(\varepsilon e^{-C'}z^{\alpha}/\log z)$, negligible
against the main saving $\exp(\varepsilon(1-\alpha)z^{\alpha}/2)$ whenever
$e^{-C'}\le(1-\alpha)(\log z)/4$ — true for all large $z$. The numerology
closes with room at every joint.

## 3. The two load-bearing lemmas (open)

**L1 (windowed correlations).** For distinct shifts $d_1<\dots<d_j\le T$,
$j\le k$, with $S_j(d)=\prod_p\big(1-\omega_p(d)/p\big)$ ($\omega_p$ =
number of distinct residues of the $d_i$ mod $p$, product over $p\le z$):
$$\frac1X\sum_{x\in[X,2X]}\prod_{i\le j}1_{\mathrm{rough}}(x+d_i)
=S_j(d)\,\big(1+O(je^{-C'})\big)+O\!\big(X^{-\varepsilon'}\big),$$
uniformly for $j\le k$, via fundamental-lemma majorants/minorants at level
$y$ per factor and the joint-modulus truncation $\mathrm{lcm}\le
X^{1-\varepsilon}$. Elementary; the work is bookkeeping the $j$-fold
remainder sums. I regard L1 as safe.

**L2 (uniform centered moments — the crux).** With correlations from L1,
$$\frac1X\sum_{x}(N_T(x)-\delta T)^k\le(C\,k\,\delta T)^{k/2}
\qquad\text{uniformly for }k\le\delta T/C.$$
Equivalent to uniform-in-$j$ cancellation in the centered singular-series
sums $V_j(T)=\sum_{d}\big(S_j(d)-\delta^{j}\big)$-type objects — exactly the
sums Montgomery–Vaughan (1986) control per-period with non-uniform constants
and Montgomery–Soundararajan (2004) control for the prime singular series.
For the *rough-number* sieve the natural identity
$N_T-\delta T=\sum_{1<d\mid P}\mu(d)E_d(x)$, $E_d=\#\{i\le T:d\mid x+i\}-T/d$,
$|E_d|\le1$, reduces L2 to moment bounds for short divisor sums — laborious
but elementary in character. **This is the single remaining mathematical
obstacle to Erdős #1212** on the current route.

## 4. Two traps (documented so nobody re-falls)

1. **Bonferroni fails.** Truncated inclusion–exclusion on
   $\prod_i(1-1_{\mathrm{rough}}(x+i))$ at depth $k\ll\delta T$ gives bounds
   of size $(e\delta T/k)^k$ — astronomically large, useless. Centering is
   essential; only central moments see the cancellation.
2. **Sieve minorants don't multiply.** $\theta\le1_{\mathrm{rough}}$
   pointwise does *not* give $\prod(1-1_{\mathrm{rough}})\le\prod(1-\theta)$,
   because minorants take negative values. Any product manipulation must go
   through the exponential/moment route, not termwise domination.

## 5. Assembly (conditional chain, all pieces previously proved)

L1 + L2 $\Rightarrow$ desert rarity ($\S2$) $\Rightarrow$ the trajectory
dodge has $X^{c}$ headroom per dyadic block $\Rightarrow$ SCH
$\Rightarrow$ (Theorem D) the seed's component is infinite
$\Rightarrow$ **Erdős #1212 is YES.** The dodge step still needs its own
referee-standard write-up (the trajectory's placement freedom must be shown
independent of desert positions — with power-saving rarity this is expected
to be routine, but "expected routine" is not "proved").

## 6. Relation to prompt v3

This skeleton *sharpens* v3: GPT Pro should be pointed at L2 specifically
(with L1 assumed or proved en route), told the exact $k$-range
$k\asymp\log X/\log T$ (modest — uniformity is needed far below $\delta T$,
which is easier than the general problem), and given the two traps.

## 7. The β-framework for L2 (derived and verified 2026-07-30, late)

Write $\beta_p(n)=1_{p\mid n}-1/p$. Then $1_{\mathrm{rough}}(n)=
\prod_{p\le z}((1-1/p)-\beta_p(n))$, and expanding,
$$N_T(x)-\delta T=\delta\sum_{d\mid P,\,d>1}(-1)^{\omega(d)}
\prod_{p\mid d}(1-1/p)^{-1}\,W_d(x),\qquad
W_d(x)=\sum_{i\le T}\prod_{p\mid d}\beta_p(x+i).$$
Three verified structural facts (numerically checked for p ∈ {3,5,7,11,13},
all exact):

1. **Orthogonality / single-prime vanishing.** $\mathbb E_p[\beta_p]=0$, and
   over full periods correlations factor over distinct primes (CRT). Hence in
   any $k$-fold correlation, **a prime appearing in exactly one $d_j$ kills
   the term**: only configurations where every prime is shared by ≥ 2 indices
   survive. This is the source of the Gaussian structure.
2. **Exact local factors.** For shifts occupying $r$ distinct residues mod
   $p$ with multiplicities $m_1..m_r$:
   $$\mathbb E_p\Big[\prod_s\beta_p^{m_s}(x{+}a_s)\Big]
   =\sum_{s_0}\frac1p\Big(1-\frac1p\Big)^{m_{s_0}}
   \prod_{s\ne s_0}\Big(-\frac1p\Big)^{m_s}
   +\Big(1-\frac rp\Big)\prod_s\Big(-\frac1p\Big)^{m_s}.$$
   In particular the pair value is $(1/p)(1-1/p)$ for congruent shifts and
   $-1/p^2$ otherwise — each congruence collision costs one factor $1/p$.
3. **Small-prime cancellation is pointwise, not statistical.**
   $|W_p(x)|=|\#\{i\le T:p\mid x{+}i\}-T/p|<1$ for every $x,p,T$. The naive
   fear that small primes contribute $(T/p)^m$-sized clusters is unfounded:
   shift-sums must be performed inside the local factors, where the
   $r$-collision structure carries the decay. (I fell into the $(T/2)^m$
   trap before noticing this — recorded as trap #3.)

**What remains for L2**, now fully specified: organize the $k$-fold sum over
$(d_1..d_k)$ by the partition into connected prime-sharing clusters; bound
each connected $m$-cluster's total mass by $m!\,C^m\,\delta T$-type cumulant
estimates using the local factors above (the dominant mass is shift-collision
pairings, total pair mass $=\sigma^2\asymp\delta T$); handle the
window-vs-period truncation ($\mathrm{lcm}\le X^{1-\varepsilon}$ exact,
tail via pointwise bounds and divisor counts); conclude
$M_k\le(Ck\sigma^2)^{k/2}$ for $k\le\delta T/C$ by the standard
cumulant-to-moment inequality. All four steps are standard-technique-shaped;
the content is uniformity bookkeeping, no longer ideas.

## 8. Session-final state (2026-07-30, night): the minorant reformulation

Salvaged from a 30-minute deep-reasoning attempt (agent transcript mined;
its response overflowed but the reasoning survived):

- **(S1) Endgame robustness.** The Markov endgame closes for every α<1 even
  with moment bounds as weak as $(Ck\log k\,\delta T)^{k/2}$ and with the
  $k$-range shrunk by polylog factors. The route has slack; only genuine
  structure can kill it.
- **(S2) Absolute values lose.** The off-diagonal absolute mass is
  $\asymp\delta^2T^2$: any argument that bounds the correlation sums in
  absolute value overshoots by a factor $\delta T$. Signed cancellation
  per divisor is mandatory.
- **(S3) The exact-centering wall.** Decomposing $1_{\mathrm{rough}}$ into a
  level-$D$ approximant plus sparse remainder forces
  $\log D\asymp\log^2z/\log\log z$ (the remainder's $k$-norm is dominated by
  its mean), shrinking $k$ by $\log z/\log\log z$ — survivable for the
  endgame but ugly.
- **(S4) Tree elimination.** Sequential variable elimination with
  cancellation works exactly on tree-structured interaction hypergraphs;
  cycles couple the eliminated factors. Trees must dominate by cycle
  suppression ($1/p$ per independent cycle), not by elimination alone.

**The reformulation that dissolves (S3).** Do not decompose
$1_{\mathrm{rough}}$ at all. Use a Brun/Bonferroni **minorant** of bounded
level: $\theta_m(n)=\sum_{d\mid(n,P),\,\omega(d)\le m}\mu(d)$ with $m$ odd
satisfies $\theta_m\le1_{\mathrm{rough}}$ **pointwise** (verified: 0
violations on $[2,2\times10^5]$ at $z=31,m=3$), has level $\le z^m$ and mean
$\mu_\theta\ge c_m\,\delta$ with $c_3\approx0.58$ measured. Then
$$N_T(x)=0\ \Longrightarrow\ N_{\theta}(x)\le0\ \Longrightarrow\
|N_\theta(x)-\mu_\theta T|\ge\mu_\theta T,$$
and Markov needs only the central moments of $N_\theta$ — a divisor sum of
**bounded level $z^{O(1)}$**, fully localizable with the full $k$-range
$k\asymp\varepsilon\log X/\log z$ (joint moduli $\le z^{mk}\le X^{1-\varepsilon}$).
No exact centering, no sparse tail, no fundamental-lemma accuracy demand
beyond "mean bounded below" ($m=3$ suffices).

**Empirical calibration** ($z=31$, $T=62$, 4000 windows at $10^7$):
$\sigma^2=9.4\approx\delta T=9.5$; $M_k/(2k\sigma^2)^{k/2}=0.25,\ 0.075,\
0.037$ for $k=2,4,6$ — Gaussian with growing margin.

**The one remaining estimate**, in final form: for $\theta=\theta_3$ (level
$z^3$, coefficients $\mu(d)$, $\omega(d)\le3$),
$$\frac1X\sum_{X<x\le2X}\Big(\sum_{i\le T}\theta(x+i)-\mu_\theta T\Big)^{k}
\le(Ck\,\delta T)^{k/2},\qquad k\le\varepsilon\frac{\log X}{\log z},$$
proved via the β-framework (§7) cluster expansion: single-prime vanishing
kills unshared primes; local factors are exact; trees dominate by (S4) with
cycles suppressed by $1/p$ per cycle; window-vs-period error is
$O(z^{3k}/X)$ per configuration. This is a classical-type moment estimate
for a bounded-level sieve sum — the last opening between here and
Erdős #1212.
