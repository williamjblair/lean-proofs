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
