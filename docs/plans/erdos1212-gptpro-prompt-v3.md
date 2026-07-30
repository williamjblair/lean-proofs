# GPT Pro prompt v3 — the desert-counting problem (pure analytic NT)

Copy everything below the line. (Context for us, not for GPT Pro: this is the
single missing input identified by four convergent attempts on Erdős #1212;
the literature probe of 2026-07-30 found the tools below and no result at the
needed scale.)

---

This is a self-contained analytic number theory research problem. I am not
asking for exposition; I am asking you to prove the strongest theorem you can
in a precisely mapped gap in the literature.

**Setup.** Call $n$ **$z$-rough** if its least prime factor exceeds $z$. The
density of $z$-rough integers is $\prod_{p\le z}(1-1/p)\sim e^{-\gamma}/\log z$,
so the average gap between consecutive $z$-rough integers is
$\sim e^{\gamma}\log z$. Call a maximal run of consecutive integers containing
no $z$-rough integer a **$z$-desert**, and its length $T$. By
Rankin/Ford–Green–Konyagin–Maynard–Tao lower bounds for Jacobsthal's function,
deserts of length $T\gg z\log z\log\log z/(\log\log\log z)^2$ exist; by
Iwaniec (Demonstratio Math. 11 (1978) 225–232), $T\ll z^2$ always.

**The problem.** Prove an unconditional upper bound on the **number of
$z$-deserts of length $\ge T$ with starting point in a dyadic window
$[X,2X]$**, of the form
$$N(X;z,T)\ \ll\ \frac{X}{T}\cdot\rho(T/\log z),$$
with $\rho$ decaying as fast as you can prove, **uniformly in as large a
$T$-range as you can reach** — the prize range is $T$ up to $z^{1+o(1)}$, and
$X$ may be assumed enormous relative to $z$ (think $\log X\asymp z^{\alpha}$,
any fixed $\alpha>0$ you need). Weaker but still valuable: any localized bound
beating the trivial $N\le X/T$ by a growing factor for $T\ge K\log z$ with
moderate $K$.

**The literature map — start from these; do not rediscover them.**
1. Montgomery–Vaughan, *On the distribution of reduced residues*, Ann. of
   Math. 123 (1986) 311–333: $k$-th moment bounds for the count of reduced
   residues mod $q$ in intervals of length $h$:
   $M_k(q;h)\ll_k(hP+(hP)^{k/2})q$, $P=\varphi(q)/q$. Taking $q=P(z)=
   \prod_{p\le z}p$, reduced residues mod $q$ *are* the $z$-rough pattern.
   Markov then bounds per-period desert counts with arbitrary fixed
   polynomial decay in $T/\log z$. **Two known deficiencies**: constants are
   not uniform in $k$ (nobody has published the uniformity needed to optimize
   $k$ with $T$), and the bound is per full period $P(z)=e^{(1+o(1))z}$ — it
   says nothing about a single dyadic window $[X,2X]$ with $X\ll P(z)$, where
   in the worst case the period's deserts could cluster. Bloom–Kuperberg
   (arXiv:2312.09021, Proc. LMS 2025) complete the odd-moment picture, still
   fixed $k$.
2. Gorodetsky, *The variance of integers without small prime factors in short
   intervals*, arXiv:2111.00853 (Math. Z. 2024): unconditional **dyadically
   localized** variance for $z$-rough counts in short intervals. This is the
   localization technology at the second-moment level; by Chebyshev it already
   beats trivial slightly above the mean gap, but one power of savings dies
   far below $T\asymp z$.
3. **The proof template one scale down — read this first**: Gafni–Tao,
   *Rough numbers between consecutive primes*, arXiv:2508.06463 (Aug 2025).
   They bound, unconditionally, the number of prime gaps in $[X,2X]$
   containing no $\sqrt X$-rough integer by $\ll X/\log^2X$, using Montgomery
   (1970) second moments plus Montgomery–Soundararajan (Comm. Math. Phys. 252
   (2004)) higher moments **of sifted sets, localized in dyadic ranges**. This
   is exactly the shape of argument needed, executed at gap scale
   $T\asymp\log X$. Your task, in essence: determine how far the
   Montgomery–Soundararajan moment method can be pushed in $T$ (optimizing
   the moment order $k$ against $T/h$ and tracking the $k$-dependence of all
   constants explicitly — this is where the non-uniformity has stopped
   everyone), and extract the strongest localized desert count it yields.
   If the constants permit $k\to\infty$ slowly, the natural target is a bound
   like $\rho(u)=\exp(-cu^{1/2})$ or better in some range $T\le z^{\theta}$;
   state precisely the range and decay you can defend.

**Rules.** Referee standard. Track every constant's dependence on $k$
explicitly — the entire difficulty is quantitative uniformity, and a proof
that silently uses "$\ll_k$" in a range where $k$ grows is invalid. If the
method caps at some $T_{\max}(z)$, prove your best theorem there and state the
cap as a theorem too ("beyond $T_{\max}$ the moment method gives nothing
because ..."). Partial results are valuable: even $T\le\log^{100}z$ with
super-polynomial decay would be new and useful. If you find the needed
uniform-in-$k$ moment bounds already in print somewhere I missed, cite
exactly and assemble.

**Why this matters (one paragraph, so you know the stakes; do not spend
effort here).** This statement is the missing input for Erdős problem #1212:
a trajectory argument with $\sim z/\mathrm{polylog}$ placement freedom per
step needs to dodge deserts; average-case margins are enormous
(average gap $21$ vs desert length $3.5\times10^6$ at $z=10^5$), and the only
missing piece is knowing deserts near the Jacobsthal scale are *rare in every
window*, not just on average over the period. Any nontrivial localized
rarity bound feeds directly into a resolution of that problem, and the
desert-counting theorem would also be of independent interest (it is the
natural "upper-bound side" of the Jacobsthal problem, where all published
work is on lower bounds).
