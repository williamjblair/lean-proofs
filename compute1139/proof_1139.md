# Erdős Problem #1139: gaps between integers with at most two prime factors

**Working document — full technical record.**
Date: 2026-07-30. Working directory: `/Users/williamblair/personal/lean-proofs/compute1139/`.

---

## 0. The problem and its canonical reading

**Statement** (erdosproblems.com/1139, source [Va99, 1.4]). Let $1 \le u_1 < u_2 < \cdots$ be the
sequence of integers with at most $2$ prime factors. Is it true that
$$\limsup_{k\to\infty} \frac{u_{k+1}-u_k}{\log k} = \infty\,?$$

**Canonical formalization** (google-deepmind/formal-conjectures, `ErdosProblems/1139.lean`, fetched
2026-07-30): the sequence is `Nat.nth (fun n ↦ 0 < n ∧ Ω n ≤ 2)` and the question is whether
$$\limsup_{k\to\infty}\frac{u_{k+1}-u_k}{\log(k+1)} = \top \quad\text{in }\overline{\mathbb R}.$$
So the canonical reading is:

* **prime factors counted with multiplicity**: $\Omega(n)\le 2$. The sequence is
  $\{1\} \cup \{\text{primes}\} \cup \{p^2\} \cup \{pq\}$ — OEIS **A037143** ($1,2,3,4,5,6,7,9,10,11,13,\dots$),
  counting function **A101041**, $\#\{n\le x: \Omega(n)\le 2\} \sim x\log\log x/\log x$ (Landau).
* $1$ is included ($\Omega(1)=0$); indexing off-by-ones ($\log k$ vs $\log(k+1)$, `Nat.nth` 0-indexing)
  are immaterial for the limsup (Section 2.4).
* Since $\{n:\omega(n)\le 2\} \supsetneq \{n:\Omega(n)\le 2\}$, the distinct-prime-factor variant is a
  *different (harder) statement*; we treat $\Omega$ as primary per the formalization and close the
  $\omega$-variant's reduction separately (Theorem A′).

**Answer targeted: YES** (this is what the community expects and what the sole claimed proof asserts).

---

## 1. Phase 0 — literature and community state (verdict)

Fetched 2026-07-30: problem page, forum thread (10 comments), proof-claims page, OEIS A037143/A101041,
MathOverflow 106682 and 233042, FKMPT *Long gaps in sieved sets* (JEMS 23 (2021) 667–700,
`ems32526.pdf` in this directory), the Chojecki note (`erdos1139-short.pdf`), the gavinsherry
reduction gist.

**Published literature: no nontrivial lower bound exists.**
* MathOverflow 233042 ("Large gaps between almost primes", 2016, restated 2017) asks exactly for the
  longest interval in $[1,x]$ free of primes and products of two primes; it has **no answer** as of
  today. MathOverflow 106682 concerns the *upper*-bound side (Halberstam–Heath-Brown–Richert 1981:
  $(x-x^{0.455},x]$ contains $\gg x^{0.455}/\log x$ integers that are $P_2$; refinements by
  Iwaniec–Laborde, Luo). Upper bounds are irrelevant to #1139 except as context.
* Woett (forum, 24 Jan 2026) reports an extensive automated literature sweep found *no* nontrivial
  lower bound for $\max_{u_k\le x}(u_{k+1}-u_k)$. My own searches (arXiv/web, July 2026) likewise
  found nothing beyond the prime-gap literature (Westzynthius 1931; Erdős 1935; Rankin 1938;
  Maynard, Ann. of Math. 183 (2016); Ford–Green–Konyagin–Tao, Ann. of Math. 183 (2016);
  Ford–Green–Konyagin–Maynard–Tao, J. Amer. Math. Soc. 31 (2018); FKMPT JEMS 23 (2021)).
  **Note**: the FKMPT sieved-sets theorem is one-dimensional ($|I_p|$ bounded, $\approx 1$ on average)
  and does **not** black-box apply here (see §4).

**Community/forum state (decisive for status):**
1. **One claimed full proof**, submitted **2026-07-15** by *Liam Price (using GPT Pro)*, affirmative.
   External link: Overleaf read-link `overleaf.com/read/jcrjsxtwpvqc` (JS-walled; not retrievable in
   this environment — attempted via curl, WebFetch, and a browser pane; the associated ChatGPT share
   `chatgpt.com/share/6a3570e7-…` titled "Erdos problem 1139 Price check" is now login-gated).
   A detailed strategy digest is in Price's 19 Jun 2026 comment (analyzed in §6).
   *Nat Sothanaphan* (19 Jun 2026) ran a "screening check" finding "no issues" plus one typo (p. 12).
   Zero comments on the formal claim page; the site explicitly disclaims verification; the problem
   is still listed **OPEN** (page last edited 23 Jan 2026).
2. **Terence Tao** (28 Jan 2026), on the split-Rankin idea (Chojecki's note, `erdos1139-short.pdf`,
   which splits primes into $1$ and $3 \bmod 4$ and asserts a covering Lemma 1 in each class):
   *"I find it unlikely that Lemma 1 will be easy to prove. With only half the primes available for
   sieving, the standard Rankin trick of reducing to mostly smooth numbers or (almost) primes no
   longer works, and also the power of random sieving is also diminished."* My independent
   quantitative confirmation is §4 below.
3. **gavinsherry** (29 Apr 2026): a careful note (gist, saved) proving the two sufficient covering
   criteria (equivalent to my Theorem A below, which I derived independently before reading it) and
   the sieve-dimension caveat about FKMPT. Explicitly *not* a solution.
4. **Erdős #689** is the non-sparse core: choose $a_p \bmod p$ for *all* $p\le n$ so that every
   $m\in[1,n]$ satisfies at least two congruences. Any sparse 2-cover in the sense of Theorem A with
   primes $\le n$ and $Y=n$ implies #689 (pad the unused primes with arbitrary classes — extra
   coverage only helps). The converse fails: #689 has weight $\theta(n)\sim n$, useless for #1139,
   which needs weight $o(Y)$. #689 also has a claimed proof (30 comments; same circle of
   contributors). Tao: "the core is the same or very similar".

**Verdict.** Not solved in the published literature. One unvetted claimed proof (Green–Tao-based,
right shape — see §6), inaccessible in full from this environment. The problem's elementary content
(reduction + baseline) is fully provable and is proved below; the analytic core is genuinely at the
level of the modern large-prime-gap machinery.

---

## 2. Theorem A: the covering reduction (complete proof)

All logs are natural. $\Omega$ counts prime factors with multiplicity. $A_2:=\{n\ge 1:\Omega(n)\le 2\}$,
$u_k$ its increasing enumeration ($u_1=1$).

**Definition (sparse forced-factor system).** A *system* is a finite set $S$ of primes, exponents
$e_p\in\{1,2\}$, and an integer $c\ge 0$. Its *modulus* is $M:=\prod_{p\in S}p^{e_p}$, its *weight*
$L:=\log M=\sum_{p\in S}e_p\log p$. For $n\ge 1$ define the *forced count*
$$W(n) := \sum_{p\in S}\min\bigl(v_p(c+n),\,e_p\bigr),$$
where $v_p$ is the $p$-adic valuation (note $c+n\ge 1$, so $W$ is well defined).

**Theorem A.** Suppose that for every $j\in\mathbb N$ there exist $Y_j\to\infty$ and a system
$(S_j,e_j,c_j)$ with
1. $W_j(n)\ge 2$ for every integer $1\le n\le Y_j$, and
2. $L_j = o(Y_j)$ as $j\to\infty$.

Then $\displaystyle\limsup_{k\to\infty}\frac{u_{k+1}-u_k}{\log k}=\infty$ (equally with denominator
$\log(k+1)$, and equally for the 0-indexed `Nat.nth` version).

*Proof.* Fix $j$; drop subscripts. Let $N$ be the least integer with $N\equiv c \pmod M$ and $N>M^2$;
then $M^2 < N \le M^2+M$.

**(i) Forced divisor.** For $p\in S$ we have $p^{e_p}\mid M \mid N-c$, hence
$N+n \equiv c+n \pmod{p^{e_p}}$, so
$$v_p(N+n) \ \ge\ \min\bigl(v_p(c+n),e_p\bigr) \qquad (p\in S).$$
(If $v_p(c+n)\ge e_p$, then $p^{e_p}$ divides both $c+n$ and $N-c$, hence $N+n$; if
$v_p(c+n)=t<e_p$, then $p^t$ divides both, giving $v_p(N+n)\ge t$.) Therefore
$d_n := \prod_{p\in S}p^{\min(v_p(c+n),e_p)}$ divides $N+n$, with
$\Omega(d_n)=W(n)\ge 2$ and $d_n \le M$.

**(ii) Third factor.** For $1\le n\le Y$: $\dfrac{N+n}{d_n} \ge \dfrac{N}{M} > M \ge d_n \ge 1$, and in
particular $(N+n)/d_n > 1$ is an integer, so
$$\Omega(N+n) \;=\; \Omega(d_n) + \Omega\!\Bigl(\tfrac{N+n}{d_n}\Bigr)\;\ge\; 2+1 \;=\;3 .$$
Hence $(N, N+Y] \cap A_2 = \emptyset$.

**(iii) Gap.** Let $k$ be the largest index with $u_k\le N$ ($k$ exists: $u_1=1\le N$). Then
$u_{k+1} > N+Y$, so $u_{k+1}-u_k \ge Y+1 > Y$.

**(iv) $k\to\infty$.** First, $M > Y$. Indeed, if $M\le Y$ then $[1,Y]$ contains a full residue
system mod $M$, so $W(n)\ge 2$ for **all** integers $n$ (as $W(n)$ depends only on
$n \bmod M$ — note $\min(v_p(c+n),e_p)$ is determined by $c+n \bmod p^{e_p}$); by (i)–(ii) applied to
arbitrarily large $n$, every sufficiently large integer would have $\Omega\ge 3$, contradicting the
infinitude of primes. Hence $N > M^2 > Y^2 \to\infty$, and $k\to\infty$ (if $k_j\le B$ along a
subsequence then $u_{k_j+1}\le u_{B+1}<\infty$, contradicting $u_{k_j+1}>N_j\to\infty$).

**(v) Normalization.** $k \le u_k \le N \le M^2+M$, so
$$\log k \ \le\ \log N \ \le\ 2\log M + 1 \ =\ 2L+1 .$$
Therefore, along $j$:
$$\frac{u_{k+1}-u_k}{\log k} \ \ge\ \frac{Y}{2L+1}\ \xrightarrow{\ j\to\infty\ }\ \infty ,$$
by hypothesis 2. Since $k=k_j\to\infty$, the ratio is frequently arbitrarily large, i.e.
$\limsup_k = \infty$. With denominator $\log(k+1)\le 2L+2$ the same bound holds; the 0-indexed
version differs by a single index shift. $\blacksquare$

**Remarks.**
* No prime-counting input at all is needed for Theorem A — not even Chebyshev. The frequently-used
  "choose $N\in(Y^2, Y^2+M]$" variant (gavinsherry's Claim 2) needs all covering primes $\le Y$;
  taking $N>M^2$ removes that restriction and permits moduli of any size.
* Hypothesis 1 with $e_p\equiv 1$ is the "two distinct primes" 2-fold cover; $e_p=2$ lets a single
  prime contribute both units (the $p^2\mid c+n$ trick), which is essential for cheap stage-0
  forcing (§5).

**Theorem A′ ($\omega$-variant).** If in addition, for every $n\in[1,Y]$ there are **three distinct**
primes $p\in S$ with $v_p(c+n)\ge 1$, then the same construction gives $\omega(N+n)\ge 3$, so the
analogous limsup for the sequence of integers with $\omega\le 2$ is also infinite. *Proof identical*
(three distinct forced prime divisors survive regardless of multiplicities; the cofactor argument is
not needed). Note the $p^2$ trick does *not* help $\omega$: the $\omega$-variant genuinely requires a
3-fold distinct-prime cover and is strictly more demanding. (This matches gavinsherry's Claim 1.)

So the problem is **reduced to a finite combinatorial statement**: *2-fold sparse covering with
log-weight $o(Y)$.* Everything below concerns producing such systems.

---

## 3. Theorem B: the baseline one-fold Rankin–Erdős cover (complete proof)

This is the classical input the task's "split" would need, in the weakest form with full rigor and
explicit constants. It gives a **one**-fold cover of weight $o(Y)$ — the object that provably exists.

**Notation.** $\log_2 x:=\log\log x$, $\log_3 x:=\log\log\log x$; $\theta(x)=\sum_{p\le x}\log p$;
$\pi(x)$ the prime counting function; $\Psi(Y,z):=\#\{n\le Y:\ p\mid n\Rightarrow p\le z\}$.

**External inputs** (all classical, explicit, elementary-effective):
* (E1) Rosser–Schoenfeld (Illinois J. Math. 6 (1962)): $\pi(t) < 1.25506\,t/\log t$ for $t>1$;
  $\pi(t) > t/\log t$ for $t\ge 17$; $\theta(t) < 1.01624\,t$ for $t>0$;
  $\pi(2t)-\pi(t) > \tfrac{3t}{5\log t}$ for $t\ge 20.5$.
* (E2) Mertens with error (Rosser–Schoenfeld):
  $\prod_{p\le t}(1-1/p) = \frac{e^{-\gamma}}{\log t}\bigl(1+\varepsilon(t)\bigr)$ with
  $|\varepsilon(t)|\le \frac{1}{2\log^2 t}$ for $t\ge 285$; and
  $\sum_{p\le t}\frac1p \le \log_2 t + 0.2615 + \frac{1}{\log^2 t}$ for $t\ge 2$ (define
  $\log_2 t$ suitably for small $t$).

**Lemma B1 (Rankin's trick, explicit).** For $z\ge z_0$ (absolute) and any $Y\ge z$,
with $u:=\log Y/\log z$:
$$\Psi(Y,z) \ \le\ C_R\, Y\, e^{-10u} (\log z)^{6}, \qquad C_R := e^{1.2 e^{11}} \text{ (absolute)}.$$

*Proof.* For any $\sigma\in(0,1)$:
$\Psi(Y,z) \le \sum_{n\ z\text{-smooth}} (Y/n)^{\sigma} = Y^{\sigma}\prod_{p\le z}\bigl(1-p^{-\sigma}\bigr)^{-1}$.
Take $\sigma = 1-\frac{10}{\log z}$ (so $\sigma\ge 0.9$ once $\log z\ge 100$). Using
$-\log(1-t)\le t/(1-t)$ and $p^{-\sigma}\le 2^{-0.9}$:
$$\log \prod_{p\le z}\bigl(1-p^{-\sigma}\bigr)^{-1} \ \le\ 2.2 \sum_{p\le z} p^{-\sigma}
 \ =\ 2.2 \sum_{p\le z} \frac{e^{10\log p/\log z}}{p}.$$
Split at $z^{1/10}$: for $p\le z^{1/10}$ the exponential is $\le e$, contributing
$\le e(\log_2 z + 1.3)$ by (E2); for $z^{1/10}<p\le z$ it is $\le e^{10}$, and
$\sum_{z^{1/10}<p\le z}1/p \le \log 10 + o(1) \le 2.4$ by (E2), contributing $\le 2.4\,e^{10}$.
Hence $\log\prod \le 6\log_2 z + 1.2e^{11}$ (absorbing constants), while
$Y^{\sigma} = Y e^{-10u}$. $\blacksquare$

**Theorem B (one-fold sparse cover).** There is $x_0$ such that for all $x\ge x_0$, setting
$$F(x) := \frac{\log x}{8(\log_2 x)^2}, \qquad Y := \lfloor F(x)\, x\rfloor,$$
there exist residues $a_p \pmod p$ for the primes $p\le x$ such that every integer $n\in[1,Y]$
satisfies $n\equiv a_p \pmod p$ for some $p\le x$. The weight is
$\sum_{p\le x}\log p = \theta(x) \le 1.02\,x = o(Y)$, and $Y/x = F(x)\to\infty$.

*Proof.* Put $w:=\log x$, $z:=x^{1/\log_2 x}$ (so $\log z = \log x/\log_2 x$), and partition the
primes $\le x$ into
$$T:=\{p\le w\},\quad M:=\{w<p\le z\},\quad V:=\{z<p\le x/4\},\quad
  V':=\{x/4<p\le x/2\},\quad R:=\{x/2<p\le x\}.$$

**Step 1 (zeros).** Set $a_p=0$ for $p\in T\cup V$. An $n\in[1,Y]$ is then uncovered only if $n$ has
no prime factor in $[2,w]\cup(z,x/4]$.
Since $Y \le x\log x < (x/4)^2$ for large $x$, $n$ has at most one prime factor $>x/4$.
* If $n=qm$ with a prime $q>x/4$: then $m \le Y/(x/4) = 4F(x) \le \log x = w$ for large $x$
  (as $4F = \log x/(2(\log_2 x)^2) \le \log x$). If $m>1$, $m$ has a prime factor $\le m\le w$, so
  $n$ is covered by $T$. Hence $m=1$ and $n=q$ is a **prime in $(x/4, Y]$**. Call this set $B$.
  By (E1), $|B| \le \pi(Y) \le 1.25506\,Y/\log Y \le 1.26\,Y/\log x$.
* Otherwise every prime factor of $n$ lies in $(w,z]$; in particular $n$ is $z$-smooth. Call this
  set $A$ (it contains $n=1$). By Lemma B1 with
  $u = \log Y/\log z \ge \log_2 x$:
  $$|A| \ \le\ C_R\, Y e^{-10\log_2 x}(\log z)^6 \ \le\ C_R\, \frac{Y}{(\log x)^{10}}(\log x)^6
    \ =\ C_R\,\frac{Y}{(\log x)^4} \ \le\ \frac{x}{\log x}\cdot\frac{C_R}{8(\log x)(\log_2 x)^2},$$
  which is $\le 0.001\,x/\log x$ for $x\ge x_0(C_R)$.

**Step 2 (greedy pigeonhole on $B$).** Process the primes $p\in M$ in any order; maintain the set
$B^{(i)}$ of still-uncovered elements of $B$. For each $p$, choose $a_p$ to be a residue class mod
$p$ containing at least $\lceil |B^{(i)}|/p\rceil$ elements of $B^{(i)}$ (one exists, by pigeonhole
over the $p$ classes); remove them. Then
$$|B^{(\mathrm{end})}| \ \le\ |B| \prod_{p\in M}\Bigl(1-\frac1p\Bigr)
 \ \le\ 1.26\,\frac{Y}{\log x}\cdot \frac{\log w}{\log z}\Bigl(1+\frac{2}{\log^2 w}\Bigr)
 \ \le\ 1.4\,\frac{Y (\log_2 x)^2}{(\log x)^2}$$
for large $x$, using (E2) twice ($\prod_{w<p\le z}(1-1/p) = \prod_{p\le z}/\prod_{p\le w}$). With
$Y \le x\log x/(8(\log_2 x)^2)$ this is $\le 0.175\, x/\log x$.

**Step 3 (individual patches).** Uncovered so far: $\le |A| + |B^{(\mathrm{end})}| \le 0.18\,x/\log x$
elements. By (E1), $|R| = \pi(x)-\pi(x/2) \ge \tfrac{3}{5}\cdot\tfrac{x/2}{\log(x/2)} \ge 0.3\,x/\log x$
for large $x$. Assign to each uncovered $n$ a distinct prime $p\in R$ and set $a_p \equiv n \pmod p$.
Unused primes (in $V'$, $R$, or leftover) get $a_p=0$. Now every $n\in[1,Y]$ is covered.
Weight: $\theta(x)\le 1.01624\,x$ by (E1). $\blacksquare$

**Corollary (classical, for orientation).** Via the one-fold analogue of Theorem A (a single forced
prime $p\mid N+n$ with $p\le x < N$ makes $N+n$ composite), Theorem B reproduces Erdős's 1935 prime-gap
bound: with $\log N \asymp \theta(x) \asymp x$ (so $\log x \asymp \log_2 N$, $\log_2 x\asymp\log_3 N$),
one gets prime gaps $\ \ge\ \tfrac18(1+o(1))\,\log N\,\log_2 N/(\log_3 N)^2\ $ infinitely often.
Rankin's 1938 refinement inserts a further $\log_4$-type factor; irrelevant here, since **any**
divergence suffices — which is exactly why Theorem B is stated in this minimal form.

---

## 4. Phase 1 verdict on the assigned "split-Rankin" construction: it fails

The task specified: partition the primes $\le z$ into classes $P_1,P_2$ so that each class supports
the covering construction at scale $g'(z)$ with $g'/z\to\infty$, then run Theorem B twice and CRT.
**This does not work.** The failure is structural, not a matter of constants; it is the content of
Tao's 28 Jan 2026 comment, and here is the precise accounting.

**4.1 Where the construction breaks.** In Theorem B, three mechanisms interlock:

| Stage | Mechanism | Class-restricted behavior |
|---|---|---|
| zeros on $T\cup V$ | survivors = smooth $\cup$ prime | survivors = "$P_i$-free" numbers — **not** smooth $\cup$ prime |
| greedy on $M$ | factor $\prod_{p\in M}(1-1/p) \approx \frac{\log w}{\log z}$ | factor $\approx \bigl(\frac{\log w}{\log z}\bigr)^{1/2}$ (half the primes) |
| patches on $R$ | budget $\asymp x/\log x$ singletons | budget $\asymp x/(2\log x)$ |

The fatal line is the first. With only $V\cap P_1$ receiving the zero residues, the uncovered set
after Step 1 is $\{n\le Y:\ n \text{ has no prime factor in } (T\cup V)\cap P_1\}$, which contains
every integer composed of primes of $P_2$. This is a **sieve of dimension $\rho=1/2$** (relative
log-density of $P_1$), leaving $\asymp Y/(\log x)^{1/2}$ survivors instead of
$Y\cdot u^{-u} + O(Y/\log x)$. Quantitatively, taking the split $P_2 \supseteq \{p\equiv 3 \bmod 4\}$
(any split with $\ge$ half the primes per dyadic block behaves identically):

**Proposition C (survivor lower bound; rigorous).** Let $Y$ be as in Theorem B. The set
$$E := \{ q_1q_2 \le Y:\ q_i \text{ prime} \equiv 3 \bmod 4,\ Y^{1/3}<q_1\le Y^{1/2}<q_2 \}$$
satisfies $|E| \ge 0.1\,Y/\log Y$ for large $Y$, and no element of $E$ is divisible by any prime of
$P_1=\{p\equiv 1 \bmod 4\}\cup\{2\}$ or by any prime $\le Y^{1/3}$.
*Proof sketch (standard):* $|E| = \sum_{q_1} [\pi(Y/q_1;4,3)-\pi(Y^{1/2};4,3)]$; PNT in progressions
mod 4 gives $\pi(t;4,3) = \frac{t}{2\log t}(1+o(1))$ uniformly for the ranges used; and
$\sum_{Y^{1/3}<q_1\le Y^{1/2},\ q_1\equiv 3(4)} 1/q_1 = \tfrac12\log\tfrac{3}{2}+o(1) \ge 0.2$.
Multiplying: $|E| \ge 0.2 \cdot \tfrac34 \tfrac{Y}{\log Y}(1+o(1)) - O(Y^{1/2}) \ge 0.1\,Y/\log Y$. $\square$

Consequently the $P_1$-run of the construction reaches its Steps 2–3 facing
$\ge 0.1\,Y/\log Y = 0.1 F(x)\, x/\log x \cdot(1+o(1))$ survivors from $E$ alone, while:
* the greedy stage over $M\cap P_1$ has certified factor
  $\prod_{p\in M\cap P_1}(1-1/p) \asymp (\log w/\log z)^{1/2}$, reducing $E$ only to
  $\asymp \frac{Y}{\log Y}\cdot\frac{\log_2 x}{(\log x)^{1/2}} \gg \frac{x}{\log x}\cdot\frac{(\log x)^{1/2}}{8\,\log_2 x}$,
* the patch budget is $< \pi(x) < 1.26\,x/\log x$.

The deficit factor is $\ \gg (\log x)^{1/2}/\log_2 x \to\infty$: **the split construction cannot be
completed by its own stages, for any choice of split**, because halving every prime range halves the
*exponent* in every Mertens product (dimension $1$ → $1/2$), while budgets stay at dimension‑1 size.
This kills the assigned Phase‑1 plan as stated. (It does **not** prove that no residue assignment
exists — coverage lower bounds are exactly the open core; it refutes every *certificate* the
classical method produces. Chojecki's `erdos1139-short.pdf` asserts the split cover as its Lemma 1
with a "only changes constants" remark; by the above, that remark is wrong — the restriction changes
the sieve dimension, not constants. Steps 2–3 of that PDF are fine; the document is a conditional
statement, not a proof.)

**4.2 Why no elementary repair closes it (the $2e^{-\gamma}$ wall).** One can avoid two disjoint
full covers via the $p^2$ trick (Theorem A with $e_p=2$): impose $c\equiv 0$, $e_p=2$ for $p\le r$
and $e_p=1$ for $r<p\le s$ ("stage 0", weight $\theta(r)+\theta(s) = o(Y)$ for $r\le s=o(Y)$). Then
$W(n)\ge 2$ automatically **except** on the target set
$$\mathcal T \ =\ \{R\} \ \cup\ \{qR\} \ \cup\ \{q^jR\},\qquad
  R \text{ $s$-rough (all prime factors} > s), \ q \le s,$$
(precisely: $n$ whose $s$-part is $1$ or a single prime power with capped valuation $1$). With
$s=Y/z$, $z\to\infty$ slowly, $\mathcal T$ consists of: primes in $(Y/z, Y]$ needing **two** more
forced factors ($\approx Y/\log Y$ of them); integers $q\cdot R$ with $q\le z$ prime, $R>Y/z$ prime,
needing **one** more ($\approx \tfrac{Y}{\log Y}\log_2 z$); plus $O(\pi(Y/z)+\sqrt Y)$ stragglers.
Additional forced factors must come from fresh primes $P>s$, one residue class each. Now three
scale-invariant facts, each elementary:

1. **Mertens conservation.** Any family of fresh moduli $P\in(P_0,B]$ with total weight
   $\theta(B)-\theta(P_0) = o(Y)$ (forcing $B=o(Y)$) has
   $\sum 1/P = \log\frac{\log B}{\log P_0}+o(1)$, so the *certified* (pigeonhole) survivor-reduction
   factor is $\exp(-\sum 1/P) = \frac{\log P_0}{\log B}(1+o(1))$. Combined with the rough-number
   density $\prod_{p\le P_0}(1-1/p) \approx e^{-\gamma}/\log P_0$ of stage-0 survivors, the product
   $$\underbrace{\frac{e^{-\gamma}Y}{\log P_0}}_{\text{targets}}\cdot
     \underbrace{\frac{\log P_0}{\log B}}_{\text{certified reduction}}
     \ \approx\ \frac{e^{-\gamma}\,Y}{\log Y}$$
   is **independent of every parameter**. No staging escapes it: interposing more zero-stages or
   greedy stages just re-partitions the same Mertens product $\prod_{p\le B}(1-1/p)$.
2. **Endgame counting bound.** Patching $m$ stragglers needs $\ge m$ distinct fresh primes (two each
   for demand-2 targets), of total weight $\ge (1+o(1))\,m\log m$ (the $m$ smallest primes have
   $\theta(p_m)\sim m\log m$). So weight $o(Y)$ forces $m = o(Y/\log Y)$ stragglers — but item 1
   pins the certified straggler count at $\asymp e^{-\gamma}Y/\log Y$ with demand $\approx 2$,
   i.e. patch cost $\approx 2e^{-\gamma}\,Y \approx 1.12\,Y \ne o(Y)$. The elementary machinery
   saturates at gap $\asymp \log N$ — it misses **by exactly the divergence factor sought**.
3. **First-moment repair also fails.** Averaging over CRT lifts $N = N_0+tM$, $t\le T$, and using
   Montgomery–Vaughan's Brun–Titchmarsh ($\pi(x+H;Q,a)-\pi(x;Q,a) \le 2H/(\varphi(Q)\log(H/Q))$) to
   bound "accidental" failures ($(N+n)/q$ prime, or $N+n$ prime/semiprime), the expected failure
   count is $\asymp$ (support $\tfrac{e^{-\gamma}Y}{\log Y}$)$\times$(class density
   $\tfrac{M}{\varphi(M)}\cdot\tfrac{1}{\log T} \approx \tfrac{e^{\gamma}\log Y\,\psi}{Y}$) $= \psi$,
   where $\psi := Y/\log N$ is the very divergence factor being constructed. So $\mathbb E[\#\text{fail}]\gg 1$
   always; and failures cannot be patched by congruences, because adding a congruence moves $N$ and
   re-randomizes every accidental event (patch-forcing is lift-independent, accident-avoidance is
   not). Note the same $e^{\gamma}$ from $M/\varphi(M)$ cancels the $e^{-\gamma}$ of item 1 —
   scale-invariance again. GRH-quality equidistribution improves the constant 2, not the $\psi$.

**Conclusion of §4.** Every route whose per-modulus coverage is certified only by *averages*
(pigeonhole, Brun–Titchmarsh, first moments) is blocked at a constant multiple of $\log N$. Any
proof must certify residue classes capturing **unboundedly more than the average number** of
prime/semiprime targets — which is precisely the innovation of Maynard (Ann. 183 (2016)) and FGKT
for prime gaps (classes populated by clustered primes via the multidimensional sieve / linear
equations in primes), and precisely what the sole claimed proof imports via Green–Tao. Tao's
one-line diagnosis is thus quantitatively confirmed on all three axes.

---

## 5. What a correct proof needs (specification), and the assigned Phase-1/Phase-2 checklist

For the record, the assigned construction's own checklist, answered honestly:

* (a) *Does the split preserve the covering bound?* **No** — dimension halves in every Mertens
  product; Proposition C gives an explicit $\gg Y/\log Y$ survivor family immune to the entire
  restricted first stage. This is fatal as specified.
* (b) *Cofactor $>1$*: handled once and for all in Theorem A(ii) via $N>M^2$ — including all edge
  cases $n\le Y$, any modulus sizes.
* (c) *$n$ prime in the interval*: impossible — Theorem A forces $\Omega(N+n)\ge 3$ for every
  offset; $N+n > M^2 > Y^2 > $ any forced prime, so $N+n$ never equals a forced prime.
* (d) *Counting/normalization*: Theorem A(iv)–(v); only $k\le N$ and $u_{k+1}>N$ are used; Landau's
  asymptotic is *not needed* for the direction required (it would only be needed to convert an
  upper bound on gaps).
* (e) *$\Omega$ vs $\omega$*: $\Omega$ (canonical) needs $W\ge 2$; $\omega$ needs 3 distinct forced
  primes (Theorem A′). Both reductions are closed; the $\omega$ analytic core is strictly harder.

**Specification of the remaining open core** (the precise gap): produce, for arbitrarily large $Y$,
a system per Theorem A with $L=o(Y)$. Equivalently, after the cheap stage 0
($c=0$, $e_p=2$ for $p\le z$, $e_p=1$ for $z<p\le Y/z$, weight $2\theta(z)+\theta(Y/z) = o(Y)$),
cover the targets
$$\mathcal T_1 = \{\text{primes } q\in(Y/z,\,Y]\}\ (\text{demand }2),\qquad
  \mathcal T_2 = \{ sq \le Y:\ s\le z \text{ prime},\ q>Y/z \text{ prime}\}\ (\text{demand }1)$$
using distinct fresh primes $P$, one class each, total weight $o(Y)$ — with per-class capture
$\omega(1)$ targets on average against their demand. This requires prime-tuple-type input.

---

## 6. Review of the claimed proof (Liam Price / GPT Pro, submitted 2026-07-15)

**Provenance.** Claim page: "A full proof, claimed by Liam Price (using GPT Pro)… affirmative."
External link = Overleaf read-link (not retrievable here; attempted curl/WebFetch/browser — the
environment blocks Overleaf, and the companion ChatGPT share is login-gated). What follows reviews
the author's own detailed strategy digest (19 Jun 2026 comment) against my independent analysis.

**Digest of the claimed proof.** With $Y$ the interval length and $z\to\infty$ slowly:
1. Stage 0: $N \equiv 0 \pmod{M_0}$, $M_0 = \prod_{p\le z}p^2 \prod_{z<p\le Y/z}p$ — *identical to
  the stage 0 derived independently in §5*, forced-count $W\ge 2$ off the target set; remaining
  targets are exactly my $\mathcal T_1$ (primes, "two coloured vertices") and $\mathcal T_2$
  (semiprimes $sq$, "one vertex"), plus sparse exceptions.
2. Hyperedges: for a fresh "modulus prime" $P$ and residue $A$, the class $\{A+dP\}$ covers several
  targets at once; a selected index $d$ carries a type (prime target $q$, or semiprime target $sq$
  with prescribed small factor $s$); the residue is engineered so the targets are the prime values
  of an explicit system of primitive affine-linear forms $Q_d(P,C)$ with no fixed prime divisor.
3. Counts: the Main Theorem of Green–Tao, *Linear equations in primes* (Ann. of Math. 171 (2010)
  1753–1850 — the annals link in the comment), applied to single hyperedges and to pairs, gives
  first and second moments: expected fractional load per modulus prime bounded below 1; load per
  target concentrated near a large prescribed value.
4. A selection argument (one admissible hyperedge per "regular" modulus prime, independently) covers
  all but $o(Y/\log Y)$ vertices; stragglers and exceptional offsets get one or two dedicated
  reserve primes from $(Y,2Y]$; CRT assembles $N$; forced products are $<N+n$, so $\Omega\ge 3$;
  $\log N = o(Y)$ gives the result as in Theorem A.

**Assessment.**
* *Architecture*: correct and, per §4, of the **required** shape — it is exactly the
  "above-average certified capture" design (FGKT-style hypergraph covering with prime-tuple input),
  the unique known way past the wall. The elementary frame (stage 0, reserves, CRT, normalization)
  coincides with what I proved independently in Theorems A/§5, so those ~40% of the proof I can
  vouch for directly.
* *Green–Tao applicability*: for **fixed** $z$, the family of form-systems is finite (types
  $s\le z$, bounded pattern sets $d$), coefficients bounded; GT handles any fixed finite-complexity
  system, and pairwise-nonproportional affine forms in the two variables $(P,C)$ have finite
  complexity. Ineffectivity and non-uniformity in the system are then harmless because the target
  is a **limsup**: run $Y\to\infty$ at fixed $z$ to get $\liminf$-gap-ratio $\ge \phi(z)$, then
  diagonalize $z\to\infty$. This is the one place a naive reviewer would object ("GT is not uniform
  in the coefficients") and the digest's structure already dodges it. Sound.
* *Unverifiable here*: the second-moment/codegree computations (pairs of hyperedges through a
  vertex), the non-degeneracy of every merged form system, the "at most one hyperedge per regular
  prime" selection concentration, and the weight bookkeeping $\sum\log P = o(Y)$. These are the
  fiddly 60%; each is standard-shaped (cf. FGKT JEMS 23 §3–5) but standard-shaped is where AI
  proofs die. One independent screening (Sothanaphan, AI-assisted) found only a typo; the claim has
  had **zero** expert sign-off in six weeks; Tao commented on the January attempts but has not, in
  the visible record, endorsed this one.
* *Difference from "our" assigned approach*: ours (disjoint split, two independent Rankin runs) is
  refuted (§4); Price's replaces the second cover with $p^2$-forcing plus GT-powered multi-capture,
  which is the repair my barrier analysis says is necessary. No contradiction between my negative
  result and his claim: Proposition C blocks *certificate-free splits*, not GT-certified classes.

**Review verdict: plausible-unverified.** Strategy sound; elementary skeleton independently
confirmed here; analytic core unretrievable and unvetted. Not to be cited as a theorem yet.

---

## 7. Phase 3 — numerics (sieve to $10^8$)

`gaps1139.py`, output `numerics_output.txt`. $\Omega$ computed by prime-power sieve; sequence checked
against OEIS **A037143** (first 30 terms match exactly — definitional sanity, $\Omega$ w/ multiplicity,
$1$ included). $\#\{u_k\le 10^8\} = 23{,}188{,}714$ ($\approx 10^8\cdot\log_2/\log$ ✓).

Record gaps ($u_{k+1}-u_k$, with $u_k\le N$, $k$ the 1-based index):

| $k$ | $u_k$ | gap | gap$/\log k$ | gap$/\log u_k$ |
|---|---|---|---|---|
| 132 | 241 | 6 | 1.23 | 1.09 |
| 13 778 | 39 343 | 16 | 1.68 | 1.51 |
| 173 573 | 584 213 | 24 | 1.99 | 1.81 |
| 1 370 179 | 5 167 587 | 32 | 2.26 | 2.07 |
| 6 740 807 | 27 489 679 | 40 | 2.54 | 2.34 |
| 16 571 993 | 70 416 259 | 42 | 2.53 | 2.32 |

Max gap to $10^8$: **42**, at $u_k = 70\,416\,259$. The normalized record ratio creeps
$1.0 \to 2.5$ over eight decades — consistent with a $\limsup$ diverging like a power of
$\log_2$/$\log_3$ (Rankin-type rates), and decisively unlike a bounded ratio. Mean gap in the last
decade $4.36$ vs $\log N/\log_2 N = 6.32$. Nothing here contradicts the affirmative answer or the
definitional reading; nothing can confirm a limsup statement.

---

## 8. Honest final assessment

**Status: GAP-REMAINS (for this session's mandate of a self-contained solve); the problem is
plausibly SOLVED externally, modulo verification.** Precisely:

1. **Proved here, referee-standard**: Theorem A (+A′) — the sparse 2-fold forced-factor criterion
   implies the affirmative answer, including all normalization/edge cases; Theorem B — the
   elementary one-fold Rankin–Erdős cover with $Y/\text{weight}\to\infty$, explicit constants;
   Proposition C and the §4 barrier accounting.
2. **Refuted here**: the assigned split-Rankin Phase-1 construction (and Chojecki's Lemma 1 route),
   by an explicit $\gg Y/\log Y$ immune survivor family plus dimension accounting — in agreement
   with Tao's expert judgment. My Phase-2 adversarial pass therefore *killed my own assigned
   construction*, which is the correct outcome: delivering it as a "proof" would have been wrong.
3. **The precise open core** (all that separates the problem from solved): existence of the sparse
   2-fold cover of §5's specification — equivalently, residue classes capturing $\omega(1)\times$
   average prime/semiprime targets per fresh modulus prime at total weight $o(Y)$. This demands
   Maynard/Green–Tao-type input; it is not reachable by the elementary toolkit, provably so at the
   level of certificates (§4.2).
4. **External claim**: Price/GPT-Pro (2026-07-15) implements exactly this specification via
   Green–Tao + hypergraph covering; architecture verified sound here; details unretrievable in this
   environment; one positive screening; no expert endorsement; site still lists OPEN.
   **Plausible-unverified.**
5. **Numerics**: definition pinned to A037143/$\Omega$; record ratios slowly increasing (max gap 42
   at $7\times 10^7$); fully consistent.

Files: `page1139.html`, `forum1139.html`, `proofclaims1139.html`, `erdos1139-short.pdf`(+`.txt`),
`ems32526.pdf` (FKMPT JEMS 1020), `gist.html`, `A101041.html`, `gaps1139.py`, `numerics_output.txt`,
this document.

### References
Westzynthius (1931); Erdős, *On the difference of consecutive primes*, Q. J. Math. 6 (1935);
Rankin, J. LMS 13 (1938); Rosser–Schoenfeld, Illinois J. Math. 6 (1962); Landau (1900) for
$\pi_2(x)\sim x\log_2 x/\log x$; Montgomery–Vaughan, *The large sieve*, Mathematika 20 (1973);
Maynard, *Large gaps between primes*, Ann. of Math. 183 (2016); Ford–Green–Konyagin–Tao, Ann. of
Math. 183 (2016); Ford–Green–Konyagin–Maynard–Tao, J. AMS 31 (2018); Ford–Konyagin–Maynard–
Pomerance–Tao, *Long gaps in sieved sets*, JEMS 23 (2021) 667–700; Green–Tao, *Linear equations in
primes*, Ann. of Math. 171 (2010) 1753–1850; Green–Tao–Ziegler, Ann. of Math. 176 (2012);
Halberstam–Heath-Brown–Richert (1981) [upper-bound context]; T. F. Bloom, erdosproblems.com/1139
and /689, accessed 2026-07-30.
