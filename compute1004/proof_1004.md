# Erdős Problem #1004: pairwise distinct totients in polylogarithmic windows

**Status delivered by this document.**

- **Full problem (every fixed c > 0): GAP-REMAINS.** The problem is open, and (see App. B) the
  first-moment/union-bound method used here provably cannot be pushed to c ≥ 2.
- **Proved here rigorously (assembly of refereed literature + new glue, complete proofs):
  the answer is YES for every fixed c < 2**, in the stronger almost-all form: for every fixed
  c < 2, for all sufficiently large x, *all but o(x)* of the n ≤ x have
  φ(n+1), ..., φ(n+⌊(log x)^c⌋) pairwise distinct. More precisely the conclusion holds for any
  window length L = L(x) with L·log(3L)·log log(3L) = o((log x)²).
- The two nontrivial inputs are **published, refereed, and stated in exactly the needed uniform
  form** in Pollack–Pomerance–Treviño (Ramanujan J. 30 (2013), 379–398), §3 (Theorems 3.1 and
  3.3, Lemma 3.2). Everything else (the shift-summed singular-series estimate, the union bound,
  odd-shift vanishing of structured solutions) is proved in full below. Appendix A additionally
  reconstructs, at referee standard and with every k-dependence audited, the proof of the
  uniform exceptional bound (PPT Thm 3.1), whose journal proof is a sketch deferring to
  Erdős–Pomerance–Sárközy (1987) and Graham–Holt–Pomerance (1999); I have verified the
  generalization against the original EPS87 argument line by line.

---

## 1. The problem (pinned)

From https://www.erdosproblems.com/1004 (fetched 2026-07-30; page last edited 2026-04-12;
status OPEN; source [Er85e]):

> Let c > 0. If x is sufficiently large then does there exist n ≤ x such that the values of
> φ(n+k) are all distinct for 1 ≤ k ≤ (log x)^c, where φ is the Euler totient function?

Site remark: "Erdős, Pomerance, and Sárközy [EPS87] proved that if φ(n+k) are all distinct for
1 ≤ k ≤ K then K ≤ n/exp(c(log n)^{1/3}) for some constant c > 0." (See §3.6 for a caveat on
this attribution.) See problem #945 for the divisor-function analogue.

Forum state (2026-07-30): 7 comments, 0 claimed proofs. The comments contain (i) an AI-produced
partial-result note ("aditya", 2026-04-29) proving the c < 2 case along the same lines as §4
below, checked without issues by a verifier and believed "implicitly known" from
Pollack–Pomerance–Treviño; (ii) a claimed uniform bound R_h(X) ≪_{A,B} X/(log X)^A for
h ≤ (log X)^B ("Svyable", 2026-04-28) which was challenged by P. Chojecki and **retracted by
its poster**: it is not in the literature and is essentially certainly false (App. B makes the
falsity unconditional for A ≥ 51). This document confirms the retraction was correct.

**Quantifier reading (fixed once and for all).** c > 0 is fixed; the assertion is
∃x₀(c) ∀x ≥ x₀(c) ∃n ≤ x: φ(n+i) ≠ φ(n+j) for all 1 ≤ i < j ≤ ⌊(log x)^c⌋. For small c the
window ⌊(log x)^c⌋ may be short (even length 1, where the statement is vacuous-true); this is
harmless since x₀ may depend on c. Our Theorem 4.4 gives the statement for every fixed c < 2
with the good n forming density 1 − o(1).

## 2. Notation

φ = Euler's totient; P(n) = largest prime factor of n (P(1) = 1); rad(n) = γ(n) = product of
distinct primes dividing n; ω(n) = number of distinct prime divisors;
C₂ = ∏_{p>2}(1 − (p−1)^{-2}) (twin-prime constant). For k ≥ 1,

  P(x; k) = #{n ≤ x : φ(n) = φ(n+k)}.

Following GHP/PPT, a solution n of φ(n) = φ(n+k) is *of Theorem-A form* if there are j with
rad(j) = rad(j+k), g = gcd(j, j+k), and a positive integer r with (j/g)r + 1 and
((j+k)/g)r + 1 both prime, neither dividing j, such that n = j(((j+k)/g)r + 1). Write
P₀(x;k) for the number of solutions n ≤ x of Theorem-A form, P₁(x;k) = P(x;k) − P₀(x;k).
Implied constants are absolute unless subscripted.

## 3. Literature verdict (all statements verified against the original PDFs)

### 3.1 EPS87-II (verified from the original)

P. Erdős, C. Pomerance, A. Sárközy, *On locally repeated values of certain arithmetic
functions. II*, Acta Math. Hungar. 49 (1987), 251–259.

**Theorem 2 (EPS87-II, p. 253, exact).** For large x, the number of solutions n ≤ x of
φ(n) = φ(n+1) is at most x/exp{(log x)^{1/3}}.

The proof (§4 of the paper, verified in full; reconstruction in App. A) is the template for
everything below. They remark the same holds for σ(n) = σ(n+1), and conjecture ≥ x^{1−ε}
solutions; infinitude is still open for k = 1.

### 3.2 GHP (verified from https://math.dartmouth.edu/~carlp/phi.pdf)

S. W. Graham, J. J. Holt, C. Pomerance, *On the solutions to φ(n) = φ(n+k)*, in: Number Theory
in Progress (Zakopane, 1997; Schinzel 60th birthday volume), de Gruyter, 1999, pp. 867–882.

- **Theorem 1** (the structured families; "Theorem-A form" above), generalizing Schinzel's
  n = (2p−1)k. Proof: if rad(j) = rad(j+k) then φ(j)(j+k) = jφ(j+k), and the two prime
  conditions give φ(n) = φ(n+k) by multiplicativity.
- **Theorem 2**: for every **fixed** k there is x₀(k) with P₁(x;k) < x/exp((log x)^{1/3}) for
  x ≥ x₀(k). Proof by modifying EPS87-II; the class-(B) case (φ(m)/m = φ(m')/m' for the
  cofactors) is shown to force Theorem-A form.
- **Corollary 1**: with c(k) = Σ*_j [g/(j(j+k))] ∏*_{p | jk(j+k)/g³, p>2} (p−1)/(p−2)
  (Σ* over j with rad(j) = rad(j+k), g = gcd(j, j+k)): 0 < c(k) < ∞, and under the
  quantitative Dickson/Bateman–Horn conjecture, **P(x;k) ~ 2C₂ c(k) x/(log x)²** for even k.
- **Theorem 3**: Σ_{k≤x} P₀(k;x) ~ c·x. Also Table 1 (P(k;x) for k ≤ 100, x ≤ 10^{10}) —
  matches our numerics §7.

*Transcription caveat (adversarial finding — a fatal typo, though only in the quotation):*
GHP's proof sketch of their Theorem 2 quotes EPS87-II's parameter as
L = exp((1/8)(log x)^{1/3} log log x); the original EPS87-II (p. 257) has
L = exp{(1/8)(log x)^{2/3} log log x}. The 2/3 exponent is the one that makes the
smooth-number and factorization-counting steps work: with the printed 1/3 the Rankin bound of
Lemma A.3 fails outright, since its saving would no longer beat the Euler-product loss (see
Remark A.4(ii)). The typo is confined to GHP's quotation of EPS87; the arguments of EPS87-II,
GHP and PPT all use the correct parameter, and so does App. A.

### 3.3 PPT — the decisive uniform statements (verified; published Ramanujan J. 30 (2013), 379–398)

P. Pollack, C. Pomerance, E. Treviño, *Sets of monotonicity for Euler's totient function*
(preprint copy: campus.lakeforest.edu/trevino/monotone4.pdf; §3 "Counting solutions to
φ(n) = φ(n+k)"). They write: "This equation has been treated in [GHP, Theorem 2] and [Yamada],
but only for fixed k. **We require results which are uniform in k**, which we state and prove
in §3."

- **Theorem 3.1 (exact).** For x > x₀, we have P₁(x;k) < x/exp((log x)^{1/3}), **uniformly for
  natural numbers k ≤ exp((log x)^{1/3})**.
  Their proof is a sketch: "We imitate the proof of [GHP, Theorem 2] ... The argument of
  [EPS87-II] goes through with obvious minor changes until [EPS87-II, eq. (4.4)]. At that
  point, it is important to know that given m and a certain prime q′, the congruence
  mp + k ≡ 0 (mod q′) forces p to lie in a uniquely determined residue class modulo q′. This
  holds as long as q′ ∤ m. If q′ | m and q′ | mp + k, then q′ | k. But we also have
  q′ ≡ 1 (mod r), where r ≥ l⁴ and l = exp((log x)^{1/3}). Hence q′ > l⁴ > k, and so q′ ∤ k."
  **App. A below reconstructs the full argument and audits every k-dependence; the sketch is
  correct.**
- **Lemma 3.2 (exact).** The number of j for which j and j+k have the same set of prime
  factors is at most 3·7^{3+2ω(k)}. (Proof via Evertse's S-unit theorem: (j+k)/k + (−j/k) = 1
  is an S-unit equation with S = {∞} ∪ {p : p | k}, since rad(j) = rad(j+k) implies
  rad(j) | k.) Consequently ≤ k^ε such j once k > k₀(ε).
- **Theorem 3.3 (exact).** Let ε(x) → 0 with x^{ε(x)} → ∞. For even k with 2 ≤ k ≤ x^{ε(x)},
  as x → ∞, **P₀(x;k) ≤ (16C₂ + o(1)) c(k) x/(log x)², uniformly in k.** Moreover
  (2k)^{-1} ≤ c(k) ≤ 3·7^{3+2ω(k)} ∏_{p|k, p>2} (p−1)/(p−2) · k^{-1}; their Remark:
  c(k) ≪ k^{-1} exp(O(log k/log log 3k)).
  (Proof: for each admissible j with j(j+k)/g ≤ x^{√ε(x)}, Selberg's upper-bound sieve
  [Halberstam–Richert, Thm 5.7] applied to the prime pair (j/g)r + 1, ((j+k)/g)r + 1 in
  r ≤ gx/(j(j+k)); the j with j(j+k)/g > x^{√ε(x)} contribute ≤ x^{1−√ε(x)} each and number
  ≤ x^{ε(x)} by Lemma 3.2. I verified the printed proof; it is complete and uniform.)

These two theorems are **exactly the needed uniform inputs**; the assembly below is then
elementary. The forum's "implicitly known in PPT" is accurate for the collision bounds; the
window corollary (§4) is not stated in PPT but is a page of glue.

### 3.4 Later work on φ(n) = φ(n+k) (2000–2026, checked)

- T. Yamada, *On equations σ(n) = σ(n+k) and φ(n) = φ(n+k)* (arXiv:1001.2511): for **fixed**
  data, improves the exceptional bound to ≪ x·exp(−(2^{-1/2}+o(1))(log x log log log x)^{1/2});
  in particular this holds for P(x;k), k odd fixed. Not uniform in k; not needed here.
- J. Holt (2003): at least two solutions of φ(n) = φ(n+k) for **every** even k.
- K. Ford, *Solutions of φ(n) = φ(n+k) and σ(n) = σ(n+k)* (arXiv:2002.12155): unconditionally,
  φ(n) = φ(n+k) has infinitely many solutions for some even k ≤ 3570 and for every k divisible
  by 442720643463713815200 (via Maynard–Tao). Confirms structured solutions are genuinely there.
- S. Kim, *On the equations φ(n) = φ(n+k) and φ(p−1) = φ(q−1)* (csun.edu preprint/paper):
  **Theorem 1.1**: with j = 50#, for sufficiently large x there is k_x ∈ {j, 2j, ..., 49j}
  with P₀(k_x; x) ≫ x/(log x)^{50}, unconditionally (Maynard–Tao + GHP Cor. 2). Used
  adversarially in App. B.
- T. Tao, *Monotone non-decreasing sequences of the Euler totient function* (arXiv:2309.02325):
  resolves PPT's M↑(x) question; monotone runs, tangential to distinctness.
- Nothing in the literature (searched arXiv/journals through July 2026) states the polylog
  window distinctness result itself; the strongest related prior text is the (unrefereed,
  plausibly correct) forum note of 2026-04-29 proving the c < 2 case.

### 3.5 Consequence map

EPS87-II (k = 1, fixed) → GHP (all k fixed, + structured/exceptional split) → PPT §3
(both bounds uniform in k) → **§4 below (window theorem, every c < 2)**.

### 3.6 A caveat on the site remark

The remark on erdosproblems.com/1004 attributes to [EPS87] the single-n window bound
"φ(n+k) all distinct for 1 ≤ k ≤ K ⟹ K ≤ n/exp(c(log n)^{1/3})". Having read EPS87-II and
EPS87-III in full, I could not find this statement in either paper: EPS87-II Thm 2 is the
*count* bound for φ(m) = φ(m+1), m ≤ x, and EPS87-III concerns ω/Ω/d. A counting bound cannot
by itself bound K for an *individual* n (rare events need not appear in a given window), and a
deterministic construction of equal-totient pairs at relative distance exp(−(log n)^{1/3})
does not seem to be available. Presumably the remark paraphrases a statement of Erdős in
[Er85e]; I flag it as *not verified* here. It plays no role in our proof; it concerns the
complementary regime (very long windows must contain collisions), while the problem and this
document concern polylog windows.

---

## 4. Main theorem: distinct totients in windows of length (log x)^c, c < 2

Throughout, x is large; L = L(x) ≥ 2 is an integer window length with L ≤ exp((log x)^{1/3})
(amply true for L = ⌊(log x)^c⌋). Call n *bad* (for x, L) if n ≤ x − L and there exist
1 ≤ i < j ≤ L with φ(n+i) = φ(n+j); call n good if n ≤ x − L and not bad.

### Lemma 4.1 (odd shifts have no structured solutions)

For odd k, there is no j with rad(j) = rad(j+k); hence P₀(x;k) = 0 and P(x;k) = P₁(x;k).

*Proof.* If rad(j) = rad(j+k) then j and j+k have the same parity (2 divides one iff it
divides the other), so k = (j+k) − j is even. ∎

### Lemma 4.2 (shift-summed singular series)

With c(k) as in §3.3 (GHP Cor. 1/PPT (7)), for L ≥ 2:

  Σ_{k even, 2 ≤ k ≤ L} c(k) ≪ (log 3L)(log log 3L).

*Proof.* Fix an admissible pair (j, k): rad(j) = rad(j+k), k ≤ L. Write g = gcd(j, j+k),
a = j/g, b = (j+k)/g, so gcd(a,b) = 1, b − a = k/g ≥ 1, and g ≤ g(b−a) = k ≤ L.

(1) *Support of the singular product.* Every prime p | j satisfies p | rad(j) = rad(j+k), so
p | (j+k) − j = k; likewise p | (j+k) ⟹ p | k. Hence all primes dividing jk(j+k)/g³ divide k,
and

  ∏_{p | jk(j+k)/g³, p>2} (p−1)/(p−2) ≤ S(k) := ∏_{p | k, p>2} (1 + 1/(p−2)).

Since ∏_{p|k, p>2}(1+1/(p−2)) ≤ exp(Σ_{p | k} O(1/p)) and the sum over the first ω(k) odd
primes is O(log log 3ω(k)) = O(log log log 3k), we have S(k) ≪ log log 3k ≤ C log log 3L
for all k ≤ L (crude but sufficient).

(2) *Radical constraint.* If p | a then p | j, so p | k = g(b−a); p ∤ b−a would still allow
p | g, and indeed p ∤ b (coprimality) while p | rad(j+k) = rad(gb) forces p | g. Symmetrically
p | b ⟹ p | g. Hence **rad(ab) | rad(g)**.

(3) *Summation.* Each term of each c(k) equals g/(j(j+k)) · ∏(...) ≤ S(k)/(g a b), and the map
(j,k) ↦ (g,a,b) is injective. Therefore

  Σ_{k ≤ L} c(k) ≤ C log log 3L · Σ_{g ≤ L} (1/g) Σ_{a,b ≥ 1, rad(ab) | rad(g)} 1/(ab)
   = C log log 3L · Σ_{g ≤ L} (1/g) ∏_{p | g} (1 − 1/p)^{-2}
   = C log log 3L · Σ_{g ≤ L} (g/φ(g))²/g.

(The inner sums over a, b factor as ∏_{p|g}(1 + 1/p + 1/p² + ...) each.) Finally
Σ_{g ≤ L}(g/φ(g))²/g ≪ log 3L: writing (g/φ(g))² = Σ_{d | g} μ²(d)h(d) with h multiplicative,
h(p) = (p/(p−1))² − 1 = (2p−1)/(p−1)² ≪ 1/p, we get
Σ_{g≤L}(g/φ(g))²/g ≤ Σ_d μ²(d)h(d)/d · (1+log L) ≪ log 3L · ∏_p(1 + h(p)/p) ≪ log 3L. ∎

*Remark.* The lower bound c(k) ≥ (2k)^{-1} (PPT Thm 3.3, from the term j = k) gives
Σ_{k ≤ L} c(k) ≫ log L, so Lemma 4.2 is sharp up to the log log factor. Using instead PPT's
c(k) ≪ k^{-1}exp(O(log k/log log 3k)) termwise would give only Σ ≪ exp(O(log L/log log L)) =
L^{o(1)}; that weaker bound also suffices for every fixed c < 2, but Lemma 4.2 gives the clean
threshold below.

### Proposition 4.3 (uniform collision bound, assembled)

There is x₁ such that for all x ≥ x₁, uniformly for 1 ≤ k ≤ exp((log x)^{1/3}):

  P(x;k) ≤ 33 C₂ c(k) x/(log x)² · 1_{k even} + x/exp((log x)^{1/3}),

and consequently, for 2 ≤ L ≤ exp((log x)^{1/2}·(log x)^{-1/6}) (in particular for
L = ⌊(log x)^c⌋, any fixed c > 0, x large):

  Σ_{k=1}^{L} P(x;k) ≪ x (log 3L)(log log 3L)/(log x)² + L x/exp((log x)^{1/3}).

*Proof.* P = P₀ + P₁. For P₁ apply PPT Thm 3.1 (App. A gives the full proof): uniformly for
k ≤ exp((log x)^{1/3}), P₁(x;k) < x/exp((log x)^{1/3}) for x > x₀. For P₀: if k is odd,
P₀ = 0 (Lemma 4.1). If k is even, apply PPT Thm 3.3 with (say) ε(x) = (log x)^{-1/2}; every
k ≤ exp((log x)^{1/3}) satisfies k ≤ x^{ε(x)} = exp((log x)^{1/2}) for large x, and the o(1)
in Thm 3.3 is uniform over such k, so P₀(x;k) ≤ (16C₂ + o(1))c(k)x/(log x)² ≤
33C₂c(k)x/(log x)² for x large. Summing over k ≤ L with Lemma 4.2 gives the display. ∎

### Theorem 4.4 (main result: distinct-totient windows below the (log x)² scale)

Let L = L(x) ≥ 2 be any integer function with

  (★) L (log 3L)(log log 3L) = o((log x)²)  and L ≤ exp((log x)^{1/4}) (say).

Then the number of bad n is o(x); explicitly

  #{n ≤ x − L : φ(n+i) = φ(n+j) for some 1 ≤ i < j ≤ L}
   ≪ x·L(log 3L)(log log 3L)/(log x)² + x·L²/exp((log x)^{1/3}) = o(x).

In particular, for each fixed c < 2, taking L = ⌊(log x)^c⌋ (which satisfies (★) since
L log 3L ≪ (log x)^c log log x = o((log x)²)): for all x ≥ x₀(c), all but
O(x (log x)^{c−2} (log log x)(log log log x)) = o(x) of the integers n ≤ x satisfy:
φ(n+1), ..., φ(n+L)
are pairwise distinct. **A fortiori such an n ≤ x exists, so the answer to Problem #1004 is
YES for every fixed c < 2.**

*Proof.* Let n ≤ x − L be bad: φ(n+i) = φ(n+j), 1 ≤ i < j ≤ L. Put h = j − i ∈ [1, L−1] and
m = n + i. Then 1 ≤ m and m ≤ (x−L) + L − h ≤ x − h < x, and φ(m) = φ(m+h): m is counted by
P(x;h). (No boundary correction is needed: both window elements n+i, n+j lie in [1, x] because
n ≤ x − L.) For fixed h, each colliding m yields at most min(L−h, L) values of n (namely
n = m − i, 1 ≤ i ≤ L−h with j = i+h ≤ L); hence

  #bad ≤ Σ_{h=1}^{L−1} (L−h) P(x;h) ≤ L Σ_{h=1}^{L} P(x;h).

Proposition 4.3 bounds the sum: #bad ≪ L·[x(log 3L)(log log 3L)/(log x)² +
Lx/exp((log x)^{1/3})]. The first term is o(x) by (★). For the second, the hypothesis
L ≤ exp((log x)^{1/4}) gives

  L²/exp((log x)^{1/3}) ≤ exp(2(log x)^{1/4} − (log x)^{1/3}) → 0,

so that term is o(x) as well. Hence #bad = o(x).
Finally, the n ∈ (x − L, x] number at most L = o(x), so at least x − o(x) integers n ≤ x are
good, and for x ≥ x₀ (with x₀ depending only on the function L, i.e., only on c in the
application) a good n ≤ x exists. For L = ⌊(log x)^c⌋, c < 2 fixed, Lemma 4.2 gives
log 3L ≪ log log x and log log 3L ≪ log log log x, so the explicit bound is
O(x(log x)^{c−2}(log log x)(log log log x)). ∎

**Quantifier/edge audit.** (a) c is fixed before x₀; all o(·), ≪ above are uniform once
L(x) is fixed, and depend on c only through L. (b) If ⌊(log x)^c⌋ ≤ 1 the statement is
vacuously true; Theorem 4.4 assumed L ≥ 2 only to avoid trivialities. (c) The window in the
problem is k = 1, ..., (log x)^c, i.e., length ⌊(log x)^c⌋ = L: matches. (d) All collision
counts were taken at argument x (not x + L) — possible because bad n were restricted to
n ≤ x − L and the tail (x−L, x] was discarded trivially. (e) Both parities of h are covered
(odd h via Lemma 4.1 + P₁; even h via P₀ + P₁).

---

## Appendix A. The uniform exceptional bound, reconstructed and audited

**Theorem A.1 (= PPT Thm 3.1).** There is an absolute x₀ such that for x > x₀ and every
natural number k ≤ l := exp((log x)^{1/3}):

  P₁(x;k) < x/l.

The proof below is EPS87-II §4 (read from the original, Acta Math. Hungar. 49 (1987) 251–259)
generalized from k = 1 to uniform k as prescribed by GHP Thm 2 and PPT Thm 3.1; each step is
annotated with its k-dependence. Set

  l = exp((log x)^{1/3}), Y = exp{(1/8)(log x)^{2/3} log log x}
  (EPS87's L; note the 2/3 exponent — see §3.2 caveat).

Let n ≤ x satisfy φ(n) = φ(n+k), n not of Theorem-A form. Discard successively:

**(A0) Small n.** n ≤ x/l²: at most x/l² = o(x/l) such n, trivially. (Discarding at x/l
instead would contribute exactly x/l and leave the final bound at (1+o(1))x/l, too weak for
the strict inequality; x/l² costs nothing elsewhere, since every later step only uses
n > x/l² through the trivial bounds p ≤ x/m, p′ ≤ 2x/m′.) [k-free]

**(A1) Smooth values.** P(n) < Y² or P(n+k) < Y². The number of such n ≤ x is
≤ 2Ψ(2x, Y²) (with Ψ the smooth-counting function; n+k ≤ 2x since k ≤ l ≤ x). By the standard
de Bruijn estimate, Ψ(2x, Y²) ≤ 2x·exp(−(1+o(1)) u log u) with
u = log(2x)/log(Y²) = 4(log x)^{1/3}/log log x (1+o(1)), so u log u ~ (4/3)(log x)^{1/3} and
Ψ(2x, Y²) = o(x/l). [k enters only through n+k ≤ 2x: uniform for k ≤ x.]

**(A2) Large squarefull part.** Some prime power r^a | n or r^a | n+k with a ≥ 2 and r^a > l³.
Count ≤ 2 Σ_{s squarefull, s > l³} 2x/s ≪ x/l^{3/2} = o(x/l). [uniform]

Surviving n: write n = mp, p = P(n); n+k = m′p′, p′ = P(n+k). By (A1)+(A2), p² ∤ n (else
p² ≤ l³ < Y⁴ ≤ p², absurd), so p ∤ m; likewise p′ ∤ m′. Thus
  φ(m)(p−1) = φ(n) = φ(n+k) = φ(m′)(p′−1). (†)
Also p ≠ p′: p = p′ would give p | n, p | n+k, so p | k; but p ≥ Y² > l ≥ k. [k-dependence:
needs k < Y², amply true — **audited**.]

**(A3) The two classes.** From (†) and mp + k = m′p′:

  p′·(φ(m)m′ − mφ(m′)) = m(φ(m) − φ(m′)) + kφ(m). (‡)

*Class (B):* φ(m)/m = φ(m′)/m′. Then φ(m)m′ = mφ(m′), so by (†), p′−1 = (m/m′)(p−1); then
m′p′ = m(p−1) + m′ = mp − m + m′ forces k = m′ − m, i.e. m′ = m + k and
φ(m)/m = φ(m+k)/(m+k). The latter forces rad(m) = rad(m+k) (Lemma A.2 below). With
g = gcd(m, m+k): ((m+k)/g)(p′−1) = (m/g)(p−1) with the two fractions coprime, so
(m/g) | p′−1: p′ = (m/g)r + 1 and then p = ((m+k)/g)r + 1, for a positive integer r
(positivity: p′ ≥ Y² > m/g + 1). Moreover p ∤ m (as above) and p′ ∤ m (p′ | n+k and p′ | m | n
would give p′ | k < Y² ≤ p′). Hence n = mp = m(((m+k)/g)r + 1) **is of Theorem-A form with
j = m** — excluded, since we count P₁. So all surviving n are in:

*Class (A):* φ(m)m′ − mφ(m′) ≠ 0. Then (‡) determines p′ = RHS/coefficient, and
p = (m′p′ − k)/m, from the pair (m, m′) (and k, which is fixed). **Each pair (m, m′) yields at
most one n.** [Class split and (B)-analysis: pure algebra, uniform in k — **audited**.]

**Lemma A.2.** If S, T are finite sets of primes with ∏_{p∈S}(1−1/p) = ∏_{p∈T}(1−1/p), then
S = T. *Proof.* Cancel common elements; assume S ∩ T = ∅, S ∪ T ≠ ∅, and let P = max(S ∪ T),
say P ∈ S. Cross-multiplying, ∏_{S}(p−1)·∏_{T}p = ∏_{T}(p−1)·∏_{S}p. The right side is
divisible by P; on the left, every p ∈ T is < P and every factor p−1 (p ∈ S) is < P, so all
prime factors of the left side are < P. Contradiction. ∎

**(A4) Small cofactors.** Discard class-(A) n with m < Y or m′ < Y. If m < Y: the pair (m, m′)
has m < Y, m′ ≤ (x+k)/Y² ≤ 2x/Y² (since m′p′ = n+k ≤ 2x, p′ ≥ Y²); at most one n per pair, so
≤ 2xY/Y² = 2x/Y such n; similarly for m′ < Y (m ≤ x/Y²): total ≤ 4x/Y = o(x/l). [uniform;
this is EPS87's "(iii)", with (iii) being the assumption m, m′ ≥ Y — **audited**: the
one-n-per-pair count is exactly EPS87 p. 257, boxes {m < L, m′ ≤ (x+1)/L²} ∪ {m ≤ x/L²,
m′ < L}.] Henceforth m, m′ ≥ Y; note this forces p = n/m ≤ x/Y and p′ ≤ 2x/Y.

**(A5) φ(m) with only small prime factors.** Discard n with P(φ(m)) < l⁴ or P(φ(m′)) < l⁴.
Following EPS87 (4.2)–(4.3): for any integer t > 1, φ(t) = ∏_{q^a || t} (q−1)q^{a−1} presents
φ(t) together with a factorization into parts q−1 and q (each prime power q^a || t
contributing one part q−1 and a−1 parts q), all parts ≥ 2 except at most one part 1 (from
q = 2, a = 1). By a lemma of Pomerance (*On the distribution of amicable numbers. II*,
J. reine angew. Math. 325 (1981), 183–188, p. 186 — used identically by EPS87-II, GHP, PPT),
**at most 2 distinct integers t share both the value φ(t) and this factorization**. Hence,
with f(v) = number of unordered factorizations of v into parts ≥ 2,

  N(z) := #{t : 1 < φ(t) ≤ z, P(φ(t)) < l⁴} ≤ 4 Σ_{v ≤ z, P(v) < l⁴} f(v).

**Lemma A.3 (self-contained Rankin bound).** There is an absolute constant C₀ (C₀ = 30 is
admissible) such that for all z ≥ Y and all x with log log x ≥ 32(C₀ + 3):

  Σ_{v ≤ z, P(v) < l⁴} f(v) ≤ z/(4l²),  hence N(z) ≤ z/l².

*Proof.* Let σ = 1 − δ with δ := 1/(4 log l) = 1/(4(log x)^{1/3}), chosen so that
δ·log(l⁴) = 1, i.e. d^{δ} ≤ e for every l⁴-smooth-supported d ≤ l⁴ and, more to the point,
q^{δ} ≤ e for every prime q < l⁴. Rankin's trick gives

  Σ_{v ≤ z, P(v)<l⁴} f(v) ≤ z^{σ} F(σ),  F(σ) := Σ_{P(v)<l⁴} f(v)v^{−σ}
    = ∏_{d ≥ 2, P(d) < l⁴} (1 − d^{−σ})^{−1},

the Euler product being the standard generating identity for unordered factorizations into
parts ≥ 2 (each part d ≥ 2 usable with any multiplicity).

*Correct size of the exponent.* Using −log(1−t) ≤ t + t²/(1−t) for 0 < t ≤ 2^{−σ} < 0.52,

  log F(σ) ≤ A + O(1),  A := Σ_{d ≥ 2, P(d) < l⁴} d^{−σ} = ∏_{q < l⁴}(1 − q^{−σ})^{−1} − 1,

where the O(1) collects Σ_{d≥2} d^{−2σ}/(1−d^{−σ}) = O(1) (as 2σ > 3/2). **A is a sum over
all l⁴-smooth d, not over primes**, and it is *not* O(log log x): already at σ = 1, Mertens
gives ∏_{q<l⁴}(1−1/q)^{−1} ~ e^{γ}·4 log l ≈ 7.12(log x)^{1/3}. The correct evaluation is

  log ∏_{q<l⁴}(1−q^{−σ})^{−1} = Σ_{q<l⁴} q^{δ}/q + O(1)
    = ∫_{δ log 2}^{1} e^{u} du/u + O(1) = log(1/δ) + O(1) = log log(l⁴) + O(1),

by partial summation from Mertens' theorem with the substitution u = δ log t (the integral is
finite at the upper limit precisely because δ log(l⁴) = 1, and contributes its main term
log(1/δ) from the lower range where e^{u} = 1 + O(u)). Hence ∏_{q<l⁴}(1−q^{−σ})^{−1} ≍ log l
and A ≤ C₁ log l with C₁ absolute; numerically the asymptotic constant is
e·e^{γ}·4 ≈ 19.4, so C₁ ≤ 29 and C₀ := C₁ + 1 = 30 is admissible for large x. Thus

  Σ_{v ≤ z, P(v)<l⁴} f(v) ≤ z·exp(−δ log z + C₀ log l).

*The margin.* For z ≥ Y, δ log z ≥ δ log Y = (1/(4 log l))·(1/8)(log x)^{2/3} log log x
= (1/32)(log x)^{1/3} log log x = (1/32)(log log x)·log l. Therefore

  Σ_{v ≤ z, P(v)<l⁴} f(v) ≤ z·exp(−log l·[(1/32) log log x − C₀]) ≤ z·exp(−3 log l) ≤ z/(4l²)

as soon as (1/32) log log x − C₀ ≥ 3, i.e. log log x ≥ 32(C₀ + 3) (= 1056 with C₀ = 30). ∎

**Remark A.4 (why the margin is structural, and why GHP's printed exponent is fatal).** The
saving in Lemma A.3 is log l·[(1/32) log log x − C₀]: the Rankin loss C₀ log l is *of the same
order* as the main saving δ log Y, and is beaten only by the extra factor log log x carried by
Y = exp{(1/8)(log x)^{2/3} log log x}. Two consequences.
(i) The threshold is an absolute constant, but a large one (log log x ≥ 1056, i.e.
x ≥ exp(exp(1056)) with the crude C₀ above); the resulting x₀ in Theorem A.1 — and hence in
Prop. 4.3 and Theorem 4.4 — is astronomically large but absolute and effective. Nothing is
circular, and the asymptotic statements are unaffected. (EPS87-II likewise only claim
"for large x".)
(ii) With GHP's *printed* parameter L = exp((1/8)(log x)^{1/3} log log x) (§3.2) one would get
δ log Y = (1/32) log log x = o(log l), which does **not** beat the Rankin loss C₀ log l, and
Lemma A.3 would fail outright. So the discrepancy flagged in §3.2 is a **fatal typo in the
quotation, not a cosmetic one**: the (log x)^{2/3} exponent of the original EPS87-II (p. 257)
is exactly what makes this step work, and it is the exponent used here throughout.

Discard count: for each prime p ≤ x/Y (forced by m ≥ Y), the discarded n = mp with
P(φ(m)) < l⁴ have m ≤ x/p, φ(m) ≤ x/p, and z = x/p ≥ Y, so at most N(x/p) ≤ x/(p l²)
choices of m; n = mp is then determined. Summing: Σ_{p ≤ x/Y} x/(p l²) ≪ x log log x/l² =
o(x/l). Same for m′ (n = m′p′ − k is determined by (m′, p′) since k is fixed). [uniform —
**audited**: k appears only via the determination n = m′p′ − k, one n per pair.]

**(A6) Final count.** Remaining n: by symmetry assume p > p′ (the case p < p′ is identical
with the roles of n, n+k swapped, giving a factor 2; p = p′ was excluded). Let
r = P(φ(m)) ≥ l⁴ (prime). Since r | φ(m) and r² ∤-considerations: r | φ(m) means either
q ≡ 1 (mod r) for some prime q | m, or r² | m; the latter is impossible: r² | m | n is a
squarefull divisor > l³ of n, excluded by (A2). So **∃ prime q | m with q ≡ 1 (mod r)**.
Also φ(m) | φ(n) (m | n), so r | φ(n) = φ(n+k) = φ(m′)(p′−1); as before, either r² | n+k
(excluded by (A2)) or **∃ prime q′ | n+k with q′ ≡ 1 (mod r)**; then q′ ≥ 1 + l⁴ > k.
[**The k-critical step, audited:**] gcd(m, q′) = 1: a common prime divisor would divide both
n and n+k, hence k; but q′ is prime and q′ > k, so q′ ∤ k, forcing q′ ∤ m. Therefore
q′ | n + k = mp + k determines the residue p ≡ −k·m^{−1} (mod q′), a single class a(m, q′, k)
mod q′. Moreover q′ | n+k gives q′ ≤ P(n+k) = p′ < p ≤ x/m, so q′ < x/m and
#{p ≤ x/m : p ≡ a (mod q′)} ≤ x/(m q′) + 1 ≤ 2x/(m q′). The number of surviving n is thus

  ≤ 2 Σ_{r ≥ l⁴ prime} Σ_{q ≡ 1 (r)} Σ_{m ≤ x, q | m} Σ_{q′ ≡ 1 (r), q′ ≤ x} 2x/(m q′)
  ≪ x Σ_r [Σ_{q′≤x, q′≡1(r)} 1/q′] [Σ_{q≤x, q≡1(r)} (1/q) Σ_{m′≤x/q} 1/m′·(1/1)]
  ≪ x Σ_{r ≥ l⁴} (log x/r)·(log x/r)·log x = x (log x)³ Σ_{r ≥ l⁴} r^{−2}
  ≪ x (log x)³ / l⁴ = o(x/l).

(Here Σ_{t ≤ x, t ≡ 1 (r)} 1/t ≤ Σ_{j ≤ x/r} 1/(jr) ≪ (log x)/r was used twice, and
Σ_{m ≤ x, q|m} 1/m = (1/q)Σ_{m′ ≤ x/q}1/m′ ≪ (log x)/q.) [k enters only through the residue
class a(m, q′, k) — its exact value is irrelevant to the count — and through q′ > k in the
gcd step. **Uniform for k ≤ l.**]

Total over (A0)–(A6): P₁(x;k) ≪ x(log x)³/l⁴ + x log log x/l² + x/Y + Ψ-terms = o(x/l), and
< x/l for x > x₀ absolute. ∎

**Audit summary (adversarial phase, item-by-item).**
1. *Uniformity of constants in k*: k enters at exactly four points — (n+k ≤ 2x) in (A1);
   (p = p′ ⟹ p | k) before (A3); (n = m′p′ − k determined) in (A5); (q′ | k impossible) in
   (A6). Each needs only k < min(Y², l⁴) — true for k ≤ l. All other constants are absolute.
   **Pass.**
2. *Exceptional-set counting uniform*: the discarded sets (A1), (A2), (A4), (A5) are counted
   by k-free arguments (shifts only enlarge x to 2x). **Pass.**
3. *Where "k = 1" was structural in EPS87*: (a) EPS87 used gcd(n, n+1) = 1 to get
   gcd(m, m′) = 1 hence class (B) empty; for general k class (B) is nonempty and is exactly
   the Theorem-A/GHP-structured family — this is GHP's contribution, reproved above. (b) EPS87
   used gcd(m, q′) = 1 from consecutiveness; for general k this needs q′ > k — PPT's
   observation, verified above. No other use of k = 1. **Pass.**
4. *Pomerance's factorization lemma*: cited, not reproved (published; used identically by
   three refereed papers). Note: the naive "≤ 2 readings per part" version of the lemma is
   false for the coarse factorization into parts (q−1)q^{a−1} (counterexample:
   φ(35) = φ(45) = φ(56) = φ(72) = 24 with common coarse multiset {4, 6}); the lemma is about
   the fine factorization with parts q−1 and q separately, which distinguishes these
   (35 ↦ {4,6}, 45 ↦ {2,3,4}, 56 ↦ {1,2,2,6}, 72 ↦ {1,2,2,2,3}). This is the single cited
   ingredient of App. A not reproved here. **Flagged, low risk.**

---

## Appendix B. Why c ≥ 2 is out of reach for this method (precise gap statement)

**B.1 The union bound is exhausted at c = 2 — conditionally sharp.** Under Bateman–Horn
(GHP Cor. 1 = PPT Thm B): P(x;k) ~ 2C₂c(k)x/(log x)² for even k, with c(k) ≥ (2k)^{-1}.
Then the expected number of colliding pairs in a random window of length L = (log x)^c is

  (1/x)Σ_{h ≤ L}(L−h)P(x;h) ≍ L Σ_{h ≤ L} c(h)/(log x)² ≫ L log L/(log x)² ≍
  (log x)^{c−2} log log x,

which → ∞ for every c ≥ 2. So for c ≥ 2 the first moment does not (and, conditionally,
cannot) show that a positive proportion of windows is collision-free; for c > 2 the standard
heuristic (collision events at distinct offsets behave quasi-independently) predicts that
**almost every window has a collision, i.e., the almost-all form of Theorem 4.4 is expected
to be FALSE for every c > 2** (and already at c = 2, where the expectation is ≍ log log x).
Any proof for c ≥ 2 must therefore exploit *concentration/clustering* of collisions on few n,
or construct special windows.

**B.2 The proposed shortcut is unconditionally false.** The attack plan (and the retracted
forum comment) hoped for: ∀A, B: P(x;k) ≪_{A,B} x/(log x)^A uniformly for k ≤ (log x)^B.
This is false unconditionally for A ≥ 51: by Kim's Theorem 1.1 (§3.4), with j = 50# there is
for each large x some k_x ∈ {j, ..., 49j} with P₀(k_x;x) ≫ x/(log x)^{50}; by pigeonhole some
fixed even k ≤ 49·50# has P(x;k) ≫ x/(log x)^{50} for infinitely many x. Since 49·50# is an
(enormous but) absolute constant, it is ≤ (log x)^B eventually for any B ≥ 1. Hence the c < 2
route via structured/exceptional decomposition is not a convenience but a necessity, and no
polylog-uniform (log x)^{-A} collision bound with large A exists.

**B.3 What exactly remains open, and plausible truth values.**

- *2 ≤ c: existence form.* Needed: for L = (log x)^c, one window (n, n+L], n ≤ x, avoiding all
  collisions. The bad set has (conjectural) density → 1, but the collisions are highly
  structured: each even-h collision in a window is of Theorem-A form (up to exceptional sets),
  i.e. requires m = j·q ∈ window with q, and (j/g)(q−1)/((j+h)/g) + 1-type companion, prime —
  a twin-prime-like double event attached to a divisor pattern. A Poisson model with intensity
  λ(x) ≍ (log x)^{c−2} log log x per window predicts ≍ x·e^{−λ} collision-free windows: this
  is ≫ 1 for every c < 3 (since λ = o(log x)), so **YES is plausible for all c < 3**; for
  c > 3 naive Poisson predicts x·e^{−λ} → 0, so the truth for large c genuinely depends on
  clustering. Clustering is real: GHP Thm 4 and their §5 data show equal-totient values occur
  in arithmetic progressions (e.g. φ(583200+30i) constant for i = 0..5), so collisions
  concentrate; this pushes the collision-free count up and keeps YES plausible for all c —
  but nothing resembling a proof is in sight in either direction. Deciding c ≥ 2 appears to
  need second-moment estimates for Theorem-A configurations (a Montgomery–Soundararajan-style
  variance for the GHP families), which in turn needs uniform two-point Bateman–Horn-type
  correlations — currently unavailable.
- *NO-direction for large c* would require showing every length-(log x)^c window contains a
  structured collision — i.e., a lower-bound sieve producing a prime pair in each of x/L
  windows simultaneously: strictly beyond Maynard–Tao technology (which gives infinitude, not
  all-windows coverage).
- *Between the theorem and the conjectural break-point*: Theorem 4.4 actually gives windows up
  to L = (log x)²/((log log x)(log log log x)·ω(x)) for any ω(x) → ∞; the almost-all threshold
  is conjecturally L ≍ (log x)²/log log x exactly (B.1 lower bound vs. Theorem 4.4), i.e. the
  first-moment analysis here is essentially best possible, off by at most (log log x)^{O(1)}.

**B.4 Comparison with the EPS-scale regime.** In the opposite regime of very long windows, the
site remark (§3.6) asserts K ≤ n/exp(c(log n)^{1/3}); whatever its precise provenance, no
polylog information flows from it: it is consistent with (and far from) both YES and NO for
every fixed c.

---

## §7 Numerics (x = 10^6, 10^7; script `numerics_1004.py`, this directory)

P(x;h) = #{m ≤ x: φ(m) = φ(m+h)} computed by full φ-sieve to 10^7 + 20:

| h | P(10^6;h) | P(10^7;h) | | h | P(10^6;h) | P(10^7;h) |
|---|-----------|-----------|-|---|-----------|-----------|
| 1 | 68 | 142 | | 11 | 77 | 141 |
| 2 | 2588 | 17286 | | 12 | 4561 | 28319 |
| 3 | 2 | 2 | | 13 | 79 | 152 |
| 4 | 1536 | 9730 | | 14 | 1540 | 9517 |
| 5 | 20 | 43 | | 15 | 4 | 4 |
| 6 | 7594 | 49754 | | 16 | 650 | 3371 |
| 7 | 81 | 162 | | 17 | 89 | 162 |
| 8 | 985 | 5596 | | 18 | 3376 | 20464 |
| 9 | 2 | 2 | | 19 | 81 | 164 |
| 10 | 917 | 5393 | | 20 | 1297 | 7782 |

Consistency checks (all pass):
- Even h grow like c(h)x/(log x)²: e.g. h = 2: ratio 17286/2588 = 6.68 vs. predicted
  10·(log 10^6/log 10^7)² = 7.35 (singular series and secondary terms account for the gap).
- **Count hierarchy** P(x;6) > P(x;12) > P(x;18) > P(x;2) > P(x;4): at x = 10^7 this is
  49754 > 28319 > 20464 > 17286 > 9730, and it reproduces GHP Table 1 exactly at x = 10^8
  (356157 > 196539 > 139506 > 125986 > 69131) and at x = 10^{10}
  (20969365 > 11257702 > 7834367 > 7558421 > 4047331).
  *This is a hierarchy of counts, not of the constants c(k)*: computing c(k) from
  GHP Cor. 1 / PPT (7) gives c(2) = 0.2500, c(4) = 0.1250, c(6) = 0.6435, c(12) = 0.3218,
  c(18) = 0.2145, i.e. the constant order is c(6) > c(12) > **c(2) > c(18)** > c(4) — the
  opposite of the count order at the pair (2, 18). The discrepancy is a finite-x effect: the
  ratio P(x;k)/[2C₂c(k)x/(log x)²] is not yet 1 and drifts with k,
  = 1.36, 1.53, 1.52, 1.73, **1.88** for k = 2, 4, 6, 12, 18 at x = 10^7, falling to
  1.21, 1.30, 1.31, 1.41, **1.47** at x = 10^{10}. The cause is visible in GHP Cor. 1: the
  true prediction is Σ*_j 2C₂∏*(p−1)/(p−2)∫₂^{gx/(j(j+k))} dt/[log(jt/g)·log((j+k)t/g)], and
  replacing that integral by x/(log x)² — legitimate asymptotically — loses most at finite x
  for the k admitting many, and larger, values of j (18 = 2·3² admits j = 6, 9, 18, 36, 54,
  144; k = 2 admits only j = 2). GHP's Table 5 confirms this: keeping the integral, their
  predicted/actual ratios at 10^{10} are 0.9938–0.9998 across even k ≤ 30. Since the excess
  shrinks faster for k = 18 than for k = 2 (1.88 → 1.47 vs. 1.36 → 1.21), the counts are
  consistent with P(x;2) eventually overtaking P(x;18), as c(2) > c(18) requires.
- Odd h are exceptional-only (Lemma 4.1): counts 2–164, with h ≡ 3 (mod 6) nearly extinct
  (2, 2, 4 at h = 3, 9, 15) — exactly GHP's §2 observation.
- φ(5186) = φ(5187) = φ(5188) = 2592 reproduced (the classical triple).
- Longest run of consecutive integers in [1, 10^7] with pairwise distinct φ: **length 321**
  (starting at 9491695), vs. (log 10^7)² ≈ 259.8 — the empirical maximum sits just above the
  (log x)² scale, consistent with the conjectural threshold of B.3 and comfortably above
  (log x)^c for every c < 2 at this x (e.g. (log x)^{1.9} ≈ 196). Nothing definitional is
  misread: distinctness of a window is exactly "no P(x;h)-event with both endpoints inside".

---

## §8 Final verdict

- **Problem #1004 as stated (all c > 0): OPEN — GAP-REMAINS.** The gap is precisely: decide
  windows of length L ≥ (log x)² (equivalently any fixed c ≥ 2), where the union bound is
  conditionally exhausted (B.1), the polylog-uniform power-savings shortcut is unconditionally
  false (B.2), and even the conjectural truth value is unsettled for c > 3 (B.3).
- **Proved (this document, referee-standard): YES for every fixed c < 2**, with density-one
  good n and the sharper window threshold L(log 3L)(log log 3L) = o((log x)²). Ingredients:
  PPT Thm 3.1 (uniform exceptional bound; full reconstructed proof in App. A, all
  k-dependencies audited against EPS87-II) + PPT Thm 3.3/Lemma 3.2 (uniform structured bound;
  printed proof verified) + Lemma 4.2 and Theorem 4.4 (new glue, proved here). The single
  cited-not-reproved ingredient is Pomerance's 1981 factorization lemma (App. A audit item 4).
- Classification per the house labels: overall **GAP-REMAINS**; the c < 2 sub-result is
  **SOLVED** as an assembly (its only unverified-from-scratch atom being [Po81]; with that,
  SOLVED-mod-[Po81] if one insists on full self-containment).

## References

- [EPS87-II] P. Erdős, C. Pomerance, A. Sárközy, On locally repeated values of certain
  arithmetic functions. II, Acta Math. Hungar. 49 (1987), 251–259. (users.renyi.hu/~p_erdos/1987-14.pdf)
- [EPS87-III] —, III, Proc. Amer. Math. Soc. 101 (1987), 1–7. (1987-15.pdf)
- [GHP] S. W. Graham, J. J. Holt, C. Pomerance, On the solutions to φ(n) = φ(n+k), Number
  Theory in Progress (Zakopane 1997), de Gruyter 1999, 867–882. (math.dartmouth.edu/~carlp/phi.pdf)
- [PPT] P. Pollack, C. Pomerance, E. Treviño, Sets of monotonicity for Euler's totient
  function, Ramanujan J. 30 (2013), 379–398. (campus.lakeforest.edu/trevino/monotone4.pdf, §3)
- [Po81] C. Pomerance, On the distribution of amicable numbers. II, J. reine angew. Math. 325
  (1981), 183–188.
- [Yam] T. Yamada, On equations σ(n) = σ(n+k) and φ(n) = φ(n+k), arXiv:1001.2511.
- [For] K. Ford, Solutions of φ(n) = φ(n+k) and σ(n) = σ(n+k), arXiv:2002.12155.
- [Kim] S. Kim, On the equations φ(n) = φ(n+k) and φ(p−1) = φ(q−1), csun.edu/~sungjin.
- [Tao] T. Tao, Monotone non-decreasing sequences of the Euler totient function, arXiv:2309.02325.
- [HR] H. Halberstam, H.-E. Richert, Sieve Methods, Academic Press, 1974 (Thm 5.7).
- Problem page and forum: erdosproblems.com/1004, /forum/thread/1004 (accessed 2026-07-30).
