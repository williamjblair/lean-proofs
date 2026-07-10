# Erdős #730 — audit of the claimed GPT Pro proof of infinitely many consecutive pairs

Audit date: 2026-07-10. The initial one-pass audit isolated a quantified
digit-counting gate; a same-day adversarial follow-up proved that gate FALSE
as stated and replaced it with an explicitly open range-split gate.

## 0. Problem and sources

**Problem** (erdosproblems.com/730, [EGRS75]): Are there infinitely many pairs of integers
n ≠ m such that C(2n,n) and C(2m,m) have the same set of prime divisors?
Known examples: (87,88), (607,608); triple (10003,10004,10005) (AlphaProof); OEIS A129515.
Site status: OPEN (page last edited 27 Dec 2025).

**Claim under audit**: forum comment by **Liam Price, 21:06 on 24 Jun 2026**
(https://www.erdosproblems.com/forum/discuss/730), asserting GPT Pro proved the *stronger*
statement: infinitely many **consecutive** pairs (n, n+1).

**Follow-up**: comment by **Tomodovodoo, 01:08 on 25 Jun 2026**, linking a "closing
derivation": https://chatgpt.com/share/6a3c7e81-cab8-83eb-a247-cd10b62e80fb
(conversation titled "Proof Route Mapping", model slug `gpt-5-5-pro`).

**Availability caveat (load-bearing):** the full proof exists only as a **private PDF**
("the proof document", §§2–4) that was uploaded into ChatGPT sessions. It is **not
linked anywhere public**. Public record = (a) the one-paragraph gist below, (b) the
route-mapping share, which reproduces the *algebraic* skeleton (§2) in full detail but
only *names* the analytic sections ("PDF §§3–4: Fourier estimates and the first-moment
argument"). The audit gate must therefore be evaluated against what is stated publicly
plus reconstruction.

## 1. Verbatim source material

### 1.1 Liam Price forum comment (full text)

> GPT Pro, in fact, can show the stronger result that there are infinitely many such
> pairs which are consecutive. Here is the general gist of its argument:
>
> The proof begins by converting equality of prime supports into a problem about
> base-$p$ digits. Kummer's theorem then shows that a prime can disappear from
> $\binom{2n}{n}$ or appear in $\binom{2n+2}{n+1}$ only when a certain quotient
> associated with $n+1$ or $2n+1$ has all its base-$p$ digits at most $(p-1)/2$. We
> then construct an explicit quadratic family for which $n+1=PQ$ and $2n+1=3RS$, where
> $P,Q,R,S$ are pairwise separated linear forms, so that every possible obstruction is
> attached to exactly one of four branches. On each branch, after fixing a prime
> divisor and parametrising the corresponding congruence class, the relevant quotient
> becomes a quadratic polynomial whose linear coefficient is a $p$-adic unit. This
> gives strong permutation properties modulo powers of $p$. Fourier analysis and
> bounds for incomplete quadratic sums then show that, on blocks of length $p^r$, the
> proportion of values whose first $2r$ base-$p$ digits are all restricted is
> essentially $4^{-r}$. The proof then concludes with some case checking on some
> obstruction prime range sizes.

### 1.2 Tomodovodoo forum comment (full text)

> As an addition to Liam's provided argument, a closing derivation based on the
> provided reasoning traces can be found
> [here](https://chatgpt.com/share/6a3c7e81-cab8-83eb-a247-cd10b62e80fb).

### 1.3 The "closing derivation" (ChatGPT share, final assistant message, verbatim)

User prompt in that conversation (verbatim): *"Figure out where and how the image can be
explained by the following compacted reasoning traces. An expert mathematician currently
commented: 'it never really explained or could explain how it got their, it just works'.
I pasted in both reasoning traces. (and the proof document) Clearly show where in which
reasoning trace it figured it out, and how. Essentially, a proof route mapping."*

Final answer (verbatim, minus inline file-citation markers):

> ## Verdict
>
> The expert's criticism is **fair for the compacted traces**: neither trace records the
> exact choice
> \[ (a,b)=(7,6),\qquad P=42Tx+11,\ Q=72Tx+13,\ R=28Tx+5,\ S=72Tx+19, \]
> or explicitly derives the four displayed \(\Phi\)-formulae.
>
> What happened is more precise:
>
> - **Trace 1** found the correct architecture, an earlier prototype, the
>   coefficient-search machinery, and the later \(p\)-adic/Fourier strategy.
> - **Trace 2** found the Kummer/carry criterion, but then pursued a different
>   Chebyshev–Pell–Schinzel route.
> - **The proof document itself contains the missing exact algebraic bridge.**
>
> So the formulae do not "just work," but the compacted reasoning omitted the decisive
> coefficient-selection step.
>
> ## Proof-route map
>
> | Stage | Where it appears | What was actually obtained |
> |---|---|---|
> | Convert equality of radicals into digit/carry tests | Trace 2, lines 6–10; PDF Lemma 2.1 | Kummer gives the two cofactor tests for primes dividing \(n+1\) and \(2n+1\). |
> | Search for a factorisation of both boundary integers | Trace 1, lines 29–49 | Prototype \(A=PQ,\ M=9RS=2A-1\), with four linear forms and explicit computational tests. |
> | General coefficient-matching engine | Trace 1, lines 604–669 | Brute-force search for identities \(2PQ-1=HRS\); this is the closest point where the final family could have been discovered. |
> | Exact final family | PDF §2.1, pages 2–3 | Human construction from \((2P-a)(Q+b)\), choosing \(a=7,b=6\), then parametrisation and CRT. It is absent from both traces. |
> | Four functions in the image | PDF page 3 | Direct substitution of the four prime-factor cofactors into Lemma 2.1. |
> | Why the \(\lambda_L\) matter | Trace 1 had the idea at lines 107–122 and 688–692; PDF equations (7)–(9) finish it | They turn every branch into the same quadratic \(p\)-adic permutation polynomial. |
> | Restricted-digit counting | Trace 1, lines 691–760 and 2196–2205; PDF §§3–4 | Fourier estimates and the first-moment argument. |
> | Trace 2 after the opening | Trace 2, from roughly line 1275 onward | Chebyshev factorisations and eventually a conditional Schinzel-H route—not the route used in the PDF. |
>
> ## The exact missing derivation
>
> Set \(A=n+1\), \(M=2n+1\). The goal is to arrange
> \(A=PQ\), \(M=2PQ-1=3RS\)
> with all four factors linear in one parameter.
>
> Start with the elementary identity
> \((2P-a)(Q+b)=2PQ+(2bP-aQ)-ab\).
> Therefore, imposing \(2bP-aQ=ab-1\) makes the right-hand side equal to \(2PQ-1\).
>
> The proof chooses \(a=7\), \(b=6\). This is an engineered choice, not a forced one:
> \(ab-1=41\), \(ab+1=43\) are both prime, while \(a/2b=7/12>1/2\) has the desired
> large-prime digit behaviour. The proof explicitly notes that this choice is not unique.
>
> Thus \(12P-7Q=41\), and \(2PQ-1=(2P-7)(Q+6)\). Define \(3R=2P-7\), \(S=Q+6\). Then
> \(2PQ-1=3RS\), and a second useful relation follows: \(18R-7S=-43\).
>
> A particular solution of \(12P-7Q=41\) is \(P=4,Q=1\), so \(P=4+7t\), \(Q=1+12t\).
> Requiring \(R=(2P-7)/3\) to be integral gives \(t=1+3u\):
> \(P=11+21u\), \(Q=13+36u\), \(R=5+14u\), \(S=19+36u\).
> Taking \(u=2v\) makes every factor odd:
> \(P=42v+11\), \(Q=72v+13\), \(R=28v+5\), \(S=72v+19\).
> Finally, taking \(v=Tx\), \(T=3\cdot41\cdot43\) removes the possible common factors
> \(3,41,43\). This gives the four forms used in the image.
>
> ## Deriving each displayed \(\Phi_L(c)\)
>
> A transition obstruction means that the relevant cofactor lies in \(D_p\), the set of
> integers having only "small" base-\(p\) digits.
>
> **The \(P\)-branch.** Suppose \(p^a\parallel P\), \(c=P/p^a\). The transition-test
> integer is \((n+1)/p^a=cQ\). Since \(12P-7Q=41\), we have
> \(Q=(12P-41)/7=(12p^ac-41)/7\). Therefore
> \(\Phi_P(c)=cQ=(12p^ac^2-41c)/7\).
>
> **The \(Q\)-branch.** Now \(p^a\parallel Q\), \(c=Q/p^a\), and the test integer is
> \(cP\). From \(P=(7Q+41)/12\), we get \(\Phi_Q(c)=cP=(7p^ac^2+41c)/12\).
>
> **The \(R\)-branch.** If \(p^a\parallel R\), then \((M/p^a-1)/2=(3cS-1)/2\). The
> relation \(18R-7S=-43\) gives \(S=(18R+43)/7=(18p^ac+43)/7\). Hence
> \(\Phi_R(c)=(3cS-1)/2=(54p^ac^2+129c-7)/14\).
>
> **The \(S\)-branch.** If \(p^a\parallel S\), then the test integer is \((3Rc-1)/2\).
> From \(18R=7S-43\) we obtain \(3R=(7S-43)/6\), and hence
> \(\Phi_S(c)=(3Rc-1)/2=(7p^ac^2-43c-6)/12\).
>
> This also explains the claim that these expressions are integers: each one is
> literally one of \(cQ\), \(cP\), \((3cS-1)/2\), \((3cR-1)/2\). The denominators are
> artifacts of eliminating \(P,Q,R,S\), not unexplained divisibility miracles.
>
> ## Where Trace 1 nearly found the final family
>
> Trace 1 searches for identities of the form \(P=At+B\), \(Q=Ct+D\),
> \(2PQ-1=H(Et+F)(Gt+J)\). Its code conditions are exactly coefficient matching:
> \(2AC=HEG\), \(2(AD+BC)=H(EJ+GF)\), \(2BD-1=HFJ\).
>
> The prototype found in the trace is \((A,B,C,D,H,E,F,G,J)=(15,2,24,7,9,8,1,10,3)\),
> which is precisely \(2(15t+2)(24t+7)-1=9(8t+1)(10t+3)\).
>
> The final proof family, before the last rescaling, is the tuple
> \((21,11,36,13,3,14,5,36,19)\). Indeed,
> \(2(21u+11)(36u+13)-1=3(14u+5)(36u+19)\).
>
> It satisfies every equation tested by the trace: \(2(21)(36)=3(14)(36)\),
> \(2(21\cdot13+11\cdot36)=3(14\cdot19+36\cdot5)\), \(2(11)(13)-1=3(5)(19)\).
>
> It also passes the trace's large-prime heuristic: \(HG/2E=27/7\), \(HE/2G=7/12\),
> whose fractional parts are \(6/7\) and \(7/12\), both above \(1/2\).
>
> But the trace set `Amax = 30` and therefore never considered \(C=36\). So it had the
> exact search mechanism, but its search box literally excluded the final answer. That
> is the clearest location of the missing provenance.
>
> ## Why the \(\lambda\)'s appear
>
> They are simply the slopes: \(\lambda_P=42T\), \(\lambda_Q=72T\), \(\lambda_R=28T\),
> \(\lambda_S=72T\).
>
> If \(p^a\mid L(x)\), choose the unique solution \(x_0\bmod p^a\) and write
> \(x=x_0+p^ak\). Then \(c=L(x)/p^a=c_0+\lambda_Lk\).
>
> Substituting this into every \(\Phi_L\) produces the common quadratic form
> \(\Phi_L(c_0+\lambda_Lk)=3024T^2p^ak^2+(p^au_L+b_L)k+v_L\), because
> \((12/7)(42T)^2=(7/12)(72T)^2=(54/14)(28T)^2=3024T^2\).
>
> The non-\(p^a\) parts of the linear coefficients are exactly
> \(b_P=-246T\), \(b_Q=246T\), \(b_R=258T\), \(b_S=-258T\).
>
> Consequently,
> \(G(k_1)-G(k_2)=(k_1-k_2)(3024T^2p^a(k_1+k_2)+p^au_L+b_L)\).
> For every relevant prime \(p\), the expression in parentheses is a \(p\)-adic unit, so
> \(v_p(G(k_1)-G(k_2))=v_p(k_1-k_2)\). Thus \(G\) permutes every residue system modulo
> \(p^j\). This is the rigorous realization of Trace 1's repeated "quadratic permutation
> modulo \(p^j\)" and Fourier/restricted-digit idea.
>
> ## Bottom line
>
> The exact route is: Kummer transition criterion → seek \(PQ,\ 3RS\) →
> \((2P-a)(Q+b)\) → \((a,b)=(7,6)\) → \(P,Q,R,S\) →
> \(\Phi_P,\Phi_Q,\Phi_R,\Phi_S\) → \(\lambda_L\)-progressions →
> \(p\)-adic quadratic permutations → restricted-digit first moment.
>
> Trace 1 contains almost every structural idea, but not the exact final coefficient
> choice. Trace 2 supplies only the opening Kummer intuition and then goes elsewhere.
> The proof document supplies the missing algebra that makes the image fully explainable.

(Other comments on the thread — Mercuri 10 Sep 2025, Firsching 10 Sep 2025 — concern
the (10003,10005) pair and the mo271/kummer numerical tool; not part of the claim.)

## 2. Reconstructed dependency tree with verdicts

Notation: D_p = {integers all of whose base-p digits are ≤ (p−1)/2}. All computations
below were run 2026-07-10 (scripts in scratchpad: `check1_kummer.py`,
`check2_family.py`, `check3_survivors.py`).

```
N0  Consecutive pairs (n,n+1), infinitely many                    [OPEN — hinges on N6]
 ├─ N1  Exact Kummer transition criterion (PDF "Lemma 2.1")            SOUND
 ├─ N2  Quadratic family n+1=PQ, 2n+1=3RS, branch separation           SOUND
 ├─ N3  Φ_L formulas + integrality                                     SOUND
 ├─ N4  λ-progressions + p-adic permutation lemma                      SOUND
 ├─ N5  Top prime range (p > L^{2/3}): congruence-class structure      SOUND as
 │      of obstructions ("case checking on range sizes")               structure;
 │                                                                     bound REPAIRABLE
 └─ N6  Restricted-digit counting on incomplete blocks +               *** THE GATE ***
        ├─ old interval-uniform lemma                                  FALSE
        ├─ maximal-r near-affine payment                               PAPER-PROVED/EXACT (<0.01)
        └─ separated far + short/top first-moment budget               NOT ESTABLISHED
```

### N1 — Kummer criterion. VERDICT: SOUND (elementary; proven and machine-checked)

Quantified statement (reconstructed and verified):
for n ≥ 1, supp C(2n,n) = supp C(2n+2,n+1) **iff**
1. for every odd prime power p^a ‖ n+1: (n+1)/p^a ∉ D_p, and
2. for every odd prime power p^a ‖ 2n+1: ((2n+1)/p^a − 1)/2 ∉ D_p.

Proof sketch (all steps elementary, no gaps): p ∤ C(2n,n) ⟺ n ∈ D_p (Kummer: no
carries in n+n). If p ∤ (n+1)(2n+1): last digit of n is < (p−1)/2 strictly whenever
n ∈ D_p (last digit = (p−1)/2 forces p | 2n+1), so membership cannot change; if
p^a ‖ n+1: n ends in a digits (p−1), so p ∈ supp C(2n,n) always, and p drops out at
n+1 iff (n+1)/p^a ∈ D_p; if p^a ‖ 2n+1: n ends in a digits (p−1)/2 preceded by digits
of ((2n+1)/p^a − 1)/2, and n+1 has last digit (p+1)/2, so p ∈ supp C(2n+2,n+1) always
and p enters iff ((2n+1)/p^a −1)/2 ∈ D_p. p = 2 never transitions (C(2n,n) even ∀n≥1).

Machine check: criterion vs brute-force support comparison for **all n ∈ [1,2000]:
2000/2000 match, 0 mismatches**. Known pairs verified: (87,88), (607,608),
(10003,10004), (10004,10005), (10003,10005) all equal-support ✓. Bonus: criterion
finds further consecutive pairs n = 199, 237, 467, 967, 1127, 1319, 1483, 1903, 1943
(n = 199, 237 confirmed by literally factoring the binomial coefficients).

### N2 — Family and branch separation. VERDICT: SOUND (machine-checked, symbolic)

With T = 5289 = 3·41·43, P = 42Tx+11, Q = 72Tx+13, R = 28Tx+5, S = 72Tx+19:
- 2PQ − 1 = 3RS identically ✓; 12P−7Q = 41; 18R−7S = −43; 12P−7S = −1; 7Q−18R = 1 ✓.
- Hence gcd(P,Q) | 41, gcd(R,S) | 43, gcd(P,S) = gcd(Q,R) = 1, gcd(P,R) | 7,
  gcd(Q,S) | 6; residues mod 2,3,41,43 are fixed units and P ≡ 4, R ≡ 5 (mod 7),
  Q ≡ 1 (mod 6): **every obstruction prime divides exactly one branch** ✓
  (also confirmed on all x ≤ 3000: no shared prime ever observed).
- Fixed primes: n+1 ≡ {1,2,3,20,14} and 2n+1 ≡ {1,0,5,39,27} mod {2,3,7,41,43}: so
  2, 41, 43 never divide (n+1)(2n+1); 3 ‖ 2n+1 always, and (RS−1)/2 ≡ 2 (mod 3)
  forces a base-3 digit 2 > 1, so **p = 3 is deterministically harmless**
  (verified for all x ≤ 3000) ✓.
- Caveat found in audit: 7 is NOT excluded from Q,S (72T ≡ 1 mod 7); 7 is just an
  ordinary "variable" obstruction prime. Harmless because 7 ∤ b_L (N4). The
  route-map's wording is loose here but the structure is unaffected.

### N3 — Φ formulas. VERDICT: SOUND (machine-checked, symbolic)

Φ_P = (12p^a c²−41c)/7 = cQ, Φ_Q = (7p^a c²+41c)/12 = cP,
Φ_R = (54p^a c²+129c−7)/14 = (3cS−1)/2, Φ_S = (7p^a c²−43c−6)/12 = (3Rc−1)/2 —
all four verified symbolically; integrality is by construction (each equals one of
the manifestly integral test integers from N1) ✓.

### N4 — Permutation lemma. VERDICT: SOUND (machine-checked, symbolic + sampled)

Substituting x = x₀ + p^a k gives, on every branch,
G(k) = 3024T²·p^a·k² + (p^a u_L + b_L)k + v_L with
(12/7)(42T)² = (7/12)(72T)² = (54/14)(28T)² = 3024T² = 84 591 927 504 ✓ and
b_P = −246T = −2·3²·41²·43, b_Q = 246T, b_R = 258T = 2·3²·41·43², b_S = −258T ✓
(symbolically verified). Since a ≥ 1 the difference quotient
3024T²p^a(k₁+k₂) + p^a u_L + b_L ≡ b_L (mod p), and p ∤ b_L for all p ∉ {2,3,41,43}
— exactly the primes excluded by N2. Hence v_p(G(k₁)−G(k₂)) = v_p(k₁−k₂), so G is a
p-adic isometry and permutes Z/p^j for every j. Verified exhaustively for 25 random
(branch, p ≤ 200, a ∈ {1,2}) cases mod p² / p³, plus (p,a,branch) = (7,2,Q) ✓.

Consequences: on any FULL block of k of length p^{2r}, the count of k with the first
2r digits of G(k) restricted is EXACTLY ((p+1)/2)^{2r} — density 4^{-r}(1+1/p)^{2r},
no error term, no Fourier. **All difficulty is concentrated in incomplete blocks.**

### N5 — Top prime range. VERDICT: structure SOUND; quantitative bound REPAIRABLE

For p ‖ L with small cofactor c (2-digit regime, 12c²/7 < (p−1)/2 roughly
c ≲ 0.5√p), the test integer has exactly 2 base-p digits and the digit condition
degenerates to a **congruence on c**, computed in this audit and confirmed against
all x ≤ 3000 with **zero mismatches**:
- P-branch: obstruction ⟺ c ≡ 3, 4 (mod 7)  (units digit = ((12c² mod 7)p − 41c)/7;
  12c² mod 7 ∈ {5,3,6}, only 3 < 7/2). Observed 277/1374 events.
- R-branch: obstruction ⟺ c ≡ 5, 9 (mod 14) (54c² mod 14 ∈ {12,10,6}, only 6 < 7).
  Observed 336/1378.
- Q- and S-branches: c coprime to 12 ⟹ 7c² ≡ 7 (mod 12) > 6 ⟹ **never obstructed**
  (0 events observed) — this is precisely the engineered "a/2b = 7/12 > 1/2".
So in the range p > L^{2/3} (where NO equidistribution statement is possible — the
congruence class of x mod p contains ≪ p^{1/2} points of [1,X]) the bad set is an
explicit union {c | L(x), c in a bad class, L(x)/c prime}. Bounding it needs only an
upper-bound sieve (Brun–Titchmarsh/Selberg for the linear forms) — standard, but the
sieve constant (≈2) enters the final budget (see gate). Repairable, not free.

### N6 — Incomplete-block restricted-digit counting + summability.
### OLD UNIFORM FORM FALSE; CORRECTED GATE OPEN.

**Adversarial follow-up (proved, exact).**  Put `H=(p+1)/2` and
`s=max(2r-a,0)`.  On the admissible Q branch, `b_Q=1,301,094` is a p-adic
unit for `p=5,7,11`.  At `a=2r`, reduction modulo `p^(2r)` gives exactly

```text
G(k) = b_Q k+v.
```

After removing the one output residue that would make `p | c(k)`, partition
the `H^r` restricted r-digit outputs by residue modulo `b_Q p`.  One class
has at least `(H-1)H^(r-1)/(b_Q p)` members.  Translate the k-interval so
that class is the affine image; all of its parameters span less than `p^r`
and all outputs have r restricted lower digits and r zero upper digits.
Extending the interval to `p^r` times any fixed polylogarithm does not remove
the hits.  The ratio to the old proposed main term grows like
`(p/H)^r/poly(r)`, hence tends to infinity.

More generally, exact subtraction shows

```text
G(k+t)-G(k)-b_Q t = p^a t (A(2k+t)+u_Q).
```

Partitioning outputs modulo `b_Q p^max(s,1)` therefore yields the precise
failure criterion

```text
(p/H)^r p^(-s) / poly(r) -> infinity.
```

In particular the old bound fails whenever
`s <= (log_p(p/H)-epsilon)r` for fixed `epsilon>0` and large r.  Merely
requiring `a<2r` does not repair it.  Full proof and exact diagnostics are in
`compute730/campaign_uniform/`.

**The original gate demanded the following FALSE uniform shape:**
  #{k ∈ I : first 2r base-p digits of G(k) restricted} ≤ 4^{-r}|I| + E(p,r,I)
with E explicit and uniform over every obstruction prime p, every branch, every
congruence class (x₀, a), and incomplete intervals I, such that the total error plus
the total of the main terms over all (p, a, branch, range) is < 1 − δ.

**What is publicly stated**: one sentence — "on blocks of length p^r, the proportion
of values whose first 2r base-p digits are all restricted is essentially 4^{-r}" —
plus a pointer to non-public "PDF §§3–4". No error term, no uniformity statement, no
summability computation is available anywhere public. The phrase "essentially 4^{-r}"
appears exactly at the classic failure point:

**The regime is exactly square-root-critical.** Blocks of length p^r against a digit
condition mod p^{2r}: |I| = √(modulus). Generic completion + complete-sum bounds give
error ~ √(p^{2r})·polylog = p^r·polylog ≥ main term p^r·4^{-r} — vacuous. Two
structural facts remain useful outside the counterexample band: (i) all complete
sums of e(hG(k)/p^m) vanish for p ∤ h (G is a permutation, N4), and (ii) the quadratic
coefficient of G carries an extra factor p^a, so the surviving frequencies after
completion live in a sparse arithmetic progression.  They cannot rescue the old
uniform statement because its near-affine count is genuinely too large.  A restricted
bound in a quantitatively separated range remains plausible but unproved, and its
polylog/constant losses feed directly into a budget with almost no slack.

**The summability budget (computed in this audit).** Empirics on x ∈ [1,3000]
(every number involved fully factored; events = (branch, p, a) obstructions):
- E[#obstructions per x] = 1791/3000 ≈ **0.597**; Pr[x bad] = 0.481;
  survivor density **0.519**, stable per 600-block (0.505–0.552).
- Split by γ = log p / log L: middle range γ ≤ 2/3 ≈ 0.38 of expectation; top range
  γ > 2/3 ≈ 0.22.
The *provable* version of each piece pays: (a) middle range — the digit budget is
capped by the block length at 2r ≈ 2(1−γ)/γ digits versus the ≈ (2−γ)/γ digits the
heuristic uses, a uniform factor-2 loss per event: 0.38 → ≈ 0.76; (b) top range —
upper-bound sieve constant ≈ 2: 0.22 → ≈ 0.43. Naive provable total ≈ **1.2 > 1**:
**the first moment does not close under the publicly stated bounds**, even though the
true value (0.60) is comfortably < 1. Closing the gap requires sharper range-splitting
— e.g., in the 3-digit regime (L^{1/2} < p < L^{2/3}) the two determined digits give a
congruence factor ≈ 1/3 (deterministic, as in N5) times one equidistributed digit,
beating the pure Fourier bound by ≈ ×2.4 there — precisely the kind of "case checking
on some obstruction prime range sizes" the gist alludes to. Whether the PDF actually
performs a split whose constants sum below 1, with uniform error terms, cannot be
determined: **that text is not public**.

**Gate outcome: old lemma FALSE; corrected far/top gate NOT PASSED.**  The failure is
mathematical, not merely a missing public error term.  The live residual is one
range-split lemma: establish an explicit incomplete-block estimate in
`s >= (log_p(p/H)+1/12)r` and close its errors plus the short/top-range
contribution below `0.99-delta`.  The complementary near-affine band is now
proved to cost less than `0.01` for every `X>=2^57`, using maximal admissible
`r` and valuation rarity; see `compute730/campaign_uniform/repair/`.

## 3. Numerical certificates produced by this audit

Because N1 is elementary and fully verified, every family survivor is an
unconditionally certified consecutive pair. Smallest: x = 2 gives
**n = 338 381 863 522**, i.e. C(2n,n) and C(2n+2,n+1) share prime support, certified
by factoring n+1 = P·Q and 2n+1 = 3·R·S (P,Q,R,S ≈ 10⁵–10⁶) and checking the digit
tests. First survivor x values: 2, 3, 7, 8, 9, 11, 12, 15, 16, 18, 19, 21, 22, 23, 26.
1556 certified pairs from x ≤ 3000 alone. (These certify *existence in bulk*, not
infinitude — infinitude is exactly N6.)

## 4. VERDICT

**viable-pending-far/top-X.**  The old uniform lemma is false.  This does
**not** refute Erdős #730 or the possibility that the explicit family works after a
different valuation split.

The near-affine part of the corrected split is now proved on paper and
exact-arithmetic audited, with Lean intake still pending.  With `C=2`,
`eta=1/12`, and maximal admissible `r`, its normalized contribution is
less than `1/100` for all `X>=2^57`; the exact rational certificate is

```text
232437037423222418449 / 27831344977224191180800 < 1/100.
```

The ONE residual is the following separated counting/first-moment lemma:

> **Separated far/top lemma (OPEN).**  Put `H=(p+1)/2`,
> `s=max(2r-a,0)`, and `kappa_p=log_p(p/H)`.  There are explicit absolute
> constants `B,delta>0` and explicit errors `E_far` such that:
> (i) for every relevant prime, admissible branch/root, and interval
> `|I|>=p^r(log p^r)^2` with `s >= (kappa_p+1/12)r`, the restricted-digit count is at
> most `(H/p)^(2r)|I|(1+(log p^r)^(-1))+E_far`; and
> (ii) the normalized sum of the far main terms and errors plus the
> short/top-range contribution is at most `0.99-delta`, uniformly in the family cutoff.

Neither part of this residual is proved here.  Sparse completion is relevant
only to the separated range.  The empirical budget still suggests headroom,
but no rigorous numerical closure is currently available.

The separated Fourier audit sharpens part (i) to one exact signed inequality.
With `Q=p^(2r)`, exact-valuation restricted set `E`, Fourier coefficients
`F(h)`, and interval sums `S_I(h)` as defined in
`campaign_uniform/repair/far/far_range_findings.md`, it is

```text
Re sum_(h=1)^(Q-1) F(h)S_I(h)
  <= |I| H^(2r) (1/H + 1/log(p^r)).
```

The exact Fourier identity, cumulative energy, sparse Gauss support, and
per-frequency completion bounds are paper-proved and exact-checked.  Their
valuation-stratified triangle majorant is exponentially too large for
`p=5,7,11`; signed cancellation is load-bearing.  The long subrange
`|I|>=(H-1)Q` is proved, but does not reach the critical scale.

## 5. Provenance note

The route-mapping conversation itself concedes that neither GPT reasoning trace
derived the final family ((a,b)=(7,6) selection is called a "human construction" /
"the proof document supplies the missing algebra"; Trace 1's search had `Amax = 30`
which excludes the answer's C = 36; Trace 2 went down a Chebyshev–Pell–Schinzel dead
end). The "GPT Pro proved it" framing in the forum comment overstates what the public
evidence shows: the strategy and the machinery are real and verify beautifully at
every elementary node, but the decisive analytic lemma exists, if at all, only in a
private document.
