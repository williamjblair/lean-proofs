# Hostile audit: Erdős 730 corrected unit-range block payment

Verdict: **PASS at the paper/exact-arithmetic level for the maximal-block subrange `2<=a<=r`; not kernel-expanded as a global payment; full gate OPEN.**  The aligned-block count, root-class normalization, exact geometric double sum, 166-prime rational certificate, integer tail, endpoint-cover factor, and four-branch union factor all reproduce independently.  No producer verifier or campaign helper is imported by the hostile verifier.

The exported Lean module proves the generic quadratic identity, its square-modulus consequence, a cross-multiplied implication from four explicit hypotheses, and only the terminal numerical fact `58/125<1/2`.  It does **not** formalize the branch root classes, p-adic permutation, aligned-block digit count, arbitrary interval cover, maximal-`r` selection, double series, 166-prime sum, tail, or four-branch aggregation.  The candidate findings mostly acknowledge this paper/kernel boundary; they must not be upgraded to an attested uniform theorem without those missing compositions.

The exact remaining gate is unchanged: for some explicit `delta>0`, uniformly for every `X>=2^57`, the normalized maximal-`r` contribution with `a=1` plus a separately quantified short/top contribution must be at most `263/500-delta`.

## Frozen artifacts

Producer artifacts were audited at these SHA-256 values and were not edited:

```text
f1df0d32fdced6794f7c11948841a816779512f1f173dc58745074b6733b9930  ErdosProblems/Erdos730UnitRangeBlock.lean
b380cf779951ab63d13252ade920f16def8dc143e1e295b91d576190dd691e19  compute730/campaign_uniform/repair/far/unit_range_block.py
cc4e3e18e8794e3c0776130272e409f240cec03395a23f405c2371604a2276b2  compute730/campaign_uniform/repair/far/test_unit_range_block.py
9c3652f5336751d6208b9416e191499b973790abb1d13494cd634be25d05fc55  compute730/campaign_uniform/repair/far/unit_range_block_findings.md
79a3e0b5f3e2eeb4c88406b5e4268a1c6c2facfbd03753c44d1a459bbb949c89  docs/plans/2026-07-10-erdos730-unit-range-block.md
```

Independent audit artifacts before this report:

```text
07ab4e2656f573942995974b7d02d04719d308a7b7c1bc8d9f552bf178918b75  ErdosProblems/Erdos730UnitRangeBlockAudit.lean
637604260797f82413d1a827524192f522060b847a65fc436d74b644ffc952f5  compute730/campaign_uniform/repair/far/unit_range_block_hostile_verify.py
a3086e00cdec1e31b954359a5ed784b814dddf6dc97bb53cee186637f5e4d248  compute730/campaign_uniform/repair/far/test_unit_range_block_hostile_verify.py
ae0357facf8e603d735da235fc2408ee698920f1f4b6f362ae65d24e350315c7  docs/plans/2026-07-10-erdos730-unit-range-block-hostile-audit.md
```

## Exact dependency tree

For a relevant odd prime `p>=5`, exact exponent `a>=1`, and selected block exponent `r>=1`, put

```text
q=p^a,  P=p^r,  H=(p+1)/2,
M=(H-1)H^(r-1),
rho_(p,r)=M/P.
```

The audited route is:

```text
U0  long root class, maximal r, and 2<=a<=r
|
+- U1 exact affine root class
|  +- one root x0 modulo q on every available branch
|  +- representatives x=x0+qk form a consecutive k-interval of length N
|  `- q(N-1)<=X
|
+- U2 p-adic isometry of the quadratic branch map
|  `- G(k1)-G(k2)=(k1-k2)*(p^a*(...)+b), p does not divide b
|
+- U3 aligned P-block count
|  +- low r output digits depend only on u in k=u+Pv
|  +- u -> G(u) mod P is a permutation
|  `- exact valuation deletes one allowed least digit
|     `- exactly M low-word survivors per full aligned block
|
+- U4 arbitrary translated interval cover
|  `- C<=M(floor(N/P)+2), hence CP<=M(N+2P)
|
+- U5 critical normalization
|  +- maximal r gives N>=P(log P)^2
|  +- 2<=a<=r, p>=5, and log 5>1 give 4P<=N
|  `- CqP<=2MX, hence C/X<=2rho_(p,r)/p^a
|
+- U6 remove the maximal-r restriction conservatively
|  `- for each p and branch, sum all a>=2 and r>=a
|
+- U7 exact double geometric series
|  `- S_p=(p+1)/(p(p-1)(2p+1))
|
+- U8 prime aggregation
|  +- 166 primes from 5 through 997: sum S_p<57/1000
|  +- p>1000: S_p<1/(p(p-1)); integer tail=1/1000
|  `- endpoint factor 2 and branch factor 4
|     `- total <58/125<1/2
|
`- U9 complement
   +- long maximal-r first-power classes a=1
   `- classes without r=1 plus the separately defined short/top range
```

Per-node verdicts:

- **U1 PASS.** Exact enumeration of 396 available root-class/cutoff cases agrees with direct scanning.  When the class is nonempty, its endpoint span is exactly `q(N-1)`, so the producer's orientation `q(N-1)<=X` is correct.  The stronger bound `q(N-1)<=X-1` holds for the stated `1<=x<=X` convention.
- **U2 PASS at paper level.** The difference quotient is a unit modulo every available prime.  The only unavailable cases among the 166 checked primes are P/R at `p=7` and all four branches at `p=41,43`; adding fictitious positive payments for them is conservative.
- **U3 PASS.** The hostile verifier checks 662 complete aligned blocks, 65,266 parameters, and ten branch/prime/exponent cases.  Every low-word count is exactly `M`; every full `2r`-digit count is at most `M`.
- **U4 PASS.** There are 11,508 pure translated-block checks, including negative starts and exact alignment, and 6,360 actual branch-map interval checks.  The maximum number of boundary blocks beyond `floor(N/P)` is exactly two.  Partial boundary pieces are subsets of full aligned blocks, so charging `M` to each is valid.
- **U5 PASS.** Four actual root classes reproduce every premise and the cleared conclusion.  The boundary case `(a,r)=(2,2)` occurs on the Q branch at `p=5`, `X=12,500`: `N=500`, `C=42`, `P=25`, `M=6`, `q(N-1)=12,475`, and the cross-bound margin is `123,750`.
- **U6 PASS.** Maximal `r` is unique whenever it exists because `p^r(r log p)^2` is strictly increasing in positive integer `r`.  Each `(branch,p,a)` contributes at most one actual `r`; summing every `r>=a` is therefore an upper bound, not an assumption that all those `r` occur.
- **U7 PASS.** The closed form is independently derived and finite rectangular partial sums approach it from below for `p=5,7,11,101`.
- **U8 PASS in exact arithmetic.** The prime sieve, rational sum, strict pointwise tail inequality, integer telescoping, and factors `2` and `4` all reproduce.
- **U9 OPEN.** The candidate does not pay either term and does not claim a full conclusion.

## Aligned-block algebra and exact deleted digit

For

```text
G(k)=A p^a k^2+(p^a u+b)k+v
```

and `k=x+Pz`, direct expansion gives

```text
G(x+Pz)=G(x)+Pz(2Ap^a x+p^a u+b)+Ap^aP^2z^2.
```

Thus the low `r` output digits on a full aligned block depend only on `x mod P`.  Moreover

```text
G(k1)-G(k2)
 =(k1-k2)*(Ap^a(k1+k2)+p^a u+b),
```

and the second factor is congruent to `b` modulo `p`.  On every available branch `p` does not divide `b`, so `G` is a p-adic isometry and permutes residues modulo `P`.

The exact-valuation condition is not silently replaced by mere divisibility.  In the P/Q branches, `p|c` is equivalent to least output digit `0`; in R/S, it is equivalent to least output digit `(p-1)/2`.  Both forbidden values belong to the restricted alphabet `{0,...,H-1}`.  Deleting that one least digit leaves exactly

```text
(H-1)H^(r-1)=M
```

allowed low words.  The independent audit checks this equivalence on 304,138 actual root-class residues.

## Root classes, maximal `r`, and range boundaries

For an available affine branch `L(x)=lambda*x+mu`, the unit slope modulo `p` supplies a unique root `x0 mod q`.  The representatives in `1<=x<=X` are

```text
x_first, x_first+q, ..., x_last,
```

so their corresponding `k` values form one translated integer interval and

```text
x_last-x_first=q(N-1)<=X-1<X.
```

This proves the exact orientation needed by the normalized cross inequality.  No assumption that the root class starts at zero is used.

The critical thresholds independently reproduce, among others,

```text
p=5: 13,260,2915,25903,...
p=7: 27,743,11690,...
p=11: 64,2783,68879,...
```

for `r=1,2,...`; exact rational logarithm intervals certify the integer ceilings and `log 5>1`.  Strict monotonicity makes the maximal choice unique.  If no `r>=1` fits the actual `N`, the class is short and is not charged by the `58/125` payment.

The natural-exponent partition is exact for every `a,r>=1`:

```text
s=max(2r-a,0)<r      iff r+1<=a             strict band,
s>=r and a>=2        iff 2<=a<=r            unit range,
s>=r and a=1                                  first-power residue.
```

The audit checks all `256^2=65,536` pairs: 32,640 strict, 32,640 unit-range, and 256 first-power.  Hence `a=r` belongs to the new payment, `a=r+1` belongs to the earlier strict-band payment, and `(a,r)=(2,2)` is included.  There is no exponent overlap between the two paid bands.

Across a separate grid of actual root classes, the maximal assignment counts are 262 short, 74 strict, 28 unit-range, and 56 first-power.  Short means precisely that no `r=1` critical block exists.  The candidate does not give a quantified definition of the broader phrase "top range," so disjointness of a future top sieve cannot yet be a theorem.  This causes no current double count: no short/top amount is included in `58/125` or subtracted from the remaining `263/500`.  If a future top upper bound overlaps, adding upper bounds remains conservative, but the final gate should state the sets explicitly.

## Exact geometric and prime sums

With `H=(p+1)/2`,

```text
rho_(p,r)=(H-1)H^(r-1)/p^r.
```

For one branch, after dropping maximality,

```text
S_p
 = sum_(a>=2) p^(-a) sum_(r>=a) rho_(p,r)
 = (2p/(p+1)) * sum_(a>=2) (H/p^2)^a
 = (p+1)/(p(p-1)(2p+1)).
```

The independently generated 166 primes `5<=p<=997` give the reduced exact fraction

```text
2551637136822295606673912499820434751495888857709372375239852572903011832860218855833404247426801174347769650600008067570500105549076086113635313112230015059019327382852139285508009605317539069972625741096377717100170233059206993048531294849935158393547406303221963863070914798129086487939951756009573029472843226467254685009560715189430465628523340851384431683756087362747839366964604174422406004416055861400056474051244127278676146188240580384438745977707059
/
44987488249554444250885501771470105885368464693114878392390476246508135062978277083980415423579453355954828385370718510345153016407846832381022237166482492731373346086482188441345344624786013951698729623732415473169387053515047646431731700882498033030667166362581768930494267383225219651026401304537445887082478682661982156178645235545883070215575730847275052641604866555864643065786895322953309224849628088823852690667307134094790136733935429043787677106280000.
```

Its exact positive margin below `57/1000` has the same denominator and numerator

```text
12649693402307715626561101153361283970113629798175693126404573147951865729542937953479431717227666941655567366122887519173616386171183332082954406259487026668953344077345455648675038295263725274201847456369964870484828991150722798077412100367229489200622179445196965967258442714751032168553118349061386090858058444478297892622063236684869373764475806910246316815390030936445287785248858985932621400372939662903129316792379364726891605593739071057151617350901.
```

For every prime `p>1000`,

```text
S_p < 1/(p(p-1)).
```

Dropping primality and using

```text
sum_(n>=1001) 1/(n(n-1))=1/1000
```

gives a strict one-branch pre-cover sum below `29/500`.  The factor `2` is exactly the endpoint/block-cover loss in `C/X<=2rho/q`; the factor `4` is only the union bound over P,Q,R,S and assumes no independence.  Therefore

```text
8*(partial+1/1000) < 58/125 < 1/2.
```

The actual rational upper bound is approximately `0.4617505401800363`; the decimal is diagnostic only, while the displayed cleared margin is exact.

Unavailable branches can only reduce this sum.  Among the 166 finite primes, 163 have four available branches, `p=7` has two, and `p=41,43` have none.  Charging four branches at every prime is conservative.

## Kernel surface and formalization boundary

The producer exposes exactly four public theorems:

```text
quadratic_block_expansion
quadratic_block_difference_dvd_sq
normalized_block_cover_cross_bound
higher_prime_power_payment_ceiling_lt_half
```

Their exact signatures and kernel assumptions are:

```text
quadratic_block_expansion:
  [propext]
quadratic_block_difference_dvd_sq:
  [propext, Quot.sound]
normalized_block_cover_cross_bound:
  [propext, Quot.sound]
higher_prime_power_payment_ceiling_lt_half:
  [propext, Classical.choice, Quot.sound]
```

Both direct source compilation and `lake build ErdosProblems.Erdos730UnitRangeBlock` succeed.  The source and audit importer contain no private declarations and no executable `sorry`, `admit`, `axiom`, `native_decide`, `of_decide`, `unsafe`, `implemented_by`, or `extern` constructs.

The formal coverage must be read literally:

- `quadratic_block_expansion` and `quadratic_block_difference_dvd_sq` are generic polynomial algebra;
- `normalized_block_cover_cross_bound` assumes `4P<=N`, `q(N-1)<=X`, and `CP<=M(N+2P)` rather than deriving them from a branch class;
- `higher_prime_power_payment_ceiling_lt_half` proves only the comparison between two rational constants.

No theorem in this module states a digit-count bound, a branch-level normalized payment, the double series, or the `58/125` first-moment aggregation.  Thus the paper/exact result passes, but the kernel-expanded result is absent.  Before attestation, a row-independent Lean composition must connect the banked branch isometry and root classes to the aligned count and normalization, and the finite/infinite rational certificate must enter the kernel or be covered by the repository's accepted certificate mechanism.

## Single exact remaining gate

The earlier strict band costs less than `1/100`, and this unit range costs less than `58/125`.  Their exponent ranges are disjoint and

```text
1 - 1/100 - 58/125 = 263/500.
```

The one remaining analytic gate is:

> Prove that there exists an explicit `delta>0` such that, for every family cutoff `X>=2^57`, the sum of (i) the normalized obstruction contribution from every long branch class with exact exponent `a=1` and `r>=1` chosen maximally from its actual root-class length, and (ii) the separately quantified short/top contribution from classes outside the long critical-block regime, is at most `263/500-delta`.

For the first term, `s=2r-1>=r`.  The coarse block envelope remains available, but its maximal-`r` prime-band sum has not been bounded.  The short/top set and its quantitative sieve must be stated explicitly.  Returning either phrase without this uniform budget would be the exact theorem-strength gap.

## Reproduction

```bash
python3 -m pytest \
  compute730/campaign_uniform/repair/far/test_unit_range_block.py \
  compute730/campaign_uniform/repair/far/test_unit_range_block_hostile_verify.py -q
python3 compute730/campaign_uniform/repair/far/unit_range_block_hostile_verify.py --pretty
lake build ErdosProblems.Erdos730UnitRangeBlock
lake env lean ErdosProblems/Erdos730UnitRangeBlockAudit.lean
```

No producer file, shared import, manifest, attestation, or commit was changed by this audit.
