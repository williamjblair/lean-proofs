# Erdős 686 approach registry

Campaign branch: `main`

Exact targets:

```lean
def OddThueTailHypothesis : Prop :=
  ∀ k, k ∈ ({5, 7, 9, 11, 13, 15} : Finset ℕ) →
    NoLargeGapSolutionFour k (10 ^ 120)

def LargeKSmoothHypothesis : Prop :=
  ∀ k n d : ℕ, 16 ≤ k → k ≤ d →
    blockProduct k (n + d) = 4 * blockProduct k n →
    (∀ i, i ∈ Finset.Icc 1 k → ∀ q, q.Prime → q ∣ n + i → q < d + k) →
    False
```

The first declaration is in `ErdosProblems/Erdos686FinalReduction.lean`;
the second is in `ErdosProblems/Erdos686PrimeObstruction.lean`.

Verdicts are one of `active`, `proved`, `refuted`, or `blocked`. A `proved`
entry requires a complete dependency tree and exact reproduction; a `blocked`
entry must name one quantified missing lemma.

## Mandatory falsification fixtures

| Fixture | Scope | Required check |
|---|---|---|
| `k = 9`, `P_9(8) = 4 P_9(7)` | Target 1 structure | Any polynomial identity must explain why `d = 1` survives and use `d >= k` where needed. |
| `k = 15`, banked `d = 1` telescope | Target 1 structure | Same boundary check as `k = 9`. |
| `(k,n,d) = (984,3177026,4480)` | Target 2 row structure | Passes rows 1 through 16 and fails row 17; refutes every fixed row-prefix cap at 16. |
| `n = 48502` survivor cluster | Target 2 row structure | Passes through row 15 and fails at row 16 in the recorded range. |
| MalekZ all-moduli family for `(N,k) = (4,5)` | Congruence routes | A pure finite-congruence obstruction cannot be universal. |

## Target 1 routes

| ID | Family | Exact proposed leverage | Verdict | Evidence or gap |
|---|---|---|---|---|
| T1-CF | CF remainder identity | Substitute each exact quasi-convergent class into `P_k(X)-4P_k(Y)` and retain the signed integral remainder, not just `|alpha-X/Y|`. | active with larger certified floor | Kernel-checked Farey/CF certificates now exclude every target row throughout `10^120 <= d < 10^1000`. For k=5, a genuine root also satisfies the exact floor pin `g^2=floor(5A_3/A_5)`; among 341 stored rows only three nontrivial square/divisor floors survive and none is a root. No theorem controls the tail beginning at `10^1000`. |
| T1-VAL | p-adic valuation | A prime power `p^e | d`, `p >= k`, localizes uniquely and forces a square lift, cubic at the center; valuation concentration replaces uniqueness when `p<k`. | proved and Lean-banked | For `p>=k`, `p^(2e)<A_k*d`, with `A_k=14,17,23,26,29,35`, and the center gives `p^(3e)<A_k*d`. For `p<k`, all valuation outside one factor loses at most `1+v_p((k-1)!)`; the exact universal constant `14!*35*13^30<10^120` excludes every whole prime-power gap `d=p^e>=10^120`, including bases 2 and 3. Mixed-prime gaps remain open. |
| T1-2P | Two-prime concentration/Pell | For `d=p^e q^f`, combine global residual cleaning with the second and third local lifts. | complete two-prime-support slice closed; Lean-banked and hostile-audited | Uniformly including `p=2,3`, same owners close by coprime square multiplication; distinct owners close by a cleaned Pell relation, second obstructions, and cubic repair of reflected simultaneous zeros.  Every such gap is below `10^120`; surviving gaps have at least three distinct prime divisors. |
| T1-2O | Aggregate cleaned owners | Group arbitrary prime support by cleaned residual owner and apply the two-bucket obstruction calculus. | complete two-owner branch; Lean-banked and hostile-audited | The exact all-prime loss table is `G_k=(108,1620,136080,1224720,242494560,18914575680)`. Finite factorization, coprime bucket assembly, square divisibility, and `g<=G_k` are kernel-banked.  Global concentration chooses one assignment; at target size its nonzero cleaned owner range has no two-index cover.  Three explicit distinct live prime/owner witnesses are now extracted from that same assignment, but further owners are not discarded. |
| T1-GSQ | Global residual square lift | Recenter every lower factor as `X_i=3(n+i)-d` and retain coefficient cancellation in the exact transformed product equation. | proved and Lean-banked | `d^2 | product_i X_i` for every exact equation, with no prime-base or localization exception. Residual-progression concentration and two-bucket consequences are active. |
| T1-MOM | Global moment cancellation | Use `2^2=4` at the two signed residual centers to cancel the quadratic coefficient. | proved and Lean-banked | `d^3` divides two explicit constant-plus-linear coefficient combinations.  An exact solution shows neither raw product need be cube-divisible; the proper next use is the three-or-more-bucket regime. |
| T1-3B | Three cleaned residual buckets | Eliminate the two opposite near-square residuals from the second through fourth local lifts, then use the verified short window. | exact local restrictions through fourth order banked; short-CRT node open | Cyclically, `P|O_i`, `P^2|-3O_i+180E_i g^2(i-j)(i-l)d`, and `P^3|3bcF_i+P^2J_i`.  All 1,035 zero slopes are pairwise distinct, but an unbounded Hensel/CRT pseudo-family lifts the package through fourth order while failing the equation/window.  The next lemma must use the short window quantitatively. |
| T1-3B-Z | Zero-obstruction LCM packing | If one `O_s` vanishes, pack all three cleaned components into one coefficient product and apply the target loss bound. | repaired six-row wrapper Lean-banked and hostile-audited | The repaired ordinary-`decide` certificate checks all six target rows and gives exact coefficient bounds `<10^30,<10^18`; coprime packing yields `d|A*B*K*g^4`, excluding every designated zero at `d>=10^120`. The historical noncompiling SHA remains an immutable FAIL record. The all-nonzero short-CRT/window core remains. |
| T1-3B-Q | Fourth-to-third quotient and lattice packing | Cancel the cubic lift to a fixed-coefficient quotient congruence, eliminate common variables across three owners, and pack two zero quotients. | Generic Lean package banked and hostile-audited; zero-quotient ledger superseded equation-facing | The historical scan enumerates 2,603 noncentral two-zero placements; `10^131` closes all numerically. More strongly, the exact equation and ratio window prove all three obstructions, hence all named third quotients, nonzero from `d>=10^120`. No one-zero, multi-zero, center-zero, or 282-case branch remains live. |
| T1-3B-SIGN | Short-window lattice signs and component packing | Classify exact quotient-sign cells and turn one-sided lattice mass into two component-square bounds. | Generic Lean consequences banked; old zero-boundary census superseded | Exact-ratio domination leaves all 1,035 triples all-three-nonzero and sign-mixed. The tail-1000 determinant closes 27 center/reflected triples; 1,008 nonreflected exactly-three geometries remain. Coefficient signs alone do not bound two weighted terms. |
| T1-MO | Complete finite-owner obstruction composition | Compose every opposite residual while retaining the original loss, then use the lower residual product to exclude zero obstructions. | 10 generic Lean theorems banked and hostile-audited | For every complete owner family of cardinality `4..15`, `P_s|O_s`, `P_s^2|F_s`, and target-size `O_s!=0`. The 42,274-subset exact scan and a 130-digit CRT falsifier show the direct nonzero-size and congruence-only routes remain open. |
| T1-AO | Full-grid owner assembly | Put every retained cleaned prime power into its certified row bucket, preserve unit empty buckets and the original loss, and instantiate the finite-family obstruction package. | strengthened; Lean-banked and hostile-audited | Every target equation constructs `AllOwnerAssemblyThirdNonzeroCertificate`: exact full product and residual progression, bounded loss, all second/third divisibilities, and every composed second and third obstruction nonzero. All 2,576 four-owner circuits are sign-mixed. The unique product-square Vandermonde resultant retains the common cofactor product; on the full grid it is exactly the degree-three truncation of the block equation, and its induced fourth-power divisibility is termwise tautological from `d=gM`. The joint nonzero/short-window lemma remains open. |
| T1-5L | Fifth local lift, quotient-size layer, and reflected determinant packing | Retain the quartic local cofactor term, normalize the next quotient, bound it from the exact short window, and in the center/reflected specialization combine endpoint third obstructions with the center lift. | exact generic restrictions, direct configuration bridge, and ordinary-kernel 3,024-position ledger banked; all 27 supplied center/reflected pairs closed at `10^1000`; simultaneous nonzero branch open; generic resultant refuted | Lean proves `R5(d)=27K4+dR1+d^2R2`; with `d=PM` the square congruence is exactly `P|27w+MR1g^4`.  It also proves `|w|<Wg^4M`, `|N|<Vg^4M`, `N!=0 -> P^2<Vg^4d`, and `d^4PN=g^4J(X,d)`.  An ordinary-kernel certificate covers all 3,024 nonreflected cyclic positions, with a generic membership theorem proving exact coverage of the valid six-row domain.  The direct selected-three bridge constructs the quotient identities, `P|N`, and `w,N!=0` from an actual factorization, residual squares, and equation.  The all-owner corollary must absorb omitted buckets into an enlarged unbounded loss.  The simultaneous mixed-sign nonzero exclusion remains open, and the three square bounds are exponent-wrong when multiplied.  An independent exact fifth-gcd audit obtains `sum_s |mu_s| P_s^2 <= H_k g^4 d` in exactly 442 of the 1,008 geometries, but the bound is exponent-neutral and is not Lean-banked; all tested constant-weight closing resultants have zero kernel even modulo the exact block equation.  Separately, supplied center/reflected factorizations close below `10^200`; 121- and 1,004-digit Hensel fixtures refute congruence-only closure while failing the equation/window. |
| T1-PUI | Puiseux denominator | Expand the algebraic branch solving `P_k(X)=4P_k(Y)` beyond the leading root and prove an explicit denominator/integrality trap. | blocked | After `L` terms the cleared algebraic norm grows like `Y^(2L(k-1)-2)`; ordinary norm-smallness cannot force zero without new denominator cancellation. |
| T1-UNIT | Unit equation | Use conjugate information in `Q(4^(1/k))` to bound the structured norm identity. | active | Generic Baker-Feldman bounds are disallowed unless below `10^120`. |
| T1-SCALE | Primitive CF scale | For `X=gu`, `Y=gv`, use the exact polynomial in `z=g^2`, its coefficient filters, and the discriminant square condition. | partly proved; low-order closure refuted | An explicit unbounded k=5 family passes gcd, parity, sign, support, ratio, and the first two z-adic filters while `Q(z)>0`; the discriminant square lift is the original genus-6 curve in disguise. The floor pin is the surviving proper restriction. |
| T1-G2 | Direct k=5 genus-two quotient | Determine all rational points on `y^2=9x^6+64x^5-200x^3+64x+144` and audit the inverse square/integrality condition. | full Mordell-Weil group, eight-cover decomposition, and fourteen-packet custom sieve certified; rational-point completeness open | Lean banks the reduction, inverse relation, and exceptional denominator point. Exact Magma gives `Sel^(2)(J/Q)=(Z/2Z)^5`, trivial torsion, and `J(Q)=Z^5` with `proved=true`; five supplied point differences form a unimodular basis. The two infinity vectors are exact in the same basis. `TwoCoverDescent` gives eight locally soluble classes, all populated by known points. Fourteen exact packets through `p=59` give combined HNF index `42343330413030424784735169272832000000`, `516168751624777728` surviving cosets, and density `5383303927/441613360315210220469081750000`; all 36 known points occupy distinct classes. The height matrix has certified lower eigenvalue `43/200`. The missing sieve node is an explicit upper comparison from curve projective height to `canonical_height([P-P0])`; alternatively exhaust the eight elliptic covers. |
| T1-JET | Punctured-grid jet compression | For any proper owner support, dominate it by the full grid minus one point; construct integral sections vanishing to multiplicity `mu` there and compare their coefficient norm with the `10^1000` height budget. | k=5 fully ordinary-kernel banked, hostile-audited, manifest-tracked, and attested; k=7 audit in progress; complete support open | In the coordinate basis `B_k(X)^q X^aY^b`, all but one or two top layers are full grid-interpolation rectangles. Tensor Lagrange coordinates make the leading jet blocks diagonal, reducing the apparent k=15 `~61,000 x 61,000` system to a `448 x 540` Schur complement after exact forward elimination. The verifier saturates the integer kernel before LLL. For all 25 k=5 punctures the worst standard coefficient l1 norm has 70 digits and the exact corrected budget retains 882 decimal orders; all 175 local quotient multipliers are one. Exact curve-section resultants certify that the selected sections have precisely the punctured grid as their common on-curve zero locus. `Erdos686K5AllPunctures.lean` assembles 24 two-section endpoints and the exceptional central five-section endpoint through 1,272 local-row modules, 477 dense elimination leaves, 53 thin assemblies, and 25 Bézout kernels. The theorem `no_k5_tail_solution_of_proper_support` proves that every `k=5`, `d>=10^1000` solution has complete canonical support. Every generated puncture source is free of `native_decide`; the hostile verifier, full build, 807-theorem manifest audit, 1,286-declaration axiom gate, and 807 attestations pass. The saturated k=7 puncture `(1,1)` has 215 digits, multiplier one for all 16 sections, a 570-order margin, and an exact two-resultant base-locus gcd with no residual factor. These are proper-support results only; no complete-support contradiction is claimed. |
| T1-NJ | Normalized cell-local jets at arbitrary order | Expand the exact owner-cell quotient in one owner-adic completion and seek a nonseparable rectangle correction at higher order. | exact multiplicative coboundary identity Lean-banked; route closed | After cancelling a shared owner, `C*Q_i(Y)=4R*Q_j(X)`, equivalently `C/(4R)=Q_j(X)/Q_i(Y)`. Any formal logarithmic correction is therefore a lower row term minus an upper column term at every order. This kills normalized cell-local higher-jet rectangles and minors, but does not apply to the global punctured-grid interpolation route `T1-JET`. |

## Target 2 routes

| ID | Family | Exact proposed leverage | Verdict | Evidence or gap |
|---|---|---|---|---|
| T2-MATCH | Prime-power matching | Match maximum-valuation owners across the exact lower and upper blocks, then compress their difference chunks. | proved proper compression; Lean-banked | `B(k,n)` divides `(k-1)!` times the centered-difference lcm; the row-only fallback costs two factorials. Both deep fixtures pass, but lcm mass alone has `2k-1` hosts and does not close large `d`. |
| T2-CLEAN | Canonical all-k owner matrix | Allocate each prime to one maximizing lower/upper cell so the omitted mass is bounded by one `(k-1)!`, after removing the external factor four from one upper term. | proved, Lean-banked, repository-audited, and attested | `exists_canonicalOwnerSystem` constructs the full matrix for every `k>=4`, `k<=d` solution. It proves `G|(k-1)!`, equal lower/upper residual products, exact row and column factorizations with `c_t=4`, pairwise-coprime distinct cells, diagonal support `A_ji|d+i-j`, and `G*product A_ji=B(k,n)`. The `p=2` allocation uses `S-(F-2)=(S+2)-F`; no maximum reselection is required. Every `p>k` has one unique full-exponent owner cell. The cleaned support need not preserve raw connectedness or minimum degree. |
| T2-QSTRIP | Interval-lcm compression and quadratic strip | Bound the lcm of the centered interval using exact interval multiplicities and compare it with the equation-facing ratio lower bound. | uniform all-parity strip proved and Lean-banked | For `Lambda(m)=lcm(1,...,m)`, Lean proves `Lambda(m)<=4^m` and the exact interval theorem `m!*L | B*Lambda(m)`.  Together with the banked one-factorial compression this excludes every `k>=16,d>=k` equation satisfying `18*d<=k^2`, with no parity hypothesis.  Every live large-row residual therefore records `k^2<18*d`.  The general interval exponent is sharp up to constants and does not bridge the even Runge tail. |
| T2-MD | Supplied matched-owner residual dichotomy | For an arbitrary matched modulus `q`, use the sharp cofactor window, then split on the first signed residual and retain the normalized quadratic coefficient in the zero branch. | exact conditional theorem Lean-banked and hostile-audited; owner supply open | Always `1218443*k*b<3707904*a` and `q|D`. If `D!=0`, `1218443*k*d<3707904*a^2(C_j+2C_i)`. If `D=0`, gcd normalization gives `a=Bw`, `a+b=Aw`, `B<A<2B`, a nonzero fixed `c2`, `wq|c2`, and `d≤(A-B)|c2|+k-1`. Exact scans cover the odd-center ratio-four boundary, `q=k`, row 22, row 984, and `d=1`. No banked theorem supplies a contradiction-producing matched owner; minimum-degree-two owner cycles survive. |
| T2-VAL | Sliding-window valuations | Compare the unique landing rows of every prime power `p^e > k` with the exponent budget from the exact equation. | active | Gross log-mass counting alone is known insufficient. |
| T2-TRANS | Row-transition rigidity | Use changes between consecutive row windows to force an unsupported prime power at an unbounded row. | active | Fixed-prefix variants are refuted. |
| T2-XFER | Transfer to centered equation | Combine double smoothness with the centered `P_k` identity to obtain structure absent from arbitrary smooth blocks. | active | Smoothness by itself is not a universal obstruction. |
| T2-REFL | Reflection gcd and owner correlation | With `S=2n+d+k+1`, combine reflection, lower/upper concentration, and matching. | proved proper restrictions; Lean-banked and hostile-audited | Besides `S | reflectionCoeff(k)*reflectionProduct(k,d)`, every residual prime power divides `|i+j-(k+1)|`; non-reflected pairs land in `lcm(1,...,k-1)`, while `j=k+1-i` remains. Also `S | reflectionCoeff(k)*(k-1)!*reflectionDiffLcm(k,d)`. The factorial-lcm and product bounds are incomparable. |
| T2-442 | Greatest-prime-factor wedge | Apply the published Nair-Shorey `P(x...(x+k-1)) > 4.42k` theorem after proving every lower term composite. | paper-rigorous; Lean-checked downstream of explicit interface | Closes the unbounded range `k >= 16`, `k <= d`, `50*(d+k-1) <= 221*k`; the Nair-Shorey theorem itself is not formalized here. |
| T2-EVEN | Even-row Runge polynomial part | Use the two rational infinity branches available because the multiplier four is a square. | universal tail plus six full rows Lean-banked; direct quadratic-tail and tested Laurent/Padé bridges exactly refuted | Every even row `k=2r>=4` has a constructed exact coefficient certificate and explicit threshold `M_r`; no solution exists for `d>=max(2r,M_r)`. Separate square-root traps and ordinary-kernel finite-field covers close the complete rows `k=16,18,20,24,28,32`.  The first correction `q_(r-2)=-r(4r^2-1)/6` forces the canonical threshold above the quadratic cutoff for every row.  At the live row `k=34`, the complement begins at `d=65`; an exact rational root bracket and both equation power windows force `3091<=v<=3155`, while the optimistic fixed-divisor leading comparison needs `v>=225186598141623936273745117`.  The exact Laurent/Padé audit for `r=11,13,15,17` and orders one through four retains deficit degree `r-1` and closes none of the 108 boundary center pairs.  These are route falsifiers, not equation witnesses; a viable bridge needs a genuinely different cancellation or gcd/owner-correlation gain. |
| T2-K22-SIEVE | Row-22 shifted Runge trap plus bounded local masks | Compress the first live even row to a bounded integer parameter, then cover it by exact prime-field masks. | fully Lean-banked and hostile-audited; row closed | Lean closes `22<=d<=249`: the quadratic strip handles `22<=d<=26`, and 28 ordinary-kernel shards handle all 16,859 exact ratio-window pairs for `27<=d<=249`.  For `d>=250`, Lean reduces every solution to `S(w)=4S(v)`, `T(w)-2*T(v)=-33t`, with odd `1<=t<=3795146531`.  Parity and mod 23 leave exactly 330,012,742 candidates.  A regenerated certificate covers them with exact masks through `p=953`, split across 24 packed shards whose small map modules prove local subtree support before the union.  The full ordinary-kernel build passes, an independent hostile verifier recomputes the exact cover and digests, and the terminal theorem `no_gap_solution_four_even_twentytwo` exposes only `propext`, `Classical.choice`, and `Quot.sound`.  The earlier temporary-stub artifact remains rejected; it is not in the active dependency cone. |
| T2-CENTER | Even reflection-center gcd and cofactor quotient | Put the gap-supported part of a large-base center cofactor into the fixed odd double factorial, retaining the exact gap-coprime quotient. | proper unconditional component restrictions Lean-banked; quotient supply/bound open; aggregate-only closure refuted | For `H=2n+d+k+1=a*p^e`, prime `p>=k`, and `b=a/gcd(a,d)`, Lean proves `gcd(a,d)|(k-1)!!`, `2p^e<5(k-1)!!b`, `38d<5((k-1)!!)^2b^2`, and `1218443kd<2317440((k-1)!!)^2b^2`.  The case `a|d` has `b=1` and gives fixed-row exclusions.  An exact live-strip `k=22` fixture satisfies the ratio/strip, smoothness, reflection, absorption, square-lift, and small-defect aggregate package while all 22 row divisibilities fail.  Thus the package alone cannot close; no current theorem bounds `b`, and a new cross-row capacity theorem retaining the individual row divisibilities is required. |
| T2-SPP | Prime-power lower terms | Compare the lower owner valuation with upper concentration in the interval between consecutive `p^A` multiples. | proper unbounded restrictions; Lean-banked and hostile-audited | Both lower-block endpoints are excluded for every prime. At an interior index the exact criterion is `v_p((k-1)!) <= v_p(4)+v_p((i-1)!(k-i)!)`; every interior prime power with base `p>k` follows. More generally a single large-base owner `a*p^A` is excluded whenever `a(d+k-1)<n+i`; the sharp centered window gives this for `3707904a<=1218443k`. Exact `p=2,3` fixtures refute the unrestricted interior claim. |
| T2-GAPCOMP | Gap-component and grouped-owner square dominance | Combine the local quadratic lift with the exact `18(n+1)<13kd` upper window. | proper infinite subclasses; Lean-banked and hostile-audited | Every `p^e|d`, `p>=k`, satisfies `6p^(2e)<(13k-6)d+18(k-1)`, as does every complete cleaned owner bucket square. Whole prime-power gaps with `e>=2` are closed. A whole two-large-prime gap forces distinct owners; for odd `k>=17` the surviving branch constructs the uniform `A=3k+2` Pell and second-lift certificate, with at least one nonzero obstruction. The nonzero-obstruction Pell branch and mixed small-prime support remain open. |
| T2-HICOMP | High prime-power components at small bases | Track all translated `p`-free parts when the full component `p^e>=k`, treating `p=2,3` separately. | proved and Lean-banked | `no_four_solution_of_highPrimePower_component` dispatches to exact `p=2`, `p=3`, and `p>=5` theorems.  The valuation/unit trichotomy, the two-half-owner mod-9 exclusion at three, all three residual lifts, and the strict size contradiction compile with exactly `[propext, Classical.choice, Quot.sound]`.  `no_four_solution_primePowerGap` additionally closes every `d=p^(k+t)` with `k>=16`.  The exact verifier checks 98,172 components.  `FinalResidual686Hypothesis` records the strict reverse of all three canonical dominance thresholds.  Nair-Shorey remains external/paper-only. |
| T2-REFHARM | Reflected harmonic obstruction | Convert Sylvester--Schur prime supply into a unique negative p-adic valuation for `4N*sum(1/s)`, then derive that value from the two coefficient equations. | fully Lean-banked | A vendored complete Sylvester--Schur proof, a p-adic wrapper, and the generic `C_i,D_i` coefficient bridge prove that the two exact second obstructions at distinct owners cannot both vanish in any odd row `k>=5`. The surviving Pell branch therefore has a nonzero obstruction, but its uniform size consequence is not yet banked. |
| T2-LUCAS | Prime-power boundary binomial | Rewrite `B(k,x)=k!*C(x+k,k)` and apply Lucas at `k=p^a-1`. | proper residue restriction; Lean-banked and hostile-audited | For `p>=5`, an exact equation forces `p^a` to divide neither `n` nor `n+d`. The stronger exact Kummer-unit filter is reproduced but remains paper-level; hundreds of `p=5,a=1` classes survive, so no congruence-only closure is claimed. |
| T2-MASS | Consecutive small-part mass and owner graph | Strip primes above `k`, apply the consecutive-integer property, and study the bipartite rough-owner graph. | kernel arithmetic plus paper-level ELS classification; not a closure | Lean proves `k!` divides every stripped block product and an equation gives exact stripped ratio four. In the both-bounded ELS branch the rough-owner graph has at least `k+1` edges, at least `k+2` beyond `(2(k+1))^k`, and at a larger explicit threshold has one spanning component or two half-size components. A reflection-compatible four-cycle fixture survives every ingredient except the full lower ratio window, so no alternating determinant is claimed. |

## Stronger banked Target 2 facts

- `difference_block_below_n_of_four_solution`: `d+k-1 < n`.
- `smooth_blocks_of_four_gap_solution`: both length-`k` blocks are smooth up
  to `d+k-1`.
- `smooth_blocks_and_reflection_of_four_gap_solution`: the two blocks and
  `2*n+d+k+1` are all smooth up to `d+k-1`.
- `LargePrimeMatch`: every odd prime above `k` has unique support in each
  block, equal valuations, and prime-power divisibility of the exact gap.
- `row_smooth_of_four_gap_solution`: row `j` has the sharper cap `d+k-j`.
- `blockProduct_dvd_factorial_mul_centeredDiffLcm_four`: the exact equation
  puts the complete lower block into one centered lcm after one factorial
  allowance.
- `initialLcm_le_four_pow` and
  `factorial_mul_intervalLcm_dvd_ascFactorial_mul_initialLcm`: for every
  positive `m`-term interval, `Lambda(m)<=4^m` and `m!*L|B*Lambda(m)`.
- `no_four_solution_of_quadratic_strip`: for every `k>=16,d>=k`, the exact
  equation is impossible when `18*d<=k^2`, without a parity hypothesis.
- `exists_reflection_owner_offset_restriction_four`: every reflection-center
  prime power lands on an owner offset; the reflected pair is the surviving
  alternative.
- `reflection_lcm_compression_four`: the reflection center divides one
  coefficient, one factorial, and the lcm of the positive reflected
  differences.
- `k_mul_gap_lt_five_mul_n_of_four_solution`: `kd<5n` for `k>=16`.
- `three_k_mul_gap_lt_five_mul_n_of_four_solution`: the sharper uniform
  window `3kd<5n` for `k>=16`.
- `thirteen_k_mul_gap_lt_twenty_mul_n_of_four_solution`: centered pairing
  sharpens this further to `13kd<20n` for `k>=16`.
- `maximal_sharp_bracket_ratio_of_four_solution`: the strongest fixed-bracket
  certificate gives `1218443kd<1853952n` for `k>=16`.
- `even_reflectionCenter_gapCoprimeQuotient_sharp_gap_bound`: in an even row,
  a complete center component `H=a*p^e` with `p>=k` satisfies
  `1218443kd<2317440((k-1)!!)^2(a/gcd(a,d))^2`.

These are premises for new attacks, not solutions of `LargeKSmoothHypothesis`.

## Pipeline audit

The checkpoint is regenerated from `proofs.yaml` after the final k=18 shard
assembly. The emitter parses wrapped and axiom-free reports, rejects missing
theorem reports, and accepts any subset of
`[propext, Classical.choice, Quot.sound]`.

## Current exact gap

`ErdosProblems/Erdos686FinalResidual.lean` composes the new results into the
single quantified `FinalResidual686Hypothesis`. Its odd arm begins at
`10^1000` and carries the complete all-owner second/third-nonzero certificate.
Its large-row arm omits `k=16,18,20,24,28,32`, restricts every other even row below
its constructed threshold, includes `k^2<18*d` and `1218443kd<1853952n`, and excludes the exact
prime-power and small-cofactor owner families above.  It also includes the
large gap-component, complete grouped-owner, Lucas endpoint, uniform odd
two-prime Pell restrictions, and the all-prime high-component thresholds.
Thus any surviving exact component `p^e || d` with `k<=p^e` must satisfy
the strict reverse of the corresponding `p=2`, `p=3`, or `p>=5`
dominance inequality.
Lean proves that this
one statement implies both former interfaces and the full refutation, and
also proves the converse from
`OddThueTail1000Hypothesis ∧ LargeKSmoothHypothesis`.  Thus it is equivalent
packaging, not a weaker missing lemma.  The residual statement itself is open
and is not counted as a theorem.

## Audit rules

1. Expand every qualitative estimate to an explicit quantified bound.
2. Give an exact witness for every `refuted` verdict.
3. Do not mark a target-equivalent missing lemma as progress.
4. Reproduce every computational claim from checked-in source using exact arithmetic.
5. Admit a result to Lean only after all relevant mandatory fixtures pass.
