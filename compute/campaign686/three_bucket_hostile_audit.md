# Hostile audit: Erdős 686 three-bucket restriction

Verdict: **PASS, with the claim boundary enforced.**  The four Lean theorems,
the 1,035-triple coefficient scan, the 5,216 signed elimination fixtures, and
the 121-digit CRT pseudo-witness all reproduce independently.  These artifacts
prove exact second- and third-order restrictions and falsify a
congruence-only closure.  They do **not** close the three-bucket tail or Erdős
686.

## Frozen producer inputs

```text
baea042c70c412a0fad120239c07f707e390acea1416aaad8024985c47f85aea  ErdosProblems/Erdos686ThreeBucketRestriction.lean
33b50990b59a8faea3b0fc253e7335365361bf6c0e3c1dc41a83cc93cbd257bd  compute/campaign686/three_bucket_attack.py
f4a54e9010e501cf955f23af295f1bc17c5219464c8db49738f78bf67175e5ee  compute/campaign686/test_three_bucket_attack.py
f415ca0e948abcc2742a70cd862b182ceb3f0def3239545c9dfce7e3081bd339  compute/campaign686/three_bucket_findings.md
```

Independent audit artifacts at the time of this report:

```text
ce709f0a80949d6807a310e72fcd66b64142ca320d21be9566d107070d6019bd  ErdosProblems/Erdos686ThreeBucketRestrictionAudit.lean
950aa2b0007e41a445fc7ce8d5812c94efce3fa8c76696794d536ac064034899  compute/campaign686/three_bucket_hostile_verify.py
33466af3736bc2e7029a85b98a1a595a15cd04e2cff6db35919564655b886a8d  compute/campaign686/test_three_bucket_hostile_verify.py
```

The hostile verifier imports nothing from `three_bucket_attack.py`.

## Dependency tree and per-node verdict

```text
three-bucket setup
|
+- N1 exact residual differences
|  +- a P^2 - b Q^2 = 3(i-j)
|  `- a P^2 - c R^2 = 3(i-l)
|
+- N2 second local input at P
|  `- P | 3 C_i a - 4 D_i (g Q R)^2
|     `- N3 eliminate both opposite squares
|        `- P | 3[C_i abc - 12 D_i g^2(i-j)(i-l)]
|
+- N4 third local input at P^2
|  `- P^2 | -3[3 C_i a - 4 D_i(g Q R)^2]
|             + 20 E_i P(g Q R)^3
|     `- N5 use the same square difference identity
|        `- P^2 | -3 O_i + 180 E_i g^2(i-j)(i-l)d
|
+- N6 finite target-row degeneracy scan
|  `- 1,035 unordered triples, three distinct exact rational slopes each
|
+- N7 global cubic moments localized at one owner
|  `- both reduce, up to units, to the same second-local residue
|
`- N8 CRT route falsifier
   `- square, second, third, global-square, and both global-moment
      congruences hold at an unbounded family of gaps; equation and short
      window are not consequences of that package
```

- **N1: PASS.**  Signed equalities are hypotheses, not inferred by natural
  subtraction.
- **N2: PASS as an explicit input.**  The module does not claim to reprove the
  previously banked local lift.
- **N3: PASS.**  Lean first proves
  `P^2 | (bQ^2)(cR^2)-9(i-j)(i-l)` and then the stated `P`-divisibility.  The
  independent signed grid reproduces the identity without primality,
  positivity, or coprimality assumptions.
- **N4: PASS as an explicit input.**
- **N5: PASS.**  The exact `P^2` composition and every sign reproduce.
- **N6: PASS.**  Every center and reflected triple is included.  Pairwise
  slope distinctness only proves that at most one obstruction vanishes; it is
  not treated as a tail closure.
- **N7: PASS.**  The moment combinations add no independent first-order
  obstruction at an owner; the exact congruences are given below.
- **N8: PASS.**  The construction is a pseudo-witness to the congruence
  package, explicitly not a solution of the block equation.

## Kernel and forbidden-construct audit

The following commands succeeded:

```bash
lake env lean ErdosProblems/Erdos686ThreeBucketRestriction.lean
lake env lean ErdosProblems/Erdos686ThreeBucketRestrictionAudit.lean
```

Every public theorem has exactly the allowed kernel dependency set:

```text
three_bucket_second_obstruction_dvd:
  [propext, Classical.choice, Quot.sound]
three_bucket_third_obstruction_dvd_sq:
  [propext, Classical.choice, Quot.sound]
three_bucket_slope_determinant_eq_zero_of_two_zeros:
  [propext, Classical.choice, Quot.sound]
three_bucket_third_mod_owner_reduces_to_second:
  [propext, Classical.choice, Quot.sound]
```

The producer Lean file contains zero occurrences of `sorry`, `admit`,
`axiom`, `native_decide`, `of_decide`, `unsafe`, `implemented_by`, `extern`,
or `noncomputable`.  Its one private lemma is used only to establish the
displayed square-difference divisibility; it introduces no private theorem
assumption.  Linter warnings concern redundant tactic sequencing only.

## Independent exact-arithmetic reproduction

The independent verifier and both test files pass:

```bash
python3 compute/campaign686/three_bucket_hostile_verify.py --pretty
python3 -m pytest \
  compute/campaign686/test_three_bucket_hostile_verify.py \
  compute/campaign686/test_three_bucket_attack.py -q
```

The exact slope scan returns:

| k | unordered triples | minimum pairwise separation |
|---:|---:|---:|
| 5 | 10 | 10 |
| 7 | 35 | 7 |
| 9 | 84 | 27/5 |
| 11 | 165 | 99/35 |
| 13 | 286 | 117/70 |
| 15 | 455 | 15/14 |

The total is `1,035` unordered triples (`6,210` ordered triples).  All three
slopes are pairwise distinct in every triple.  The scan includes 251 triples
containing a center and 251 containing a reflected pair.

An independent implementation reproduces exactly `5,216` signed fixtures for
each of the intermediate square identity, the second elimination, and the
third elimination.  A separate boundary grid checks 336 fixtures with owner
component 2 or 3 and nonunit `g`; no small prime is canceled.

The named target-row `d=1` telescopes also reproduce exactly:

```text
(k,n,d)=(9,2,1),  blockProduct(9,3)=4 blockProduct(9,2),
(k,n,d)=(15,4,1), blockProduct(15,5)=4 blockProduct(15,4).
```

They have no nontrivial three-component gap and are outside this setup.

## Global moment localization

Let `d=P m`, `n+i=P x`, and `3x-m=aP`.  Put

```text
S_i = 3 C_i a - 4 D_i m^2.
```

For the lower and upper global cubic moment combinations `M_-` and `M_+`,
direct expansion at owner `i` gives the quantified congruences

```text
3 (M_- / P^2)  = S_i                 (mod P),
   M_+ / P^2   = 3^(k-1) S_i         (mod P).
```

The displayed quotients are integers under the three preceding identities.
When `gcd(P,3)=1`, both multipliers are units, so `P^3 | M_-` and
`P^3 | M_+` reproduce `P | S_i`; neither is a second independent polynomial
in `abc`.  The hostile verifier reproduces both formulas on 2,880 signed
fixtures across all six target rows.  It also evaluates both global moments
directly on the target-size witness, using two independent computations of
the polynomial coefficient of degree one.

## The 121-digit CRT pseudo-witness

The independent iterative CRT reconstruction agrees with the producer on all
observable values.  It uses

```text
k=5, (i,j,l)=(1,2,4),
P=101^20, Q=103^20, R=107^20, g=1,
d=(101*103*107)^20
 = 8528006514942991411329818759017663024603296760011487105481658555774743359211568625230878556970868752918452276874633718401.
```

Stable exact commitments to the large integers are:

```text
d decimal SHA256: 027335da1fe1ac90a3e64722c6112adcc6a88359f5628432e13396b3303910b2
n: 484 digits, decimal SHA256 84077b773d3f67f9330d7500af6794a74073746d7f9b6ba888baccc9bdb531e4
lower moment / d^3 SHA256: a4a0340d742b14d83283aeed67ff21f5ba9e88b50a08c6114133b105ecc7a8cb
upper moment / d^3 SHA256: b6737271c9ce1c97d2a8f50aa223b5777c3818c423c56a0afbfb2716c64db280
```

Direct evaluation gives all of the following:

```text
selected residual differences: 0, 3, 9;
each selected residual is positive and divisible by P^2, Q^2, or R^2;
P|n+1, Q|n+2, R|n+4;
all second-local remainders: 0;
all third-local-square remainders: 0;
global residual-product remainder modulo d^2: 0;
lower global-moment remainder modulo d^3: 0;
upper global-moment remainder modulo d^3: 0.
```

The two deliberate failures also reproduce:

```text
block difference: negative, 2,419 digits,
  decimal SHA256 c7bc70b96e12cb007788994283299cc1ab1f87a2949ef64e51b15e8264e616ba;
selected-window excess over 14d: positive, 485 digits,
  decimal SHA256 ce7d7424a7a27b044db9d2c99b93bd69730894f68cfb946fc38b00680d6447cf.
```

Thus this is not a counterexample to Erdős 686.

The phrase “no standalone bounded resultant” is justified by a parameterized
family, not merely by the single `t=20` instance.  For every integer `t>=1`,
take `(P,Q,R)=(101^t,103^t,107^t)`.  For owners `(1,2,4)` the constants are
`C=(24,-6,-6)`.  Hence the parameter coefficients
`-9 C_i(d^2/P_i^2)` are units modulo `P_i^2`; the three local parameter lifts
exist by CRT.  Because `3` is a unit modulo `d`, exactly one of three
successive `d^2` parameter lifts makes `n` integral.  The local congruences
then imply the two global moment congruences as above.  The gaps
`d=(101*103*107)^t` are unbounded.  The verifier checks the first 24 members
(`7` through `146` gap digits) as a regression test.

## Exact short-CRT lemma and properness audit

The prose phrase “lie in one step-three progression” must be read as the two
signed equations below.  With that expansion, the exact remaining lemma is:

For a row

```text
k in {5,7,9,11,13,15},
A_k in {14,17,23,26,29,35},
G_k in {108,1620,136080,1224720,242494560,18914575680},
```

there is no tuple of positive integers
`d,g,P,Q,R,a,b,c` and distinct `i,j,l in [1,k]` satisfying all of:

```text
d >= 10^120,
1 <= g <= G_k,
P,Q,R > 1 and pairwise gcd(P,Q)=gcd(P,R)=gcd(Q,R)=1,
d = gPQR,

aP^2 - bQ^2 = 3(i-j),
aP^2 - cR^2 = 3(i-l),

0 < aP^2 < A_k d,
0 < bQ^2 < A_k d,
0 < cR^2 < A_k d,
```

and, cyclically for
`(s,H,u,M)=(i,P,a,gQR),(j,Q,b,gPR),(l,R,c,gPQ)`, all six divisibilities

```text
H   | S_s := 3 C_s u - 4 D_s M^2,
H^2 | T_s := -3 S_s + 20 E_s H M^3.
```

This is a proper, stronger sufficient lemma for the equation-specific
three-bucket slice: it omits the block equation, an integer `n`, integrality
compatibility, and the global moment hypotheses.  It is therefore not a
circular restatement of the target.  It is also not vacuous.  The hostile
verifier finds the exact below-threshold tuple

```text
k=5, (i,j,l)=(1,2,3), (P,Q,R)=(2,7,5), g=97,
d=6790, n=25177,
(aP^2,bQ^2,cR^2)=(68744,68747,68750),
(a,b,c)=(17186,1403,2750).
```

It satisfies the progression, the `14d` short window, pairwise coprimality,
and all six local divisibilities.  Its only displayed short-CRT hypothesis
failure is `d<10^120`; it also fails the block equation, with exact difference
`-7091705934067167000000`.  This confirms that the large-gap threshold is a
substantive hypothesis.

The short-CRT lemma remains **unproved**.  It may be used as the exact gap for
this approach, but not as a closure or as theorem-strength progress.  Even a
proof would close only the exactly-three-cleaned-component slice; support
four and higher still require a separate reduction or argument.
