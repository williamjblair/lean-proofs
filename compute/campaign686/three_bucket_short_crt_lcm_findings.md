# Erdős 686 three-bucket short-CRT LCM restriction

Status after hostile audit: **generic zero-obstruction LCM node proved;
row-wise kernel composition missing; advertised `abc` novelty withdrawn.**
Exact arithmetic composes the generic node with all six coefficient tables
and excludes a vanishing composed second obstruction at `d >= 10^120`, but
the source module does not export the required six-row wrapper.  The listed
`abc` values are exact thresholds of the chosen majorant, yet every exact
equation tuple already satisfies the vastly stronger banked inequality
`abc > 125*g^2*d`.  The remaining short-CRT lemma is not proved.

The generic LCM argument is kernel-checked in
`ErdosProblems/Erdos686ThreeBucketShortCrtLcm.lean`.  The finite coefficient
certificate is independently reconstructed by
`three_bucket_short_crt_lcm_verify.py`; it imports none of the producer
arithmetic.

## Frozen inputs

For distinct owners `i,j,l`, write their pairwise-coprime components as
`P,Q,R`, their positive cofactors as `a,b,c`, and

```text
d = gPQR,                 t = abc,
X_i = aP^2,  X_j = bQ^2,  X_l = cR^2.
```

For an owner `s`, let `u,v` be the other two owners, put
`delta_s=(s-u)(s-v)`, and let `C_s,D_s,E_s` be its first three signed local
Taylor coefficients.  The audited producer proves, cyclically,

```text
H_s   | O_s := 3(C_s t - 12 D_s g^2 delta_s),
H_s^2 | F_s := -3 O_s + 180 E_s g^2 delta_s d.          (1)
```

The present argument treats (1), the exact row budgets, pairwise
coprimality, and positivity as inputs.  It does not rederive the second or
third local identities.

## Dependency tree and per-node verdict

```text
assume O_R = 0
|
+- Z1 positivity
|  `- t/g^2 = 12 D_R delta_R / C_R must be positive
|
+- Z2 other two second lifts
|  +- P | O_P and D_P' O_P = N_P g^2  ->  P | |N_P| g^2
|  `- Q | O_Q and D_Q' O_Q = N_Q g^2  ->  Q | |N_Q| g^2
|
+- Z3 zero owner's third lift
|  `- R^2 | |180 E_R delta_R| g^2 d
|     `- d=gPQR; cancel R; gcd(R,PQ)=1
|        `- R | |180 E_R delta_R| g^3
|
+- Z4 pairwise-coprime LCM packing
|  `- L=lcm(|N_P|,|N_Q|,|180 E_R delta_R|)
|     `- PQR | L g^3, hence d | L g^4
|
+- Z5 exact finite certificate
|  `- every positive zero slope in all 1,035 triples; max L by row
|     `- max L G_k^4 < 10^120 in all six rows
|
`- Z6 nonzero branch
   `- H_s <= |O_s| for all three owners
      `- d <= G_k product_s(3|C_s|t+36|D_s|G_k^2|delta_s|)
         `- exact monotone threshold search gives the lower bound on t=abc
```

- **Z1: PASS.**  There are 3,105 owner occurrences in the 1,035 unordered
  triples.  Exactly 1,427 have positive zero slope and enter the LCM scan;
  the other 1,678 cannot equal positive `t/g^2`.
- **Z2: PASS.**  If
  `3 C_P(slope_R-slope_P)=N_P/D_P` in lowest terms, then the exact identity
  is `D_P O_P=N_P g^2`.  No division modulo `P` occurs.
- **Z3: PASS.**  The Lean theorem cancels one positive `R` from
  `R^2 | R(Kg^3PQ)` and removes `PQ` only with the stated pairwise
  coprimality.  It never assumes `gcd(R,g)=1`.
- **Z4: PASS.**  Three pairwise-coprime divisors of one integer have product
  dividing that integer.  This is the leverage missed by multiplying three
  unrelated magnitude bounds: the loss contributes `g^3`, not `g^7`.
- **Z5: PASS.**  Every center and reflected triple is included.  Every
  third coefficient `180 E_R delta_R` in a positive-zero case is nonzero.
- **Z6: PASS.**  Once Z5 excludes zero, positivity of each component and
  `H_s|O_s` gives `H_s<=|O_s|`.  The displayed majorant uses only
  `g<=G_k` and exact absolute values.

## Exact zero-branch certificate

For each row, `L_k` is the maximum finite LCM over every positive zero-owner
case.  The last column is the exact uniform upper bound `L_k G_k^4` for `d`.

| `k` | positive zero cases | `L_k` | `L_k G_k^4` |
|---:|---:|---:|---:|
| 5 | 12 | 5,443,200 | 740,541,350,707,200 |
| 7 | 45 | 59,999,849,280 | 413,247,483,519,713,740,800,000 |
| 9 | 112 | 736,171,343,178,485,760 | 252,438,801,810,021,029,402,684,623,002,009,600,000 |
| 11 | 225 | 34,885,840,090,609,728,000 | 78,486,764,429,761,645,052,953,426,899,755,335,680,000,000 |
| 13 | 396 | 820,995,472,546,561,208,033,280 | 2,838,891,296,780,015,046,791,841,911,350,004,426,030,003,822,316,748,800,000 |
| 15 | 637 | 138,245,988,147,349,868,236,401,258,147,840 | 17,694,526,643,294,042,605,461,686,913,458,493,647,472,960,653,351,115,605,266,135,410,278,400,000 |

The global maximum is the `k=15`, owners `(1,14,15)`, zero owner `1` case:

```text
slope_1 = 1171733/165,
(|N_14|,|N_15|) = (126308477468160, 2000133607772160),
|180 E_1 delta_1| = 12847056696714240,
L = 138245988147349868236401258147840.
```

Lean checks directly that

```text
138245988147349868236401258147840 * 18914575680^4 < 10^120.
```

Together with the externally checked row certificate, this excludes a
vanishing composed second obstruction in a target-size three-bucket tuple.
It is not attestation-ready until a Lean wrapper discharges the row-specific
coefficient hypotheses.

## Exact majorant thresholds for `abc` (equation-level redundant)

For a fixed owner triple `I`, define the monotone integer majorant

```text
U_(k,I)(t) = G_k * product_(s in I)
  (3|C_s|t + 36|D_s|G_k^2|delta_s|).                  (2)
```

All second obstructions are nonzero above the cutoff, so `d<=U_(k,I)(t)`.
For each row the verifier finds the least integer `T_k` for which
`max_I U_(k,I)(T_k) >= 10^120`; it separately verifies
`max_I U_(k,I)(T_k-1) < 10^120`.  Thus this chosen majorant implies:

| `k` | exact necessary lower bound `abc >= T_k` |
|---:|---:|
| 5 | 46,296,296,296,296,296,296,296,296,296,294,624,457 |
| 7 | 716,294,573,088,391,804,384,271,040,815,308,651 |
| 9 | 3,214,574,169,492,218,063,895,298,388,397,719 |
| 11 | 18,497,091,393,047,867,380,101,052,189,640 |
| 13 | 25,548,663,987,620,205,641,977,050,294 |
| 15 | 33,652,495,592,619,590,630,929,591 |

The maximizing triple at each threshold is `(1,2,k)`.  These values are
correct, but they add no equation-level restriction.  The banked theorem
`twice_gap_lt_n_of_four_solution` gives each selected residual `X_s>5d`, so

```text
abc*(PQR)^2 = X_i*X_j*X_l > 125*d^3,
d=gPQR,
```

and hence `abc>125*g^2*d`.  At `d>=10^120` this exceeds every displayed
threshold by at least `2.7*10^84`.

## Single remaining quantified gap

For each row

```text
(k,A_k,G_k,T_k) =
  (5,14,108,46296296296296296296296296296294624457),
  (7,17,1620,716294573088391804384271040815308651),
  (9,23,136080,3214574169492218063895298388397719),
  (11,26,1224720,18497091393047867380101052189640),
  (13,29,242494560,25548663987620205641977050294),
  (15,35,18914575680,33652495592619590630929591),
```

prove that there are no positive integers `d,g,P,Q,R,a,b,c` and distinct
`i,j,l in [1,k]` satisfying

```text
d >= 10^120,       d=gPQR,       1<=g<=G_k,
P,Q,R>1 and pairwise coprime,    abc>=T_k,

aP^2-bQ^2=3(i-j),  aP^2-cR^2=3(i-l),
0<aP^2<A_k d,       0<bQ^2<A_k d,       0<cR^2<A_k d,

O_i != 0, O_j != 0, O_l != 0,
P|O_i, Q|O_j, R|O_l,
P^2|F_i, Q^2|F_j, R^2|F_l,
```

with `O_s,F_s` defined in (1).  The `abc>=T_k` clause is redundant in the
equation-specific slice.  The only new mathematical restriction is
nonvanishing of the three composed second obstructions, and even that still
needs the missing six-row Lean wrapper.  This quantified lemma is unproved;
returning it as a full closure would be circular.

## Boundary audit

- The `d=1` telescopes at `k=9,15` are below the cutoff and have no three
  nontrivial cleaned components.
- Centers and reflected pairs are retained in all 1,035 triples.  A center
  has zero second slope and therefore cannot be the vanishing owner when
  `abc>0`; it is still present as either of the other two owners.
- No prime is canceled from `g`.  In particular, the proof remains valid
  when the cleaned components share small-prime bases with the loss factor.
- Pairwise coprimality is used only among `P,Q,R`, exactly as supplied by
  bucket grouping.
- The audited below-threshold fixture has `d=6790` and lies outside both the
  cutoff and the new `k=5` cofactor-product bound.  The 121-digit CRT
  pseudo-witness still fails the short window.  Neither is mislabeled as an
  equation solution.

## Reproduction

```bash
lake env lean ErdosProblems/Erdos686ThreeBucketShortCrtLcm.lean
python3 -m pytest \
  compute/campaign686/test_three_bucket_short_crt_lcm_verify.py -q
python3 compute/campaign686/three_bucket_short_crt_lcm_verify.py --pretty
```
