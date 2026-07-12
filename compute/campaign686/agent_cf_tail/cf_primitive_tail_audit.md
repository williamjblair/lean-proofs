# Adversarial audit: CF primitive-scale finite tail (historical e166 checkpoint)

> **Historical checkpoint.**  This audit freezes the original `10^166`
> certificate.  The current canonical band reaches `10^1000` and has its own
> independent audit in `../agent_cf_tail_e1000/hostile_audit.md`; statements
> below about the tail beginning at `10^166` are not current-frontier claims.

Audited claim:

```text
For k in {5,7,9,11,13,15}, no exact solution exists with
10^120 <= d < 10^166.
```

Verdict: **proved by exact arithmetic and fully kernel-banked.**  Six
generated ordinary-`decide` Farey certificates feed the combined theorem
`no_odd_target_gap_solution_below_e166`.  The infinite tail at and above
`10^166` remains open.

## Dependency tree

```text
BRANCH A: kernel proof of the headline
existing exact block equation and row ratio bounds
├── centered row equation `KkCenteredEq X Y`
├── exact row bracket and lower threshold for Y
├── d<10^166 and the row base bound
│   └── Y <= QHI*10^166
├── generated row-k Stern-Brocot tree
│   ├── every leaf is an existing `kEqRefuted` certificate
│   └── ordinary kernel `decide +kernel`
│       └── `fareyCheck ... rowCert = true`
├── `fareyCheck_sound`
│   └── no row-k solution for 221<=d<10^166
└── six-way finite-set assembly
    └── `no_odd_target_gap_solution_below_e166`

BRANCH B: independent primitive-scale/CF reproduction
exact centered equation
├── lower algebraic side u^k < 4v^k
├── scale polynomial Q_k(g^2)=0
│   ├── constant divisibility g^2 | (r!)^2(4v-u)
│   └── signed alternating remainder
│       └── unique floor g^2=floor(e1*A_(k-2)/A_k)
├── target cutoff d>=10^120
│   └── primitive denominator v>=10^77
├── verified CF approximation |alpha-u/v|<=C/(g^2v^2)
│   └── self-contained three-class confinement
│       └── exact candidates for q_m<=v<q_(m+1), m=0,...,339
├── banked uniform ratio 109651v<100000u
│   └── d<10^166 implies v<11*10^166<q_340
└── exact full-residual evaluation on the unique square floor
    └── zero roots for all six rows
```

There is deliberately no dependency arrow from Branch B to Branch A.  The
kernel headline uses the direct Farey trees and `fareyCheck_sound`; the
primitive-scale scan is a mathematically independent reproduction and a
source of proper infinite-tail structure.

## Per-node verdicts

| Node | Verdict | Evidence |
|---|---|---|
| Branch A: centered row equation and ratio window | verified context | Exact statements and conversion lemmas are in the per-row Thue modules. |
| Branch A: six generated Farey trees | generated, then kernel-checked | `k5FareyCert166_check` through `k15FareyCert166_check`, each by ordinary `decide +kernel`. |
| Branch A: tree soundness | Lean-banked | Each row theorem calls `fareyCheck_sound` with its centered solution predicate, exact bracket, and existing `kEqRefuted_sound` leaves. |
| Branch A: row upper bounds | Lean-banked | From `d<10^166` and the row base window, the six bounds are respectively `Y<=4,5,7,8,9,11` times `10^166`. |
| Branch A: combined finite-band theorem | Lean-banked | The six row theorems assemble directly into `no_odd_target_gap_solution_below_e166`. |
| Branch B: centered equation and CF error | verified context | Exact statements are in the prompt and per-row Thue modules. |
| `u^k<4v^k` | proved | `P_k(T)/T^k` is strictly increasing for `T>r`; no approximation is used. |
| Scale polynomial | proved algebraically | Direct homogeneous substitution; coefficients are reproduced from `1^2,...,r^2`. |
| Constant divisibility | Lean-banked | `scale_constant_dvd`. |
| `d^2<3(r!)^2v^3` | Lean-banked | `gap_sq_lt_of_scale_constant`. |
| `v>=10^77` | Lean-banked | Two numerical theorems ending in `primitive_denominator_ge_ten_pow_77_of_scale_constant`. |
| Signed floor mechanism | Lean-banked generically | `floor_pin_of_signed_remainder`; the finite coefficient chains are checked exactly per candidate. |
| CF rows are exact | reproduced | Power differences, signs, determinants, recurrences, and semiconvergent straddles are recomputed from all six JSON files. |
| Three-class enumeration | proved context plus exact instantiation | Uses the self-contained confinement theorem, not a generic irrationality measure. Loop inequalities are identical to its three cases. |
| `v<11d` | Lean-banked | `primitive_denominator_lt_eleven_gap`; exact margin is `6161`. |
| `q_340>11*10^166` | reproduced | Checked separately for every artifact; the smallest is the `k=15` value printed in the findings. |
| Zero exact roots | reproduced | Full integer scale polynomial evaluated after all necessary filters; exact-root count is zero in every row. |
| Linear/cubic resultant loss | Lean-banked | `gcd_linear_cubic_dvd_sixty`. |
| Reverse Newton discrepancy | Lean-banked | `scale_quotient_gcd_bound`: `gcd(z,q)|60*e_r*e_(r-1)`. |

## Quantified bounds audit

There is no use of “essentially”, asymptotic uniformity, or a hidden
floating-point comparison.

1. The scale coefficient is bounded by
   `(r!)^2 <= (7!)^2 = 25,401,600`.
2. The denominator inequality is
   `d^2 < 76,204,800*v^3`.
3. The cutoff implication is exactly `d>=10^120 -> v>=10^77`.
4. The ratio conversion is exactly
   `109651v<100000u -> v<11(u-v)<=11d`, with margin `6161`.
5. The finite upper bound is strictly `d<10^166`, not `d<=10^166`.
6. Every candidate lies in one of 340 windows `m=0,...,339`; the upper
   denominator is the exact checked integer `q_340` for that row.

## Computational reproduction audit

Branch A is checked by Lean's ordinary kernel evaluator.  Its generator emits
six explicit Stern-Brocot trees; Lean evaluates each `fareyCheck` Boolean and
`fareyCheck_sound` supplies the proof that a true tree excludes every exact
solution in its bracket.  No result from the primitive candidate scan is
imported by `Erdos686CFTailBand.lean`.

Branch B's independent verifier uses only Python integers, `math.gcd`, and
`math.isqrt`.  It does not import `decimal`, `float`, NumPy, SymPy, Sage, or
an external CAS.  It validates the SHA-256 and mathematical content of every
source CF artifact before enumeration.  Expected stage counts are hard-coded
and tests fail on any drift.  The complete scale equation is evaluated,
rather than inferred from passing truncated filters.

Reproduction command:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q \
  compute/campaign686/agent_cf_tail/test_cf_primitive_tail_verify.py
PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_cf_tail/generate_e166_certificates.py
lake build ErdosProblems.Erdos686CFTailScale \
  ErdosProblems.Erdos686CFTailBandCert
lake env lean ErdosProblems/Erdos686CFTailBand.lean
```

Current result: `6 passed`; exact-root counts are all zero; all six generated
Boolean trees evaluate to true in the kernel; the combined headline compiles.

## Falsification-record audit

### `k=9`, `d=1`

Pass.  The verifier checks `(u,v,g,z)=(8,7,1,1)`, the exact centered
equation, zero scale residual, floor value one, and `d<k`.  Lean checks the
block identity using ordinary `decide`.

### `k=15`, `d=1`

Pass.  The verifier checks `(u,v,g,z)=(13,12,1,1)` and the same exact data.
It explicitly records that the strong large-denominator coefficient chain
does not apply to this fixture; the actual floor identity still holds.  This
prevents silently extending a tail inequality to the overlapping boundary.

### Generic irrationality measure

Not used.  Confinement uses the exact error already present in the verified
context and an elementary determinant/CF classification.  There is no
claimed exponent improvement for `4^(1/k)`.

### Baker/Feldman

Not used.

### Genus/discriminant restatement

Not used.  The only scale candidate is fixed by a signed integer remainder,
then evaluated directly.

### Reverse-divisibility overclaim

The valid statement is bounded overlap, not coprimality.  The exact `k=5`
low-filter counterfamily has `gcd(z,q)=12`, so the tempting strengthening
`gcd(z,q)=1` is explicitly falsified.  The counterfamily is not used as a
full equation witness.

### Center-owner boundary

For primes outside `60*e_r*e_(r-1)`, the reverse theorem gives the exact
valuation `v_p(3Y-d)=3v_p(g)`.  This is recorded only as a restriction.  It
does not claim that a center bucket is bounded, and the primitive `g=1`
branch remains untouched.

The kernel wrapper `good_primePower_exact_gap_center_residual` makes every
word “exact” auditable: for `H=p^a` the complementary factors in `d` and `Y`
are coprime to `H`, the linear residual contains exactly `H^2`, and the
centered residual contains exactly `H^3`.

### Third/fourth fixed-obstruction overclaim

Explicitly falsified.  The verifier lifts the full scale polynomial, one
base-`p` digit at a time, through `p^32` for one good prime in every row.  It
then selects primitive representatives satisfying `v<u<2v` and `u^k<4v^k`.
With `v_p(g)=3`, all six fixtures have the exact good-prime valuations and
still satisfy the full scale congruence modulo `p^9`, `p^12`, and `p^15`.
Consequently neither the third, fourth, nor fifth local order supplies a
fixed divisor/size cutoff.  These fixtures are not integer solutions; they
delimit what local Hensel information can prove.

### Target-equivalent missing lemma

The missing infinite statement is not counted as proved progress.  The new
content is the explicit, reproduced 46-order band
`10^120<=d<10^166` plus the kernel denominator and floor machinery.  The
remaining lemma is stated exactly as the tail `d>=10^166` in the findings.

## Kernel gate

Direct compilation reports only subsets of

```text
[propext, Classical.choice, Quot.sound].
```

The scale, generated-certificate, and headline modules contain no
`native_decide`, `sorry`, `admit`, private axiom, or external theorem
interface.  The telescope checks and all six Farey trees use ordinary kernel
`decide`.

## Final audit verdict

Admit the new arithmetic lemmas and the fully kernel-checked finite-band
headline as proper progress.  Do not update `OddThueTailHypothesis` or claim
Target 1 closed: the exact remaining gap is the six-row tail `d>=10^166`.
