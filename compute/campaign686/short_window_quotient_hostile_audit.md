# Hostile audit: Erdős 686 ShortWindowQuotient package

Verdict: **PASS as a proper partial package.**  The generic Lean module is
safe to integrate.  The finite 2,603-placement application remains exact
Python arithmetic plus generic Lean and is **not** an attestation-ready
row-quantified theorem.

The package does not close the three-owner branch or Erdős #686.

## 1. Frozen producer boundary

The existing `Erdos686ShortWindowQuotientAudit.lean` is frozen as a
producer-side importer, not treated as independent hostile evidence.

```text
bf18db4af88be78e7f4400a6cdc67b5bfb66ddef8dc12fe1072e7ad1b3903ccc
  ErdosProblems/Erdos686ShortWindowQuotient.lean
6ff2c48c62b4c77e560378888553485ede2502126ba468abbe1e45cbd373d54a
  ErdosProblems/Erdos686ShortWindowQuotientAudit.lean
af60785ae52a199a13a72759d133b6c1d6919a22dcb0d4b4172a892a2faafe0d
  compute/campaign686/short_window_quotient_attack.py
37e2f43d6169ae6fe0cf7cecbb4c23213087504d87e4d873f1a27f33ec1d78f3
  compute/campaign686/test_short_window_quotient_attack.py
b1365cdaba351c96f453c08737bf48babbe94a906a094512babd145f047f010a
  compute/campaign686/short_window_quotient_findings.md
4c228bff302f2e5fcd45ff4b9347eec1101299412807953b202415cfd0eced29
  docs/plans/2026-07-10-erdos686-short-window-quotient-attack.md
```

Fresh hostile artifacts, excluding this self-referential report:

```text
15b855d6afd7c1a27582e8e5a4dbc6483dba909c3bff44307eb9ad8383e585ec
  ErdosProblems/Erdos686ShortWindowQuotientHostileAudit.lean
1a6dad5951484a3c2351b982fdfbf779acee749df82b122f070cf4b994b95d86
  compute/campaign686/short_window_quotient_hostile_verify.py
bcd36bade9c4f98f82fd01f16e70143a79ee262a329cd0c029724653e69c4964
  compute/campaign686/test_short_window_quotient_hostile_verify.py
21a12b5fcac213660360f78ca68518189de66a2e148b661f47a3d346fba7c4f8
  docs/plans/2026-07-10-erdos686-short-window-quotient-hostile-audit.md
```

The hostile Python verifier imports no producer module.  It reconstructs
Taylor coefficients as elementary-symmetric subset sums rather than using
the producer's affine convolution.

## 2. Public theorem audit

The producer exports five definitions and thirteen theorems.  The fresh
hostile Lean module independently reproves all thirteen theorem statements.

| Producer theorem | Audited conclusion | Verdict |
|---|---|---|
| `three_bucket_reduced_fourth_identity` | exact signed polynomial reduction | PASS |
| `square_factor_cancel_from_cube_dvd` | cancel `P^2` when `P!=0` | PASS |
| `three_bucket_fourth_to_third_quotient` | fourth divisibility gives quotient divisibility | PASS |
| `three_bucket_fourth_obstruction_to_quotient` | direct banked-obstruction specialization | PASS |
| `three_bucket_reduced_fourth_quotient_dvd` | eliminate `t` with the second obstruction | PASS |
| `three_bucket_fourth_obstruction_reduced_dvd` | composed fixed-coefficient congruence | PASS |
| `three_bucket_reduced_fourth_coefficient_eq_zero_of_odd_coefficients` | center degeneracy when `D=H=0` | PASS |
| `common_component_third_quotient_dvd_fixed` | quotient overlap divides `K*g^4` | PASS |
| `common_component_opposite_cofactor_dvd_offset` | cofactor overlap divides `3*delta` | PASS |
| `three_third_quotient_lattice_identity` | annihilate common `t` and `u*d` variables | PASS |
| `two_zero_third_quotient_gap_square_bound` | `d^2 W <=L^2 Gamma g^12` | PASS |
| `two_zero_third_quotient_gap_lt_cutoff` | abstract numeric cutoff | PASS |
| `third_quotient_bound_of_short_window` | proper bound `5z<B g^2 a` | PASS |

The producer-side importer declares no theorem or lemma of its own.  It
checks two constants and prints producer axioms; the hostile module supplies
the missing independent proof layer.

## 3. Dependency tree

```text
second + third + fourth lifts
|
+- Q1 cancel P^2 from the fourth divisibility
|  `- P | 3bc*z+J
|
+- Q2 exact reduced-fourth identity
|  `- P | 27C^2bc*z+K*g^4
|
+- Q3 overlap consequences
|  +- gcd(P,z) | K*g^4
|  `- gcd(P,b) | 3*owner-offset
|
+- Q4 three-row lattice identity
|  `- sum w_s P_s^2 z_s =g^2 Gamma
|
`- Q5 two noncentral zero quotients
   +- P,Q | L*g^4
   +- if remaining weight=0: contradiction from g>0 and Gamma!=0
   +- otherwise R^2*|w_R| <=|Gamma|g^2
   `- d^2*|w_R| <=L^2|Gamma|g^12
```

Q1--Q5 are generic kernel theorems.  Substituting every target-row
coefficient and checking the cutoff is an exact finite computation, not a
row-quantified Lean wrapper.

## 4. Independent coefficient and lattice reconstruction

Across all six target rows:

```text
ordered distinct owner triples:       6210
center-owner occurrences:              502
zero reduced coefficients:             502
unordered rank-two lattice triples:   1035
zero lattice-weight components:          27
```

Every reduced coefficient zero occurs at the odd-row center.  Every lattice
Gamma is nonzero.  The extrema reproduce exactly:

```text
min nonzero |K_s| =17729280,
max |K_s| =7628070240970929200984341763734527541248000
  at (k,s,u,v)=(15,1,14,15),
min |Gamma| =2160,
max |Gamma| =4070625913172821209661440.
```

The signed identity grid contains 1,377 exact cases, including negative and
zero `t,g`, centers, and reflected owners; all pass.

## 5. The 2,603 two-zero placements

The hostile verifier independently enumerates every unordered owner triple
and every pair of noncentral zero positions.

| `k` | cases | zero-weight contradictions | numeric closures | closed | open |
|---:|---:|---:|---:|---:|---:|
| 5 | 18 | 2 | 16 | 18 | 0 |
| 7 | 75 | 3 | 72 | 75 | 0 |
| 9 | 196 | 4 | 192 | 196 | 0 |
| 11 | 405 | 5 | 400 | 405 | 0 |
| 13 | 726 | 6 | 720 | 726 | 0 |
| 15 | 1183 | 7 | 894 | 901 | 282 |

Totals:

```text
noncentral two-zero placements: 2603
closed placements:              2321
```

Both advertised conclusions are exact:

1. every noncentral two-zero placement is closed for `k<=13`;
2. exactly 901 of 1,183 noncentral placements are closed for `k=15`.

The first open row-15 case is

```text
indices [1,2,3], zero positions [0,1],
remaining weight 827009339,
L=271807019335111703420341421246717838874046408410791936000,
|Gamma|=398569323412788480000,
majorant digits 257, cutoff-side digits 249.
```

No closure is claimed for the remaining 282 placements.

## 6. Boundary audit

- **Centers remain open.**  At the row center `D=H=0`, hence `K_s=0` and
  the fixed-coefficient component bound is vacuous.  Two-zero placements
  containing a center are intentionally outside the 2,603 count.
- **Positive loss is load-bearing.**  A zero remaining lattice weight gives
  `0=g^2 Gamma`; this contradicts `Gamma!=0` only because `g>0`.
- **Pairwise coprimality is load-bearing.**  Dropping it at
  `(P,Q,R,g,L,Gamma,W)=(8,8,1,2,1,1,1)` preserves the individual
  divisibilities and weighted square premise but falsifies the generic gap
  square conclusion.
- **The row-15 numerical gate genuinely stops.**  Its 282 failures are
  inequalities in the wrong direction, not missing enumeration cases.
- **Small primes are real.**  The independent fixture
  `(P,Q,R,g,d)=(3,5,2,24,720)` satisfies every local and composed lift,
  quotient normalization, lattice identity, and new quotient restriction;
  it fails the original block equation.
- **Below-cutoff systems are nonempty.**  The frozen 20,000 search has 33
  survivors; the 200,000 search has 38, with largest gap 11,484.  All fail
  the block equation and lie below `10^120`.
- **The target Hensel diagnostic is not a solution.**  Producer tests verify
  its local/composed lifts, but it fails the upper short window and block
  equation.

## 7. Exact scope and remaining gap

Integration is safe for the thirteen generic Lean theorems and the exact
finite diagnostic.  It is not safe to describe the 2,603-case application as
kernel-banked: no six-row Lean wrapper instantiates `K`, `L`, `Gamma`, the
weights, and all numeric cutoffs.

The live branches remain:

- all three third quotients nonzero;
- exactly one quotient zero;
- center-containing multi-zero placements;
- 282 noncentral two-zero placements in row 15.

The quantified system in findings section 8 remains unproved and is stronger
than the equation-specific three-owner slice because it omits `n` and the
block equation.  The package closes neither the three-owner branch nor
Erdős #686.

## 8. Frozen findings prose note

Findings line 353 repeats line 83:

```text
P_s^3 | 3a_u a_v T_s + P_s^2 J_s,
```

In section 8 this is a restatement of the remaining system, not a second
mathematical premise or duplicated computation.  It has no semantic effect:
Markdown is not imported by Lean or Python.  The frozen findings file is left
unchanged.

## 9. Axiom and forbidden gate

Producer, producer-side importer, and independent hostile Lean modules all
compile.  Every producer and hostile theorem stays within

```text
[propext, Classical.choice, Quot.sound].
```

There is no `native_decide`, `sorry`, `admit`, custom axiom, or unsafe
declaration.  Compiler output is limited to non-material linter advice.

## 10. Reproduction

```bash
lake env lean ErdosProblems/Erdos686ShortWindowQuotient.lean
lake env lean ErdosProblems/Erdos686ShortWindowQuotientAudit.lean
lake env lean ErdosProblems/Erdos686ShortWindowQuotientHostileAudit.lean

python3 -m pytest \
  compute/campaign686/test_short_window_quotient_attack.py \
  compute/campaign686/test_short_window_quotient_hostile_verify.py -q

python3 compute/campaign686/short_window_quotient_hostile_verify.py --pretty
```

Frozen results:

```text
producer tests:              7 passed
independent hostile tests:   7 passed
producer Lean:               PASS
producer importer:           PASS
independent hostile Lean:    PASS
```

No frozen producer file, shared import, manifest, root documentation,
attestation, or commit was changed.
