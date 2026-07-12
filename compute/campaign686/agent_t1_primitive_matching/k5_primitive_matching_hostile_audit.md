# Hostile audit: k=5 primitive factor matching

## Dependency tree

```text
k=5 centered equation
├── primitive normalization X=g*u, Y=g*v, z=g^2, gcd(u,v)=1
├── exact common quotient
│   ├── U=v*a
│   └── 4V=u*a
├── fixed gcd losses
│   ├── gcd(a,u)|4
│   ├── gcd(a,v)|16
│   └── gcd(T-1,T-4)|3
├── odd-scale substitution 4v-u=z*t
│   ├── v | product(W±1,W±2)
│   └── u | product(W±4,W±8)
└── fixed affine ray u=A*t, v=B*t-1
    └── v | (A^2-B^2)(A^2-4B^2)
```

The common quotient node is equation-facing.  The scan and counterfamily
nodes are negative tests only and are not dependencies of any theorem.

## Per-node verdict

| Node | Verdict | Evidence |
|---|---|---|
| common quotient | PASS | `k5_common_matching_quotient`, ordinary Lean kernel |
| gcd loss at `u` | PASS | `k5_common_quotient_gcd_u_dvd_four` |
| gcd loss at `v` | PASS | `k5_common_quotient_gcd_v_dvd_sixteen` |
| quadratic-factor gcd | PASS | `k5_quadratic_factor_gcd_dvd_three` |
| upper `W` compression | PASS | `k5_upper_matching_compresses_to_W` |
| lower `W` compression | PASS | `k5_lower_matching_compresses_to_W`; outer `4` retained |
| affine resultant | PASS | `k5_affine_ray_resultant_dvd` |
| full primitive closure | OPEN | no exponent improvement over `g^2=O(v)` and no descent |

## Quantified-language audit

- “Almost coprime” means exactly `gcd(a,u)|4` and `gcd(a,v)|16`.
- “One variable” means exactly `W=g^3*t` under `u+g^2*t=4v`.
- “Fixed ray is finite” means exactly (9) in the findings, conditional on
  fixed positive `A,B` and nonzero resultant.
- “Unbounded boundary” means the displayed formula for every `m>=0`; the
  verifier checks `m=0,1,10^6,10^40`, and the symbolic identities prove the
  universal statement.
- No phrase “essentially Pell,” “generic,” or “uniformly bounded” is used as
  a proof step.

## Falsification fixtures

### Existing unbounded low-filter family

The campaign's `scale_filter_counterfamily.py` does not satisfy either new
matching divisibility at its first point.  It is therefore not reused as a
counterexample to the matching interface.  This is a strengthening relative
to the low scale filters, not a closure.

### Target-scale one-direction family

The family in section 4.2 of the findings reaches `d>10^120` at
`m=10^40`.  It satisfies only the upper matching direction.  The reverse
remainder is checked nonzero in every stored sample.  No two-direction claim
is inferred from it.

### Both-direction finite scan

Every one of the 25 rows through `v=200000` has both divisibilities and
unequal quotient values.  The scan constructs all prime-power roots,
including `p=2` and `p=3`, rather than assuming four roots at bad primes.

### `d=1` telescopes

The `k=9` and `k=15` telescope fixtures are genuine equations and hence pass
their corresponding factor-matching identities.  This file proves only a
`k=5` interface and makes no cross-row exclusion.  Any generalization must
retain the domain hypothesis `d>=k`; nothing here rejects a telescope by a
congruence that it actually satisfies.

## Arithmetic reproduction

```text
python3 -m pytest -q \
  compute/campaign686/agent_t1_primitive_matching/test_k5_primitive_matching_verify.py

lake env lean ErdosProblems/Erdos686K5PrimitiveFactorMatching.lean
```

The Python verifier uses integer arithmetic only.  The Lean file uses no
`native_decide`; its printed axioms are contained in
`[propext, Classical.choice, Quot.sound]`.
