# Erdős 686 Large-\(k\) Matching-Tail Import Report

Date: 2026-07-16

Status: in progress. Claims 1–4 are kernel-checked. No large-\(k\) exclusion theorem is claimed yet.

## Source provenance

The audited source is:

`/Users/williamblair/.codex/attachments/1f82548d-fb9e-4e42-b260-dabfc4dae6a6/pasted-text.txt`

SHA-256:

`24ac3e82df67cba2ec87f87856ecd10d4ddfb005c68aa2e6230830571eda644f`

The source links `normalized_matching_certificate.json` and
`verify_normalized_matching.py` under `sandbox:/mnt/data/`. Those files were
not attached in this workspace. Their reported hashes are provenance notes,
not reproduced verifier evidence:

- reported normalized certificate:
  `063f0e540c01f00678c924d6e818ebb8c3b84ae4f9fb5dd4bfa5ce42db701247`
- reported verifier:
  `aaf956d71a6bebfe1ebdfcc6fc4c357316978ae373d3926fb354a53828873223`

The certificate files in this directory are independently generated audit
artifacts and do not impersonate those missing files.

## Claim audit

### 1. Two-owner secant divisor

Accepted and kernel-checked, with explicit coprimality.

Lean interfaces:

- `Erdos686.Erdos686Variant.twoOwnerSecantForm_recenter`
- `Erdos686.Erdos686Variant.two_owner_secant_dvd`

The divisor statement is false without coprimality of the two composite
owner moduli; the Lean theorem exposes that hypothesis.

### 2. Zero-secant classification

Accepted after repair and kernel-checked.

Lean interfaces:

- `Erdos686.Erdos686Variant.zero_secant_direction_classification`
- `Erdos686.Erdos686Variant.zero_secant_classification`
- `Erdos686.Erdos686Variant.large_k_zero_secant_scale`
- `Erdos686.Erdos686Variant.large_k_zero_secant_classification`

The source left the scale derivation in prose. Lean now derives it from the
exact threshold

`708827 * k^2 < 5000000 * d`

and the banked equation-facing ratio `23*k*d < 35*n`. The boundary
`k=16,...,22` is checked by exact arithmetic inside the ordinary kernel
proof.

### 3. Zero-secant graph

Accepted and kernel-checked.

Lean interfaces:

- `Erdos686.Erdos686Variant.zero_secant_neighbor_unique`
- `Erdos686.Erdos686Variant.zero_secant_graph_max_degree_one`

The theorem requires injectivity of diagonal offsets on the support.

### 4. Controlled pairing

The source proof is rejected as written. “Repair by neighboring two or four
vertices” does not specify an algorithm or prove termination, and maximum
degree one alone is not sufficient to justify all cross-pairs.

The repaired deterministic construction is:

- sort the distinct integer offsets;
- leave the final owner unmatched exactly when the owner count is odd;
- use four-entry blocks paired `(1,3),(2,4)`;
- when the number of base pairs is odd, use one six-entry block paired
  `(1,3),(2,5),(4,6)`.

Every selected pair skips at least one distinct integer offset, so its gap is
at least two and the zero-secant classification makes its secant nonzero.
Each block costs at most twice its span, and disjoint block spans give total
gap at most twice the full support span, hence at most `4*(k-1)`.

The repaired construction is accepted and kernel-checked.

Lean interfaces:

- `Erdos686.Erdos686Variant.controlledPairing`
- `Erdos686.Erdos686Variant.pairedEntries_perm`
- `Erdos686.Erdos686Variant.controlledPairing_core_spec`
- `Erdos686.Erdos686Variant.unmatched_length_eq_mod_two`
- `Erdos686.Erdos686Variant.pair_count_eq_div_two`
- `Erdos686.Erdos686Variant.explicit_controlled_pairing`
- `Erdos686.Erdos686Variant.controlled_pairing_secants_nonzero`
- `Erdos686.Erdos686Variant.controlled_pairing_total_gap_le_four_k_sub_one`

The exact block data are independently checked by
`secant_pairing_certificate.json`.

### 5. Product upper bound

Accepted and kernel-checked, including the optional parity owner and with
every denominator cleared.

Lean interfaces:

- `Erdos686.Erdos686Variant.list_nary_amgm`
- `Erdos686.Erdos686Variant.paired_product_upper_of_weight_sum`
- `Erdos686.Erdos686Variant.controlled_pairing_product_upper`
- `Erdos686.Erdos686Variant.controlled_matching_full_product_upper`

### 6. Matching interpolation

Partially accepted. Given an integer interpolation polynomial with the
claimed node values, the local and global common-resultant divisibility is
kernel-checked. Construction of the specific integer interpolation
polynomial remains pending.

Lean interfaces:

- `Erdos686.Erdos686Variant.owner_dvd_matchingResultant`
- `Erdos686.Erdos686Variant.matching_support_product_dvd_resultant`
- `Erdos686.Erdos686Variant.owner_cell_support_product_dvd_resultant`

### 7. Tangent-defect square theorem

The polynomial identity has been independently checked in
`tangent_defect_crt_certificate.json`. The full divisibility theorem remains
pending in Lean and is not counted as accepted.

### 8. Exact CRT

Pending. In particular, division by `M` and inversion modulo every composite
owner must expose all nonzero and coprimality hypotheses.

### 9. Collinear-support exclusion

Pending. The source argument depends on the support-size lower bound and the
mass comparison, neither of which has yet been imported from this package.

### 10. Large-\(k\) tail exclusion

Not accepted yet.

The exact finite comparison has been independently reduced to

\[
k^{k-p}d_0^E2^\delta q^q >
(k-1)!\,3^{p+\delta}2^{q+k-2p}(k-1)^q(q+2k+2)^q,
\]

where \(p=\pi(k)\), \(q=\lfloor k/2\rfloor\),
\(\delta=k\bmod 2\),
\(E=k-p-q-\delta\), and
\(d_0=\lfloor708827k^2/5000000\rfloor+1\).

The independently verified candidate minimal suffix is

`K0 = 18986`,

with `k=18985` the last failure. This remains conditional on the pairing
product upper bound and the symbolic analytic tail beginning at
`k=1000000`.

## Exact verifier policy

`verify_matching_tail.py` uses:

- an exact Eratosthenes sieve and exact \(\pi(k)\);
- exact factorial boundary values;
- correctly rounded Decimal logarithms widened outward by one Decimal unit;
- directed outward interval arithmetic;
- exact cleared integer comparison whenever an interval contains zero.

Binary floating-point logarithms are not acceptance conditions. The
analytic prime-counting estimate beyond the finite scan is an imported
mathematical theorem and must be kernel-banked before the final tail
exclusion can be called formal.

## Independent artifact hashes

- `secant_pairing_certificate.json`:
  `822efab3aef6fcaf781466a306c78ecbd0817dd3ed5a7ba7e283e20c7d37c79d`
- `tangent_defect_crt_certificate.json`:
  `e196623042344f47deff452d97e49913e3c5409833bb3bb8de04310e3b884314`
- `matching_tail_threshold.json`:
  `e8f4c6575400a4e8428540548ff8f353b66566fc2caf55b1b0dbcb1d387e256e`
- `verify_matching_tail.py`:
  `6f6b7c1efcd5bdf8be080f41a8b298e65febb5fd3ed4597adb5d52dac0212958`
