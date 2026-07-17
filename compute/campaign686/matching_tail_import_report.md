# Erdős 686 Large-\(k\) Matching-Tail Import Report

Date: 2026-07-16

Status: in progress. Claims 1–8 are kernel-checked.  Claim 9 is
kernel-checked after separating its exact mass premise.  No unconditional
large-\(k\) exclusion theorem is claimed yet.

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

Accepted and kernel-checked.

Lean interfaces:

- `Erdos686.Erdos686Variant.sq_dvd_eval_sub_eval_sub_derivative`
- `Erdos686.Erdos686Variant.owner_sq_dvd_matchingResultant_tangent_defect`
- `Erdos686.Erdos686Variant.matched_owner_sq_dvd_matchingResultant_tangent_defect`

The last theorem starts from the actual normalized binomial owner-square
congruence, so the result is not merely the independently checked polynomial
identity in `tangent_defect_crt_certificate.json`.

### 8. Exact CRT

Accepted after exposing all cancellation and inversion hypotheses.

Lean interfaces:

- `Erdos686.Erdos686Variant.owner_dvd_resultantQuotient_tangent_defect`
- `Erdos686.Erdos686Variant.resultantQuotient_tangent_modEq_explicit_inverse`
- `Erdos686.Erdos686Variant.tangentCRTRepresentative_modEq`
- `Erdos686.Erdos686Variant.tangentCRTRepresentative_lt_product`

The local theorem writes `R=M*U`, `M=P*Mrest`, and the row term as
`P*xrest`, cancels one nonzero `P` from the square divisor, and requires an
explicit Bézout identity for `b*Mrest` before inversion modulo the possibly
composite owner. The finite CRT representative satisfies every local residue
and lies below the exact product modulus.

### 9. Collinear-support exclusion

Accepted after repair and kernel-checked.

Lean interfaces:

- `Erdos686.Erdos686Variant.secantLine_coefficients_bounded`
- `Erdos686.Erdos686Variant.support_product_dvd_affineLineResultant`
- `Erdos686.Erdos686Variant.collinear_support_card_le_two_of_resultant_eq_zero`
- `Erdos686.Erdos686Variant.affineLineResultant_natAbs_lt_three_k_sq_mul_d`
- `Erdos686.Erdos686Variant.collinear_matching_support_excluded_of_nat_mass`
- `Erdos686.Erdos686Variant.collinear_matching_support_excluded_of_secantLine_nat_mass`

The zero-resultant branch is closed internally: a common line through the
translated solution point would make every secant zero, so the
maximum-degree-one theorem limits the line to two support cells.  The nonzero
branch is excluded from the exact natural comparison

`3*k^2*d < product owner`.

No residual zero/nonzero hypothesis remains.

### 10. Large-\(k\) tail exclusion

Not accepted yet.

The previously missing canonical support bridge is now kernel-checked:

- `canonicalLargeOwnerSupport_product_eq_kLargePart` proves that the product
  of the projected nonunit owner cells is exactly the complete above-\(k\)
  part of the lower block;
- projected cells retain lower, upper, and signed-diagonal divisibility and
  are pairwise coprime;
- row and signed-diagonal support capacities are at most \(k\), with no
  connectedness or minimum-degree assumption;
- `exists_fixedColumn_canonicalLarge_matching` extracts an actual
  row-diagonal matching whose product \(X\) satisfies
  `kLargePart <= X^k`.

The \(k\)-th-power loss is the sharp unconditional fixed-column cover bound
and is far too large for the advertised matching mass comparison.  Thus the
remaining mathematical gap is now a precise stability theorem extracting a
matching with substantially more mass, followed by the exact threshold
comparison; it is not a missing equality between the canonical owner matrix
and `kLargePart`.

The next multiplicative-capacity layer is now kernel-checked:

- every row-fibre product divides its single lower consecutive term;
- every signed-diagonal-fibre product divides its single centered-window
  term;
- the complete high-prime mass divides both the lower-block lcm and the
  centered `(2*k-1)`-term product;
- the collision product has the exact integral factorization `Xi=M*E`;
- `E=1`, equivalently `Xi=M`, forces the complete support to be a
  row-diagonal matching.

This does not prove the required weighted matching theorem.  Moreover, the
kernel-checked uniform two-regular endpoint has `Xi=M^2` and a matching
product `X` with `X^2=M`.  Therefore the exponent-two diffuse loss is sharp
for row/diagonal capacities alone.  Any valid global closure must add
arithmetic that excludes or destabilizes this two-regular collision core.

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

An axiom-clean Chebyshev replacement has now been banked, including
`8*pi(k)<k` for every `k>=10^10`.  It is not contiguous with the exact scan:
direct use of the formal Chebyshev expression becomes favorable only around
`k=342471419`, while the convenient rational bound starts at `10^10`.
Therefore it leaves a genuine uncovered interval beginning at `10^6` and is
recorded only as a valid tail input, not as acceptance of Claim 10.

## Independent artifact hashes

- `secant_pairing_certificate.json`:
  `822efab3aef6fcaf781466a306c78ecbd0817dd3ed5a7ba7e283e20c7d37c79d`
- `tangent_defect_crt_certificate.json`:
  `e196623042344f47deff452d97e49913e3c5409833bb3bb8de04310e3b884314`
- `matching_tail_threshold.json`:
  `e8f4c6575400a4e8428540548ff8f353b66566fc2caf55b1b0dbcb1d387e256e`
- `verify_matching_tail.py`:
  `6f6b7c1efcd5bdf8be080f41a8b298e65febb5fd3ed4597adb5d52dac0212958`
- `Erdos686TangentDefectCRT.lean`:
  `e68902eaa2e7cd21fbb9220abd765f281c1eefb40d6b20fbe0e2996acbb0626a`
- `Erdos686CollinearSupport.lean`:
  `e9ac40d3d66bdcb06d3ae80e2b5742e0c13e2d0bf2d30e55a517ce440506e578`
- `Erdos686CanonicalLargeOwnerSupport.lean`:
  `913ff85aed35f34d22a5b58e218fbd593e8c7f2722c184011c00163207ff80a4`
- `Erdos686CanonicalLargeOwnerCapacity.lean`:
  `a23c0ab4df12b00f31bc5da1b9997ecdc1fc7e613ab1c14dc7eea54e0103b56b`
- `Erdos686LargeOwnerCollisionStability.lean`:
  `3e8581f36837874ce94019f61a5d08cba3fe576a2b50433d27df28daa54d2a10`
- `Erdos686MatchingTailChebyshev.lean`:
  `8939d16c75b814b83a0cd5c5b35d57cda0df4066db13e2a3b37511d58c5c9127`
