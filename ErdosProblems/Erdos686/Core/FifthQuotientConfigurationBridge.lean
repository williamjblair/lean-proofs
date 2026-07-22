/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.FifthQuotientKernelCertificate
import ErdosProblems.Erdos686.Core.ThirdObstructionNonzero

/-!
# Erdős 686: construct the selected-three fifth-quotient configuration

The finite fifth-quotient theorem previously accepted its local product,
third-quotient, opposite-product, fourth-quotient, and normalized-fifth
identities as explicit premises.  This module constructs all of those
identities from one actual selected three-bucket decomposition

`d = g * P * Q * R`

together with the three exact square residuals and the block equation.  It
also carries the genuine fifth-order consequence `P ∣ N`.  Thus the finite
ledger applies to actual selected-three data; it is not merely a conditional
polynomial statement.

This is a compositional bridge, not a contradiction.  It treats one cyclic
owner at a time and supplies no simultaneous magnitude or gcd estimate for
the three nonzero normalized numerators.
-/

namespace Erdos686
namespace Erdos686Variant

open scoped BigOperators

set_option maxHeartbeats 200000000 in
-- The ordinary-kernel metadata decision expands all 3,024 target positions.
set_option maxRecDepth 1000000 in
/-- The imported finite table also places both opposite indices in the full
owner grid and records the three pairwise inequalities needed to remove the
three selected buckets from its product. -/
theorem fifth_quotient_target_position_full_metadata_certificate :
    ∀ p ∈ fifthQuotientTargetPositions,
      p.owner ∈ allOwnerGrid p.k ∧
      p.left ∈ allOwnerGrid p.k ∧
      p.right ∈ allOwnerGrid p.k ∧
      p.owner ≠ p.left ∧ p.owner ≠ p.right ∧ p.left ≠ p.right := by
  decide +kernel

/-- Remove any three distinct selected buckets from the exact all-owner
factorization, absorbing every omitted bucket into a single explicit loss.

The resulting loss is not asserted to satisfy the original bounded-loss
estimate: that estimate is retained exactly only when every omitted bucket is
a unit. -/
lemma allOwner_gap_decomposition_at_three
    {k n d i j l : ℕ} {owner : ℕ → ℕ}
    (hi : i ∈ allOwnerGrid k)
    (hj : j ∈ allOwnerGrid k)
    (hl : l ∈ allOwnerGrid k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hd : 0 < d)
    (hassign : GlobalResidualOwnerAssignment k n d owner) :
    ∃ g : ℕ,
      d = g * allOwnerBucket k d owner i *
        allOwnerBucket k d owner j * allOwnerBucket k d owner l := by
  classical
  let rest := (((allOwnerGrid k).erase i).erase j).erase l
  let g := globalResidualGroupedLoss k d *
    ∏ x ∈ rest, allOwnerBucket k d owner x
  refine ⟨g, ?_⟩
  have hjErase : j ∈ (allOwnerGrid k).erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hlErase : l ∈ ((allOwnerGrid k).erase i).erase j :=
    Finset.mem_erase.mpr ⟨hjl.symm,
      Finset.mem_erase.mpr ⟨hil.symm, hl⟩⟩
  calc
    d = globalResidualGroupedLoss k d *
        ∏ x ∈ allOwnerGrid k, allOwnerBucket k d owner x :=
      allOwner_gap_decomposition hd hassign
    _ = globalResidualGroupedLoss k d *
        allOwnerBucket k d owner i * allOwnerBucket k d owner j *
          allOwnerBucket k d owner l *
            ∏ x ∈ (((allOwnerGrid k).erase i).erase j).erase l,
              allOwnerBucket k d owner x := by
      rw [← Finset.mul_prod_erase (allOwnerGrid k)
        (allOwnerBucket k d owner) hi]
      rw [← Finset.mul_prod_erase ((allOwnerGrid k).erase i)
        (allOwnerBucket k d owner) hjErase]
      rw [← Finset.mul_prod_erase (((allOwnerGrid k).erase i).erase j)
        (allOwnerBucket k d owner) hlErase]
      ring
    _ = g * allOwnerBucket k d owner i *
        allOwnerBucket k d owner j * allOwnerBucket k d owner l := by
      simp only [g, rest]
      ring

/-- A signed square-residual identity reconstructs the natural
`localResidual` exactly. -/
lemma localResidual_eq_of_signed_square
    {n d i a P : ℕ}
    (hres : 3 * ((n + i : ℕ) : ℤ) - (d : ℤ) =
      (a : ℤ) * (P : ℤ) ^ 2) :
    localResidual n d i = a * P ^ 2 := by
  have hnonneg : (0 : ℤ) ≤ (a : ℤ) * (P : ℤ) ^ 2 := by positivity
  have hle : d ≤ 3 * (n + i) := by
    exact_mod_cast (show (d : ℤ) ≤ 3 * ((n + i : ℕ) : ℤ) by
      linarith [hres, hnonneg])
  have hcast : (localResidual n d i : ℤ) =
      (a : ℤ) * (P : ℤ) ^ 2 := by
    unfold localResidual
    rw [Int.ofNat_sub hle]
    simpa using hres
  exact_mod_cast hcast

/-- Direct selected-three bridge at one cyclic target position.  The
conclusion constructs the named third quotient `z`, reduced fourth quotient
`w`, and normalized fifth numerator `N`; it proves the true fifth-order
divisibility `P ∣ N` and the equation-facing nonvanishing of `w,N`.

No primality, coprimality, or bounded-loss hypothesis is used. -/
theorem direct_selected_three_fifth_quotient_configuration
    {p : FifthQuotientPosition}
    (hp : p ∈ fifthQuotientTargetPositions)
    {n d P Q R g a b c : ℕ}
    (hdTarget : 10 ^ 1000 ≤ d)
    (hPpos : 0 < P)
    (hdecomp : d = g * P * Q * R)
    (hPfactor : P ∣ n + p.owner)
    (hPi : 3 * ((n + p.owner : ℕ) : ℤ) - (d : ℤ) =
      (a : ℤ) * (P : ℤ) ^ 2)
    (hQj : 3 * ((n + p.left : ℕ) : ℤ) - (d : ℤ) =
      (b : ℤ) * (Q : ℤ) ^ 2)
    (hRl : 3 * ((n + p.right : ℕ) : ℤ) - (d : ℤ) =
      (c : ℤ) * (R : ℤ) ^ 2)
    (heq : blockProduct p.k (n + d) = 4 * blockProduct p.k n) :
    ∃ z w N : ℤ,
      threeBucketThirdObstruction
          (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
          a b c g (fifthPositionDeltaLeft p)
          (fifthPositionDeltaRight p) d = (P : ℤ) ^ 2 * z ∧
      (P : ℤ) * w =
        27 * fifthPositionC p ^ 2 * (b : ℤ) * (c : ℤ) * z +
          fifthPositionK p * (g : ℤ) ^ 4 ∧
      N = 27 * w + (g * Q * R : ℕ) * fifthPositionR1 p * (g : ℤ) ^ 4 ∧
      (P : ℤ) ∣ N ∧
      w ≠ 0 ∧ N ≠ 0 := by
  have hi := (fifth_quotient_target_position_metadata_certificate p hp).2
  have hPM : d = P * (g * Q * R) := by rw [hdecomp]; ring
  have hdecompInt : (d : ℤ) = (g : ℤ) * P * Q * R := by
    exact_mod_cast hdecomp
  have hleft :
      (a : ℤ) * (P : ℤ) ^ 2 - (b : ℤ) * (Q : ℤ) ^ 2 =
        3 * fifthPositionDeltaLeft p := by
    rw [← hPi, ← hQj]
    simp [fifthPositionDeltaLeft]
    ring
  have hright :
      (a : ℤ) * (P : ℤ) ^ 2 - (c : ℤ) * (R : ℤ) ^ 2 =
        3 * fifthPositionDeltaRight p := by
    rw [← hPi, ← hRl]
    simp [fifthPositionDeltaRight]
    ring
  have hsecondLocal := second_order_local_lift
    (k := p.k) (n := n) (d := d) (i := p.owner)
    (h := P) (m := g * Q * R) (a := a)
    hi hPpos hPM hPfactor hPi heq
  have hthirdLocal := third_order_local_lift
    (k := p.k) (n := n) (d := d) (i := p.owner)
    (h := P) (m := g * Q * R) (a := a)
    hi hPpos hPM hPfactor hPi heq
  have hfourthLocal := fourth_order_local_lift
    (k := p.k) (n := n) (d := d) (i := p.owner)
    (h := P) (m := g * Q * R) (a := a)
    hi hPpos hPM hPfactor hPi heq
  have hsecond := three_bucket_second_obstruction_dvd
    (P := (P : ℤ)) (Q := (Q : ℤ)) (R := (R : ℤ))
    (a := (a : ℤ)) (b := (b : ℤ)) (c := (c : ℤ)) (g := (g : ℤ))
    (C := fifthPositionC p) (D := fifthPositionD p)
    (deltaLeft := fifthPositionDeltaLeft p)
    (deltaRight := fifthPositionDeltaRight p)
    (by simpa [fifthPositionC, fifthPositionD] using hsecondLocal)
    hleft hright
  have hthird := three_bucket_third_obstruction_dvd_sq
    (P := (P : ℤ)) (Q := (Q : ℤ)) (R := (R : ℤ))
    (a := (a : ℤ)) (b := (b : ℤ)) (c := (c : ℤ)) (g := (g : ℤ))
    (C := fifthPositionC p) (D := fifthPositionD p)
    (E := fifthPositionE p)
    (deltaLeft := fifthPositionDeltaLeft p)
    (deltaRight := fifthPositionDeltaRight p)
    (by simpa [fifthPositionC, fifthPositionD, fifthPositionE] using hthirdLocal)
    hleft hright
  have hfourth := three_bucket_fourth_obstruction_dvd_cube
    (P := (P : ℤ)) (Q := (Q : ℤ)) (R := (R : ℤ))
    (a := (a : ℤ)) (b := (b : ℤ)) (c := (c : ℤ)) (g := (g : ℤ))
    (C := fifthPositionC p) (D := fifthPositionD p)
    (E := fifthPositionE p) (F := fifthPositionF p)
    (deltaLeft := fifthPositionDeltaLeft p)
    (deltaRight := fifthPositionDeltaRight p)
    (by simpa [fifthPositionC, fifthPositionD, fifthPositionE,
      fifthPositionF] using hfourthLocal)
    hleft hright
  have hfifth := target_three_bucket_fifth_obstruction_dvd_fourth
    (k := p.k) (n := n) (d := d) (i := p.owner)
    (j := p.left) (l := p.right) (P := P) (Q := Q) (R := R)
    (a := a) (b := b) (c := c) (g := g)
    hi hPpos hdecomp hPfactor hPi hQj hRl heq
  rcases hthird with ⟨z, hz⟩
  have hzD :
      threeBucketThirdObstruction
          (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
          a b c g (fifthPositionDeltaLeft p)
          (fifthPositionDeltaRight p) d = (P : ℤ) ^ 2 * z := by
    rw [hdecompInt]
    simpa [fifthPositionC, fifthPositionD, fifthPositionE] using hz
  have hfourthD :
      (P : ℤ) ^ 3 ∣
        threeBucketFourthObstruction P b c
          (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
          (fifthPositionF p) a g (fifthPositionDeltaLeft p)
          (fifthPositionDeltaRight p) d := by
    rw [hdecompInt]
    simpa [fifthPositionC, fifthPositionD, fifthPositionE,
      fifthPositionF] using hfourth
  have hreducedFourth := three_bucket_fourth_obstruction_reduced_dvd
    (P := (P : ℤ)) (b := (b : ℤ)) (c := (c : ℤ))
    (C := fifthPositionC p) (D := fifthPositionD p)
    (E := fifthPositionE p) (H := fifthPositionF p)
    (a := (a : ℤ)) (g := (g : ℤ))
    (deltaLeft := fifthPositionDeltaLeft p)
    (deltaRight := fifthPositionDeltaRight p) (gap := (d : ℤ))
    (z := z) (by exact_mod_cast hPpos.ne') hsecond hzD hfourthD
  rcases hreducedFourth with ⟨w, hw⟩
  let N : ℤ := 27 * w +
    (g * Q * R : ℕ) * fifthPositionR1 p * (g : ℤ) ^ 4
  have hfifthD :
      (P : ℤ) ^ 4 ∣
        threeBucketFifthObstruction P Q R b c
          (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
          (fifthPositionF p) (fifthPositionG p) a g
          (fifthPositionDeltaLeft p) (fifthPositionDeltaRight p) d := by
    simpa [fifthPositionC, fifthPositionD, fifthPositionE,
      fifthPositionF, fifthPositionG] using hfifth
  have hfifthQuotientRaw :=
    three_bucket_fifth_obstruction_to_third_quotient_sq
      (P := (P : ℤ)) (Q := (Q : ℤ)) (R := (R : ℤ))
      (b := (b : ℤ)) (c := (c : ℤ))
      (C := fifthPositionC p) (D := fifthPositionD p)
      (E := fifthPositionE p) (F := fifthPositionF p)
      (G := fifthPositionG p) (a := (a : ℤ)) (g := (g : ℤ))
      (deltaLeft := fifthPositionDeltaLeft p)
      (deltaRight := fifthPositionDeltaRight p) (gap := (d : ℤ))
      (z := z) (by exact_mod_cast hPpos.ne') hzD hfourthD hfifthD
  have hthirdReduced : (P : ℤ) ^ 2 ∣
      -9 * fifthPositionC p * ((a : ℤ) * b * c) +
        108 * fifthPositionD p * (g : ℤ) ^ 2 *
          (fifthPositionDeltaLeft p * fifthPositionDeltaRight p) +
        180 * fifthPositionE p * (g : ℤ) ^ 2 *
          (fifthPositionDeltaLeft p * fifthPositionDeltaRight p) * d := by
    have hthirdDvd : (P : ℤ) ^ 2 ∣
        threeBucketThirdObstruction
          (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
          a b c g (fifthPositionDeltaLeft p)
          (fifthPositionDeltaRight p) d := ⟨z, hzD⟩
    convert hthirdDvd using 1 <;>
      simp [threeBucketThirdObstruction, threeBucketSecondObstruction] <;> ring
  have hfifthQuotient : (P : ℤ) ^ 2 ∣
      9 * (b : ℤ) * c * z +
        3 * threeBucketFourthCorrection
          (fifthPositionD p) (fifthPositionE p) (fifthPositionF p)
          ((a : ℤ) * b * c) g
          (fifthPositionDeltaLeft p) (fifthPositionDeltaRight p) +
        (g : ℤ) ^ 2 * d *
          threeBucketFifthCorrection
            (fifthPositionE p) (fifthPositionF p) (fifthPositionG p)
            ((a : ℤ) * b * c) g
            (fifthPositionDeltaLeft p) (fifthPositionDeltaRight p) := by
    convert hfifthQuotientRaw using 1 <;> rw [hdecompInt] <;> ring
  have hreducedFifth := three_bucket_reduced_fifth_quotient_sq_dvd
    (P := (P : ℤ)) (C := fifthPositionC p) (D := fifthPositionD p)
    (E := fifthPositionE p) (F := fifthPositionF p)
    (G := fifthPositionG p) (t := (a : ℤ) * b * c) (g := (g : ℤ))
    (gap := (d : ℤ)) (b := (b : ℤ)) (c := (c : ℤ))
    (z := z) (deltaLeft := fifthPositionDeltaLeft p)
    (deltaRight := fifthPositionDeltaRight p)
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using hthirdReduced)
    hfifthQuotient
  have hnormDiv := three_bucket_reduced_fifth_normalized_quotient_dvd
    (P := (P : ℤ)) (C := fifthPositionC p) (D := fifthPositionD p)
    (E := fifthPositionE p) (F := fifthPositionF p)
    (G := fifthPositionG p) (g := (g : ℤ)) (gap := (d : ℤ))
    (b := (b : ℤ)) (c := (c : ℤ)) (z := z) (q := w)
    (M := (g * Q * R : ℕ))
    (deltaLeft := fifthPositionDeltaLeft p)
    (deltaRight := fifthPositionDeltaRight p)
    (by exact_mod_cast hPpos.ne') (by exact_mod_cast hPM)
    hw hreducedFifth
  have hNdiv : (P : ℤ) ∣ N := by
    simpa [N, fifthPositionR1] using hnormDiv
  have hPiNat := localResidual_eq_of_signed_square hPi
  have hQjNat := localResidual_eq_of_signed_square hQj
  have hRlNat := localResidual_eq_of_signed_square hRl
  have hproduct :
      (d : ℤ) ^ 2 * ((a : ℤ) * b * c) =
        (g : ℤ) ^ 2 *
          (localResidual n d p.owner : ℤ) *
          (localResidual n d p.left : ℤ) *
          (localResidual n d p.right : ℤ) := by
    rw [hPiNat, hQjNat, hRlNat]
    push_cast
    rw [hdecompInt]
    ring
  have hY : (localResidual n d p.left : ℤ) =
      (localResidual n d p.owner : ℤ) -
        3 * fifthPositionDeltaLeft p := by
    rw [hPiNat, hQjNat]
    push_cast
    linarith
  have hZ : (localResidual n d p.right : ℤ) =
      (localResidual n d p.owner : ℤ) -
        3 * fifthPositionDeltaRight p := by
    rw [hPiNat, hRlNat]
    push_cast
    linarith
  have hopposite :
      (d : ℤ) ^ 2 * (b : ℤ) * c * z =
        (g : ℤ) ^ 2 * (localResidual n d p.left : ℤ) *
          (localResidual n d p.right : ℤ) *
          threeBucketThirdObstruction
            (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
            a b c g (fifthPositionDeltaLeft p)
            (fifthPositionDeltaRight p) d := by
    rw [hzD, hQjNat, hRlNat]
    push_cast
    rw [hdecompInt]
    ring
  have hgpos : 0 < g := by
    by_contra hnot
    have hg0 : g = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hdecomp, hg0] at hdTarget
    norm_num at hdTarget
  have hnonzero :=
    fifth_quotient_target_equation_fourth_and_normalized_nonzero
      hp hdTarget heq (g := (g : ℤ))
      (Y := (localResidual n d p.left : ℤ))
      (Z := (localResidual n d p.right : ℤ))
      (t := (a : ℤ) * b * c)
      (T := threeBucketThirdObstruction
        (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
        a b c g (fifthPositionDeltaLeft p) (fifthPositionDeltaRight p) d)
      (b := (b : ℤ)) (c := (c : ℤ)) (z := z)
      (P := (P : ℤ)) (M := (g * Q * R : ℕ)) (w := w) (N := N)
      (by exact_mod_cast hgpos.ne') hY hZ (by exact_mod_cast hPM) hproduct
      (by
        simp [threeBucketThirdObstruction, threeBucketSecondObstruction]
        ring)
      hopposite hw.symm rfl
  exact ⟨z, w, N, hzD, hw.symm, rfl, hNdiv, hnonzero⟩

/-- Instantiate the selected-three construction from the complete all-owner
certificate at any imported cyclic position.

Every bucket outside the selected owner/left/right triple is absorbed into
the displayed loss.  Consequently this theorem asserts neither the original
bounded-loss estimate nor that the support has only three nonunit buckets.
Those are deliberately left as the simultaneous global gap. -/
theorem allOwner_selected_three_fifth_quotient_configuration
    {p : FifthQuotientPosition}
    (hp : p ∈ fifthQuotientTargetPositions)
    {n d : ℕ}
    (hdTarget : 10 ^ 1000 ≤ d)
    (heq : blockProduct p.k (n + d) = 4 * blockProduct p.k n)
    (cert : AllOwnerAssemblyThirdNonzeroCertificate p.k n d) :
    ∃ g : ℕ, ∃ z w N : ℤ,
      threeBucketThirdObstruction
          (fifthPositionC p) (fifthPositionD p) (fifthPositionE p)
          (allOwnerCofactor p.k n d cert.base.owner p.owner)
          (allOwnerCofactor p.k n d cert.base.owner p.left)
          (allOwnerCofactor p.k n d cert.base.owner p.right)
          g (fifthPositionDeltaLeft p)
          (fifthPositionDeltaRight p) d =
        (allOwnerBucket p.k d cert.base.owner p.owner : ℤ) ^ 2 * z ∧
      (allOwnerBucket p.k d cert.base.owner p.owner : ℤ) * w =
        27 * fifthPositionC p ^ 2 *
            (allOwnerCofactor p.k n d cert.base.owner p.left : ℤ) *
            (allOwnerCofactor p.k n d cert.base.owner p.right : ℤ) * z +
          fifthPositionK p * (g : ℤ) ^ 4 ∧
      N = 27 * w +
          (g *
            allOwnerBucket p.k d cert.base.owner p.left *
            allOwnerBucket p.k d cert.base.owner p.right : ℕ) *
            fifthPositionR1 p * (g : ℤ) ^ 4 ∧
      (allOwnerBucket p.k d cert.base.owner p.owner : ℤ) ∣ N ∧
      w ≠ 0 ∧ N ≠ 0 := by
  obtain ⟨hi, hj, hl, hij, hil, hjl⟩ :=
    fifth_quotient_target_position_full_metadata_certificate p hp
  have hk := (fifth_quotient_target_position_metadata_certificate p hp).1
  have hk5 : 5 ≤ p.k := by
    rcases hk with hk | hk | hk | hk | hk | hk <;> omega
  have hk15 : p.k ≤ 15 := by
    rcases hk with hk | hk | hk | hk | hk | hk <;> omega
  have h15Target : 15 ≤ 10 ^ 1000 := by
    exact le_trans (by norm_num : 15 ≤ 10 ^ 2)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hkd : p.k ≤ d :=
    le_trans hk15 (le_trans h15Target hdTarget)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hdTarget
  obtain ⟨g, hdecomp⟩ := allOwner_gap_decomposition_at_three
    hi hj hl hij hil hjl hd cert.base.assignment
  have hPi := allOwner_residual_cast cert.base.assignment
    (allOwner_residual_pos hk5 hkd hi heq)
  have hQj := allOwner_residual_cast cert.base.assignment
    (allOwner_residual_pos hk5 hkd hj heq)
  have hRl := allOwner_residual_cast cert.base.assignment
    (allOwner_residual_pos hk5 hkd hl heq)
  rcases direct_selected_three_fifth_quotient_configuration
      (p := p) hp hdTarget
      (allOwnerBucket_pos p.k d p.owner cert.base.owner)
      hdecomp
      (allOwnerBucket_dvd_factor cert.base.assignment)
      hPi hQj hRl heq with
    ⟨z, w, N, hz, hw, hN, hdiv, hw0, hN0⟩
  exact ⟨g, z, w, N, hz, hw, hN, hdiv, hw0, hN0⟩

#print axioms fifth_quotient_target_position_full_metadata_certificate
#print axioms allOwner_gap_decomposition_at_three
#print axioms localResidual_eq_of_signed_square
#print axioms direct_selected_three_fifth_quotient_configuration
#print axioms allOwner_selected_three_fifth_quotient_configuration

end Erdos686Variant
end Erdos686
