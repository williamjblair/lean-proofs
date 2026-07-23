import Research.LatticeLens

noncomputable section
namespace Erdos959

/-- Squared norm of an integer vector, retained in `ℤ` for exact arithmetic. -/
def intNormSq (v : IntPoint) : ℤ := v.1 ^ 2 + v.2 ^ 2

/-- All oriented integer representation vectors for a positive integer `t`. -/
def representationVectors (t : ℕ) : Finset IntPoint :=
  ((Finset.Icc (-(t : ℤ)) (t : ℤ)).product
    (Finset.Icc (-(t : ℤ)) (t : ℤ))).filter fun v => intNormSq v = t

lemma mem_representationVectors_iff {t : ℕ} (ht : 1 ≤ t) (v : IntPoint) :
    v ∈ representationVectors t ↔ intNormSq v = t := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hv
    have hxSq : v.1 ^ 2 ≤ (t : ℤ) := by
      dsimp [intNormSq] at hv
      nlinarith [sq_nonneg v.2]
    have hySq : v.2 ^ 2 ≤ (t : ℤ) := by
      dsimp [intNormSq] at hv
      nlinarith [sq_nonneg v.1]
    have htSqNat : t ≤ t ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul_left t ht
    have htSq : (t : ℤ) ≤ (t : ℤ) ^ 2 := by exact_mod_cast htSqNat
    have hxAbs : |v.1| ≤ |(t : ℤ)| := sq_le_sq.mp (hxSq.trans htSq)
    have hyAbs : |v.2| ≤ |(t : ℤ)| := sq_le_sq.mp (hySq.trans htSq)
    have ht0 : (0 : ℤ) ≤ t := by positivity
    rw [abs_of_nonneg ht0] at hxAbs hyAbs
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp hxAbs),
      Finset.mem_Icc.mpr (abs_le.mp hyAbs)⟩, hv⟩

lemma representationVector_real_norm {t : ℕ} (ht : 1 ≤ t)
    {v : IntPoint} (hv : v ∈ representationVectors t) :
    normSq (intPointToReal v) = t := by
  have hi := (mem_representationVectors_iff ht v).mp hv
  dsimp [normSq, intPointToReal, intNormSq] at hi ⊢
  exact_mod_cast hi

/-- Ordered pairs in `X` at positive integer squared distance `t`. -/
def orderedDistancePairs (X : Finset IntPoint) (t : ℕ) : Finset (IntPoint × IntPoint) :=
  (X.product X).filter fun xy =>
    xy.1 ≠ xy.2 ∧ intNormSq (xy.2 - xy.1) = t

lemma mem_orderedDistancePairs_iff {X : Finset IntPoint} {t : ℕ}
    (x y : IntPoint) :
    (x, y) ∈ orderedDistancePairs X t ↔
      x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ intNormSq (y - x) = t := by
  rw [orderedDistancePairs, Finset.mem_filter]
  rw [show (x, y) ∈ X.product X ↔ x ∈ X ∧ y ∈ X from Finset.mem_product]
  tauto

/-- Encode an ordered pair by its first endpoint and displacement. -/
def encodeOrderedPair (xy : IntPoint × IntPoint) : IntPoint × IntPoint :=
  (xy.1, xy.2 - xy.1)

lemma encodeOrderedPair_injective : Function.Injective encodeOrderedPair := by
  intro xy uv h
  apply Prod.ext
  · exact congrArg (fun q => q.1) h
  · have hfirst : xy.1 = uv.1 := congrArg (fun q => q.1) h
    have hdiff : xy.2 - xy.1 = uv.2 - uv.1 := congrArg (fun q => q.2) h
    rw [hfirst] at hdiff
    exact sub_left_inj.mp hdiff

lemma orderedDistancePairs_upper (X : Finset IntPoint) (t : ℕ) (ht : 1 ≤ t) :
    (orderedDistancePairs X t).card ≤ X.card * (representationVectors t).card := by
  let E := (orderedDistancePairs X t).image encodeOrderedPair
  have hcard : E.card = (orderedDistancePairs X t).card := by
    exact Finset.card_image_of_injective _ encodeOrderedPair_injective
  have hsub : E ⊆ X.product (representationVectors t) := by
    intro xv hxv
    rcases Finset.mem_image.mp hxv with ⟨xy, hxy, rfl⟩
    have hm := (mem_orderedDistancePairs_iff xy.1 xy.2).mp hxy
    apply Finset.mem_product.mpr
    exact ⟨hm.1, (mem_representationVectors_iff ht _).mpr hm.2.2.2⟩
  rw [← hcard, ← Finset.card_product]
  exact Finset.card_le_card hsub

/-- The source data used to manufacture target ordered pairs. -/
def targetPairData (s R : ℕ) : Finset (IntPoint × IntPoint) :=
  (representationVectors s).product (offsetBox R)

/-- Map a representation vector and a midpoint-box offset to its disk pair. -/
def targetPairMap (vz : IntPoint × IntPoint) : IntPoint × IntPoint :=
  let v := vz.1
  let x := startFromOffset v vz.2
  (x, x + v)

lemma targetPairMap_injective : Function.Injective targetPairMap := by
  intro vz wz h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [targetPairMap] at hx hy
  have hv : vz.1 = wz.1 := by
    rw [hx] at hy
    exact add_left_cancel hy
  apply Prod.ext
  · exact hv
  · have hx' : startFromOffset vz.1 vz.2 = startFromOffset vz.1 wz.2 := by
      simpa [hv] using hx
    exact startFromOffset_injective vz.1 hx'

lemma targetPairMap_mem_ordered
    (s R : ℕ) (hs : 1 ≤ s) (hR : 32 ≤ R)
    (hshort : (s : ℝ) ≤ (3 * (R : ℝ) / 2) ^ 2)
    {vz : IntPoint × IntPoint} (hvz : vz ∈ targetPairData s R) :
    targetPairMap vz ∈ orderedDistancePairs (latticeDisk R) s := by
  have hvz' := Finset.mem_product.mp hvz
  let v := vz.1
  let z := vz.2
  let x := startFromOffset v z
  have hvnorm : normSq (intPointToReal v) = s :=
    representationVector_real_norm hs hvz'.1
  have hdisk := offset_gives_disk_pair v z R hR hvz'.2 (hvnorm.trans_le hshort)
  apply (mem_orderedDistancePairs_iff x (x + v)).mpr
  have hxmem : x ∈ latticeDisk R := (mem_latticeDisk_iff x R).mpr hdisk.1
  have hymem : x + v ∈ latticeDisk R := (mem_latticeDisk_iff (x + v) R).mpr hdisk.2
  have hvne : v ≠ 0 := by
    intro hv0
    have hs0R : (s : ℝ) = 0 := by
      rw [← hvnorm, hv0]
      norm_num [normSq, intPointToReal]
    have hs0 : s = 0 := by exact_mod_cast hs0R
    omega
  have hxy : x ≠ x + v := by
    intro heq
    apply hvne
    have heq' : x + v = x + 0 := by simpa using heq.symm
    exact add_left_cancel heq'
  have hdiff : intNormSq (x + v - x) = s := by
    rw [add_sub_cancel_left]
    exact (mem_representationVectors_iff hs v).mp hvz'.1
  exact ⟨hxmem, hymem, hxy, hdiff⟩

lemma target_ordered_pairs_lower
    (s R : ℕ) (hs : 1 ≤ s) (hR : 32 ≤ R)
    (hshort : (s : ℝ) ≤ (3 * (R : ℝ) / 2) ^ 2) :
    (representationVectors s).card * R ^ 2 ≤
      256 * (orderedDistancePairs (latticeDisk R) s).card := by
  let I := (targetPairData s R).image targetPairMap
  have hIcard : I.card = (targetPairData s R).card :=
    Finset.card_image_of_injective _ targetPairMap_injective
  have hIsub : I ⊆ orderedDistancePairs (latticeDisk R) s := by
    intro xy hxy
    rcases Finset.mem_image.mp hxy with ⟨vz, hvz, rfl⟩
    exact targetPairMap_mem_ordered s R hs hR hshort hvz
  have hsource : (targetPairData s R).card =
      (representationVectors s).card * (offsetBox R).card := by
    exact Finset.card_product _ _
  have hbox : R ^ 2 ≤ 256 * (offsetBox R).card := by
    rw [card_offsetBox]
    exact (radius_div_sixteen_bounds R hR).2
  calc
    (representationVectors s).card * R ^ 2 ≤
        (representationVectors s).card * (256 * (offsetBox R).card) :=
          Nat.mul_le_mul_left _ hbox
    _ = 256 * (targetPairData s R).card := by rw [hsource]; ring
    _ = 256 * I.card := by rw [hIcard]
    _ ≤ 256 * (orderedDistancePairs (latticeDisk R) s).card :=
      Nat.mul_le_mul_left 256 (Finset.card_le_card hIsub)

end Erdos959
