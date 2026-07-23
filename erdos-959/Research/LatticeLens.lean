import Research.DiskGeometry

noncomputable section
namespace Erdos959

lemma int_round_half (a : ℤ) :
    |((-(a / 2) : ℤ) : ℝ) + (a : ℝ) / 2| ≤ (1 : ℝ) / 2 := by
  have hdecomp : (2 : ℤ) * (a / 2) + a % 2 = a := Int.ediv_add_emod a 2
  have hnonneg : (0 : ℤ) ≤ a % 2 := Int.emod_nonneg a (by norm_num)
  have hlt : a % 2 < (2 : ℤ) := by simpa using Int.emod_lt a (by norm_num : (2 : ℤ) ≠ 0)
  have hdecompR : (2 : ℝ) * ((a / 2 : ℤ) : ℝ) + ((a % 2 : ℤ) : ℝ) = (a : ℝ) := by
    exact_mod_cast hdecomp
  have hnonnegR : (0 : ℝ) ≤ ((a % 2 : ℤ) : ℝ) := by exact_mod_cast hnonneg
  have hle : a % 2 ≤ (1 : ℤ) := by omega
  have hleR : ((a % 2 : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hle
  rw [abs_le]
  push_cast
  constructor <;> nlinarith

lemma centered_integer_offset_bound (a z : ℤ) (m : ℕ)
    (hz : z ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)) :
    |((-(a / 2) + z : ℤ) : ℝ) + (a : ℝ) / 2| ≤ (m : ℝ) + 1 / 2 := by
  simp only [Finset.mem_Icc] at hz
  have hr := int_round_half a
  have hzRlo : -(m : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz.1
  have hzRhi : (z : ℝ) ≤ (m : ℝ) := by exact_mod_cast hz.2
  rw [abs_le] at hr ⊢
  push_cast at hr ⊢
  constructor <;> nlinarith [hr.1, hr.2]

lemma card_int_symmetric_Icc (m : ℕ) :
    (Finset.Icc (-(m : ℤ)) (m : ℤ)).card = 2 * m + 1 := by
  rw [Int.card_Icc]
  have hnonneg : (0 : ℤ) ≤ 2 * (m : ℤ) + 1 := by positivity
  have htoNat := Int.toNat_of_nonneg hnonneg
  rw [show (m : ℤ) + 1 - -(m : ℤ) = 2 * (m : ℤ) + 1 by ring]
  exact_mod_cast htoNat

lemma card_int_symmetric_box (m : ℕ) :
    ((Finset.Icc (-(m : ℤ)) (m : ℤ)).product
      (Finset.Icc (-(m : ℤ)) (m : ℤ))).card = (2 * m + 1) ^ 2 := by
  let s : Finset ℤ := Finset.Icc (-(m : ℤ)) (m : ℤ)
  change (s.product s).card = (2 * m + 1) ^ 2
  rw [show (s.product s).card = s.card * s.card from Finset.card_product s s]
  rw [show s.card = 2 * m + 1 by exact card_int_symmetric_Icc m]
  ring

lemma radius_div_sixteen_bounds (R : ℕ) (hR : 32 ≤ R) :
    let m := R / 16
    (m : ℝ) + 1 / 2 ≤ (R : ℝ) / 8 ∧
      R ^ 2 ≤ 256 * (2 * m + 1) ^ 2 := by
  let m := R / 16
  have hm : 2 ≤ m := by
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).2 (by simpa [m] using hR)
  have hlower : 16 * m ≤ R := by
    dsimp [m]
    exact Nat.mul_div_le R 16
  have hmod : R % 16 < 16 := Nat.mod_lt R (by norm_num)
  have hdecomp : 16 * m + R % 16 = R := by
    dsimp [m]
    exact Nat.div_add_mod R 16
  constructor
  · change (m : ℝ) + 1 / 2 ≤ (R : ℝ) / 8
    have hnat : 8 * m + 4 ≤ R := by omega
    have hreal : (8 * m + 4 : ℝ) ≤ R := by exact_mod_cast hnat
    push_cast at hreal
    nlinarith
  · change R ^ 2 ≤ 256 * (2 * m + 1) ^ 2
    have hRupper : R ≤ 32 * m := by omega
    have hside : R ≤ 16 * (2 * m + 1) := by omega
    calc
      R ^ 2 ≤ (16 * (2 * m + 1)) ^ 2 := Nat.pow_le_pow_left hside 2
      _ = 256 * (2 * m + 1) ^ 2 := by ring


abbrev IntPoint := ℤ × ℤ

def intPointToReal (x : IntPoint) : Point := ((x.1 : ℝ), (x.2 : ℝ))

def startFromOffset (v z : IntPoint) : IntPoint :=
  (-(v.1 / 2) + z.1, -(v.2 / 2) + z.2)

lemma startFromOffset_injective (v : IntPoint) :
    Function.Injective (startFromOffset v) := by
  intro z z' h
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    dsimp [startFromOffset] at h1 ⊢
    omega
  · have h2 := congrArg Prod.snd h
    dsimp [startFromOffset] at h2 ⊢
    omega

def offsetBox (R : ℕ) : Finset IntPoint :=
  let m : ℕ := R / 16
  (Finset.Icc (-(m : ℤ)) (m : ℤ)).product
    (Finset.Icc (-(m : ℤ)) (m : ℤ))

def lensStarts (v : IntPoint) (R : ℕ) : Finset IntPoint :=
  (offsetBox R).image (startFromOffset v)

lemma card_offsetBox (R : ℕ) :
    (offsetBox R).card = (2 * (R / 16) + 1) ^ 2 := by
  exact card_int_symmetric_box (R / 16)

lemma card_lensStarts (v : IntPoint) (R : ℕ) :
    (lensStarts v R).card = (2 * (R / 16) + 1) ^ 2 := by
  rw [lensStarts, Finset.card_image_of_injective _ (startFromOffset_injective v)]
  exact card_offsetBox R

lemma lensStarts_card_lower (v : IntPoint) (R : ℕ) (hR : 32 ≤ R) :
    R ^ 2 ≤ 256 * (lensStarts v R).card := by
  rw [card_lensStarts]
  exact (radius_div_sixteen_bounds R hR).2

lemma offset_midpoint_in_eighth_box
    (v z : IntPoint) (R : ℕ) (hR : 32 ≤ R) (hz : z ∈ offsetBox R) :
    |((startFromOffset v z).1 : ℝ) + (v.1 : ℝ) / 2| ≤ (R : ℝ) / 8 ∧
    |((startFromOffset v z).2 : ℝ) + (v.2 : ℝ) / 2| ≤ (R : ℝ) / 8 := by
  dsimp [offsetBox] at hz
  simp only [Finset.mem_product, Finset.mem_Icc] at hz
  have hb := (radius_div_sixteen_bounds R hR).1
  constructor
  · apply (centered_integer_offset_bound v.1 z.1 (R / 16) (by
      simpa [Finset.mem_Icc] using hz.1)).trans hb
  · apply (centered_integer_offset_bound v.2 z.2 (R / 16) (by
      simpa [Finset.mem_Icc] using hz.2)).trans hb

lemma offset_gives_disk_pair
    (v z : IntPoint) (R : ℕ) (hR : 32 ≤ R) (hz : z ∈ offsetBox R)
    (hv : normSq (intPointToReal v) ≤ (3 * (R : ℝ) / 2) ^ 2) :
    normSq (intPointToReal (startFromOffset v z)) ≤ (R : ℝ) ^ 2 ∧
    normSq (intPointToReal (startFromOffset v z + v)) ≤ (R : ℝ) ^ 2 := by
  let x := startFromOffset v z
  let w : Point := ((x.1 : ℝ) + (v.1 : ℝ) / 2,
    (x.2 : ℝ) + (v.2 : ℝ) / 2)
  have hbox := offset_midpoint_in_eighth_box v z R hR hz
  have hw : normSq w ≤ ((R : ℝ) / 4) ^ 2 := by
    exact eighth_box_subset_quarter_disk w R (by positivity) hbox.1 hbox.2
  have hlens := lens_contains_quarter_disk w (intPointToReal v) R hw hv
  dsimp [w, x, intPointToReal, startFromOffset] at hlens ⊢
  push_cast at hlens ⊢
  constructor
  · convert hlens.1 using 1 <;> dsimp [normSq] <;> ring
  · convert hlens.2 using 1 <;> dsimp [normSq] <;> ring

lemma sqDist_int_translate (x v : IntPoint) :
    sqDist (intPointToReal x) (intPointToReal (x + v)) =
      normSq (intPointToReal v) := by
  dsimp [sqDist, normSq, intPointToReal]
  push_cast
  ring

lemma lensStarts_give_target_pairs
    (v x : IntPoint) (R : ℕ) (hR : 32 ≤ R) (hx : x ∈ lensStarts v R)
    (hv : normSq (intPointToReal v) ≤ (3 * (R : ℝ) / 2) ^ 2) :
    normSq (intPointToReal x) ≤ (R : ℝ) ^ 2 ∧
    normSq (intPointToReal (x + v)) ≤ (R : ℝ) ^ 2 ∧
    sqDist (intPointToReal x) (intPointToReal (x + v)) =
      normSq (intPointToReal v) := by
  rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
  have hd := offset_gives_disk_pair v z R hR hz hv
  exact ⟨hd.1, hd.2, sqDist_int_translate _ _⟩

/-- The finite integer lattice disk of radius `R`. -/
def latticeDisk (R : ℕ) : Finset IntPoint :=
  ((Finset.Icc (-(R : ℤ)) (R : ℤ)).product
    (Finset.Icc (-(R : ℤ)) (R : ℤ))).filter fun x =>
      x.1 ^ 2 + x.2 ^ 2 ≤ (R : ℤ) ^ 2

lemma mem_latticeDisk_iff (x : IntPoint) (R : ℕ) :
    x ∈ latticeDisk R ↔ normSq (intPointToReal x) ≤ (R : ℝ) ^ 2 := by
  constructor
  · intro h
    have hi := (Finset.mem_filter.mp h).2
    dsimp [normSq, intPointToReal]
    exact_mod_cast hi
  · intro h
    have hi : x.1 ^ 2 + x.2 ^ 2 ≤ (R : ℤ) ^ 2 := by
      dsimp [normSq, intPointToReal] at h
      exact_mod_cast h
    have hxSq : x.1 ^ 2 ≤ (R : ℤ) ^ 2 := le_trans (by nlinarith [sq_nonneg x.2]) hi
    have hySq : x.2 ^ 2 ≤ (R : ℤ) ^ 2 := le_trans (by nlinarith [sq_nonneg x.1]) hi
    have hR : (0 : ℤ) ≤ R := by positivity
    have hxAbs : |x.1| ≤ |(R : ℤ)| := sq_le_sq.mp hxSq
    have hyAbs : |x.2| ≤ |(R : ℤ)| := sq_le_sq.mp hySq
    rw [abs_of_nonneg hR] at hxAbs hyAbs
    have hx : -(R : ℤ) ≤ x.1 ∧ x.1 ≤ R := abs_le.mp hxAbs
    have hy : -(R : ℤ) ≤ x.2 ∧ x.2 ≤ R := abs_le.mp hyAbs
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hx,
      Finset.mem_Icc.mpr hy⟩, hi⟩

lemma lensStarts_subset_latticeDisk
    (v : IntPoint) (R : ℕ) (hR : 32 ≤ R)
    (hv : normSq (intPointToReal v) ≤ (3 * (R : ℝ) / 2) ^ 2) :
    lensStarts v R ⊆ latticeDisk R := by
  intro x hx
  rw [mem_latticeDisk_iff]
  exact (lensStarts_give_target_pairs v x R hR hx hv).1

lemma latticeDisk_card_lower (R : ℕ) (hR : 32 ≤ R) :
    R ^ 2 ≤ 256 * (latticeDisk R).card := by
  have hzero : normSq (intPointToReal (0, 0)) ≤ (3 * (R : ℝ) / 2) ^ 2 := by
    dsimp [normSq, intPointToReal]
    nlinarith [sq_nonneg (3 * (R : ℝ) / 2)]
  have hcard : (lensStarts (0, 0) R).card ≤ (latticeDisk R).card :=
    Finset.card_le_card (lensStarts_subset_latticeDisk (0, 0) R hR hzero)
  exact (lensStarts_card_lower (0, 0) R hR).trans
    (Nat.mul_le_mul_left 256 hcard)

lemma latticeDisk_card_upper (R : ℕ) :
    (latticeDisk R).card ≤ (2 * R + 1) ^ 2 := by
  have hsub : latticeDisk R ⊆
      (Finset.Icc (-(R : ℤ)) (R : ℤ)).product
        (Finset.Icc (-(R : ℤ)) (R : ℤ)) := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  calc
    (latticeDisk R).card ≤
        ((Finset.Icc (-(R : ℤ)) (R : ℤ)).product
          (Finset.Icc (-(R : ℤ)) (R : ℤ))).card := Finset.card_le_card hsub
    _ = (2 * R + 1) ^ 2 := card_int_symmetric_box R

end Erdos959
