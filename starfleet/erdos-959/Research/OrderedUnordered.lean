import Research.FiniteConstruction

noncomputable section
namespace Erdos959

/-- Equivalence between a finite set subtype and its cardinal ordinal. -/
def finsetEquivFin (Y : Finset Point) : Y ≃ Fin Y.card :=
  (Fintype.equivFin Y).trans (finCongr (Fintype.card_coe Y))

/-- Canonical (choice-dependent) enumeration of a finite point set. -/
def enumerateFinset (Y : Finset Point) : Fin Y.card → Point := fun i =>
  ((finsetEquivFin Y).symm i).1

lemma enumerateFinset_injective (Y : Finset Point) :
    Function.Injective (enumerateFinset Y) := by
  intro i j h
  apply (finsetEquivFin Y).symm.injective
  apply Subtype.ext
  exact h

lemma enumerateFinset_mem (Y : Finset Point) (i : Fin Y.card) :
    enumerateFinset Y i ∈ Y := ((finsetEquivFin Y).symm i).2

lemma enumerateFinset_surjective_on (Y : Finset Point) {y : Point} (hy : y ∈ Y) :
    ∃ i : Fin Y.card, enumerateFinset Y i = y := by
  let yy : Y := ⟨y, hy⟩
  exact ⟨finsetEquivFin Y yy, by
    dsimp [enumerateFinset]
    simp [yy]⟩

/-- Ordered distinct index pairs at one squared distance. -/
def orderedIndexDistancePairs {n : ℕ} (P : Fin n → Point) (d : ℝ) :
    Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter fun ij =>
    ij.1 ≠ ij.2 ∧ sqDist (P ij.1) (P ij.2) = d

lemma orderedIndexDistancePairs_card_eq_twice_frequency
    {n : ℕ} (P : Fin n → Point) (d : ℝ) :
    (orderedIndexDistancePairs P d).card = 2 * frequency P d := by
  let F := (indexPairs n).filter fun ij => sqDist (P ij.1) (P ij.2) = d
  let swap : Fin n × Fin n → Fin n × Fin n := fun ij => (ij.2, ij.1)
  have hswap : Function.Injective swap := by
    intro ij kl h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hdecomp : orderedIndexDistancePairs P d = F ∪ F.image swap := by
    ext ij
    simp [orderedIndexDistancePairs, F, indexPairs]
    constructor
    · rintro ⟨hne, hd⟩
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact Or.inl ⟨hij, hd⟩
      · exact Or.inr ⟨ij.2, ij.1, ⟨hji, (sqDist_comm _ _).trans hd⟩, rfl⟩
    · rintro (hij | ⟨a, b, hab, hEq⟩)
      · exact ⟨ne_of_lt hij.1, hij.2⟩
      · subst ij
        exact ⟨ne_of_gt hab.1, (sqDist_comm _ _).trans hab.2⟩
  have hdisj : Disjoint F (F.image swap) := by
    rw [Finset.disjoint_left]
    intro ij hij hjs
    rcases Finset.mem_image.mp hjs with ⟨kl, hkl, hEq⟩
    have hij' : ij.1 < ij.2 ∧ sqDist (P ij.1) (P ij.2) = d := by
      simpa [F, indexPairs] using hij
    have hkl' : kl.1 < kl.2 ∧ sqDist (P kl.1) (P kl.2) = d := by
      simpa [F, indexPairs] using hkl
    have heq1 : kl.2 = ij.1 := congrArg Prod.fst hEq
    have heq2 : kl.1 = ij.2 := congrArg Prod.snd hEq
    rw [← heq1, ← heq2] at hij'
    exact lt_asymm hkl'.1 hij'.1
  rw [hdecomp, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hswap]
  change F.card + F.card = 2 * frequency P d
  dsimp [F, frequency]
  omega

lemma orderedRealDistancePairs_enumeration_card
    (Y : Finset Point) (d : ℝ) :
    (orderedRealDistancePairs Y d).card =
      (orderedIndexDistancePairs (enumerateFinset Y) d).card := by
  let f : Fin Y.card × Fin Y.card → Point × Point := fun ij =>
    (enumerateFinset Y ij.1, enumerateFinset Y ij.2)
  have hf : Function.Injective f := by
    intro ij kl h
    exact Prod.ext (enumerateFinset_injective Y (congrArg Prod.fst h))
      (enumerateFinset_injective Y (congrArg Prod.snd h))
  let I := (orderedIndexDistancePairs (enumerateFinset Y) d).image f
  have hcard : I.card =
      (orderedIndexDistancePairs (enumerateFinset Y) d).card :=
    Finset.card_image_of_injective _ hf
  have hI : I = orderedRealDistancePairs Y d := by
    ext xy
    constructor
    · intro hxy
      rcases Finset.mem_image.mp hxy with ⟨ij, hij, rfl⟩
      have hm := Finset.mem_filter.mp hij
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨enumerateFinset_mem Y ij.1, enumerateFinset_mem Y ij.2⟩,
        fun heq => hm.2.1 (enumerateFinset_injective Y heq), hm.2.2⟩
    · intro hxy
      have hm := Finset.mem_filter.mp hxy
      have hp := Finset.mem_product.mp hm.1
      obtain ⟨i, hi⟩ := enumerateFinset_surjective_on Y hp.1
      obtain ⟨j, hj⟩ := enumerateFinset_surjective_on Y hp.2
      apply Finset.mem_image.mpr
      refine ⟨(i, j), ?_, Prod.ext hi hj⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        by
          intro hij
          change i = j at hij
          apply hm.2.1
          rw [← hi, ← hj, hij], by rw [hi, hj]; exact hm.2.2⟩
  rw [← hI, hcard]

/-- Ordered real frequency is exactly twice the problem's unordered frequency. -/
lemma orderedRealDistancePairs_card_eq_twice_frequency
    (Y : Finset Point) (d : ℝ) :
    (orderedRealDistancePairs Y d).card =
      2 * frequency (enumerateFinset Y) d := by
  rw [orderedRealDistancePairs_enumeration_card,
    orderedIndexDistancePairs_card_eq_twice_frequency]

lemma distanceValues_enumerateFinset (Y : Finset Point) :
    distanceValues (enumerateFinset Y) = pointDistanceSpectrum Y := by
  ext d
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨ij, hij, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(enumerateFinset Y ij.1, enumerateFinset Y ij.2), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    have hlt := (Finset.mem_filter.mp hij).2
    exact ⟨Finset.mem_product.mpr
      ⟨enumerateFinset_mem Y ij.1, enumerateFinset_mem Y ij.2⟩,
      fun heq => (ne_of_lt hlt) (enumerateFinset_injective Y heq)⟩
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨xy, hxy, rfl⟩
    have hm := Finset.mem_filter.mp hxy
    have hp := Finset.mem_product.mp hm.1
    obtain ⟨i, hi⟩ := enumerateFinset_surjective_on Y hp.1
    obtain ⟨j, hj⟩ := enumerateFinset_surjective_on Y hp.2
    have hij : i ≠ j := by
      intro heq
      apply hm.2
      rw [← hi, ← hj, heq]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · apply Finset.mem_image.mpr
      refine ⟨(i, j), ?_, by rw [hi, hj]⟩
      simp [indexPairs, hlt]
    · apply Finset.mem_image.mpr
      refine ⟨(j, i), ?_, ?_⟩
      · simp [indexPairs, hgt]
      · rw [hi, hj, sqDist_comm]

end Erdos959
