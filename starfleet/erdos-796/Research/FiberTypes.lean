import Research.LiftConstruction

namespace Erdos796

/-- Ordered cross-representation count between two finite core types. -/
def crossRepCount (S T : Finset ℕ) (m : ℕ) : ℕ :=
  ((S ×ˢ T).filter fun z => z.1 * z.2 = m).card

/-- Maximum ordered product multiplicity between two finite core types. -/
def crossMultiplicity (S T : Finset ℕ) : ℕ :=
  (((S ×ˢ T).image fun z => z.1 * z.2).sup fun m => crossRepCount S T m)

/-- Pairwise compatibility required of fibers attached to distinct prime
labels. -/
abbrev CrossCompatible (S T : Finset ℕ) : Prop :=
  crossMultiplicity S T ≤ 2

/-- Compatibility bounds every ordered representation count, including
products absent from the finite product image. -/
theorem crossRepCount_le_two_of_compatible
    {S T : Finset ℕ} (h : CrossCompatible S T) (m : ℕ) :
    crossRepCount S T m ≤ 2 := by
  by_cases hm : m ∈ (S ×ˢ T).image fun z => z.1 * z.2
  · exact le_trans (Finset.le_sup hm) h
  · have hempty : ((S ×ˢ T).filter fun z => z.1 * z.2 = m) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨z, hz⟩
      have hz' := Finset.mem_filter.mp hz
      exact hm (Finset.mem_image.mpr ⟨z, hz'.1, hz'.2⟩)
    simp [crossRepCount, hempty]

/-- A positive factor at most a threshold. -/
abbrev SmallFactor (R x : ℕ) : Prop := 0 < x ∧ x ≤ R

/-- A prime factor strictly above a threshold. -/
abbrev LargePrimeFactor (R x : ℕ) : Prop := R < x ∧ x.Prime

/-- Unique factorization across a fixed small/large-prime threshold.  Unless
both products use only small factors, the two unordered factor pairs agree. -/
theorem small_large_product_classification
    {R a b c d : ℕ}
    (ha : SmallFactor R a ∨ LargePrimeFactor R a)
    (hb : SmallFactor R b ∨ LargePrimeFactor R b)
    (hc : SmallFactor R c ∨ LargePrimeFactor R c)
    (hd : SmallFactor R d ∨ LargePrimeFactor R d)
    (heq : a * b = c * d) :
    ((SmallFactor R a ∧ SmallFactor R b) ∧
      (SmallFactor R c ∧ SmallFactor R d)) ∨
      ({a, b} : Finset ℕ) = {c, d} := by
  rcases ha with haS | haL
  · rcases hb with hbS | hbL
    · rcases hc with hcS | hcL
      · rcases hd with hdS | hdL
        · exact Or.inl ⟨⟨haS, hbS⟩, ⟨hcS, hdS⟩⟩
        · have hdiv : d ∣ a * b := by
            rw [heq]
            simpa [Nat.mul_comm] using Nat.dvd_mul_right d c
          rcases hdL.2.dvd_mul.mp hdiv with hda | hdb
          · exact (large_prime_not_dvd_core hdL.1 haS.1 haS.2 hda).elim
          · exact (large_prime_not_dvd_core hdL.1 hbS.1 hbS.2 hdb).elim
      · rcases hd with hdS | hdL
        · have hdiv : c ∣ a * b := by
            rw [heq]
            exact Nat.dvd_mul_right c d
          rcases hcL.2.dvd_mul.mp hdiv with hca | hcb
          · exact (large_prime_not_dvd_core hcL.1 haS.1 haS.2 hca).elim
          · exact (large_prime_not_dvd_core hcL.1 hbS.1 hbS.2 hcb).elim
        · have hdiv : c ∣ a * b := by
            rw [heq]
            exact Nat.dvd_mul_right c d
          rcases hcL.2.dvd_mul.mp hdiv with hca | hcb
          · exact (large_prime_not_dvd_core hcL.1 haS.1 haS.2 hca).elim
          · exact (large_prime_not_dvd_core hcL.1 hbS.1 hbS.2 hcb).elim
    · rcases hc with hcS | hcL
      · rcases hd with hdS | hdL
        · have hdiv : b ∣ c * d := by
            rw [← heq]
            simpa [Nat.mul_comm] using Nat.dvd_mul_right b a
          rcases hbL.2.dvd_mul.mp hdiv with hbc | hbd
          · exact (large_prime_not_dvd_core hbL.1 hcS.1 hcS.2 hbc).elim
          · exact (large_prime_not_dvd_core hbL.1 hdS.1 hdS.2 hbd).elim
        · have huniq := large_prime_core_decomposition_unique (x := a) (y := c)
            hbL.1 hdL.1 hbL.2 hdL.2 hcS.1 hcS.2 (by
              simpa [Nat.mul_comm] using heq)
          right
          rcases huniq with ⟨rfl, rfl⟩
          rfl
      · rcases hd with hdS | hdL
        · have huniq := large_prime_core_decomposition_unique (x := a) (y := d)
            hbL.1 hcL.1 hbL.2 hcL.2 hdS.1 hdS.2 (by
              simpa [Nat.mul_comm] using heq)
          right
          rcases huniq with ⟨rfl, rfl⟩
          ext z
          simp [or_comm]
        · have hdiv : b ∣ c * d := by
            rw [← heq]
            simpa [Nat.mul_comm] using Nat.dvd_mul_right b a
          rcases hbL.2.dvd_mul.mp hdiv with hbc | hbd
          · have hbc' : b = c := by
              rcases (Nat.dvd_prime hcL.2).mp hbc with h1 | h
              · exact (hbL.2.ne_one h1).elim
              · exact h
            subst c
            have had : a = d := by
              apply Nat.mul_right_cancel hbL.2.pos
              simpa [Nat.mul_comm] using heq
            exact (not_le_of_gt hdL.1 (had ▸ haS.2)).elim
          · have hbd' : b = d := by
              rcases (Nat.dvd_prime hdL.2).mp hbd with h1 | h
              · exact (hbL.2.ne_one h1).elim
              · exact h
            subst d
            have hac : a = c := Nat.mul_right_cancel hbL.2.pos heq
            exact (not_le_of_gt hcL.1 (hac ▸ haS.2)).elim
  · rcases hb with hbS | hbL
    · rcases hc with hcS | hcL
      · rcases hd with hdS | hdL
        · have hdiv : a ∣ c * d := by rw [← heq]; exact Nat.dvd_mul_right a b
          rcases haL.2.dvd_mul.mp hdiv with hac | had
          · exact (large_prime_not_dvd_core haL.1 hcS.1 hcS.2 hac).elim
          · exact (large_prime_not_dvd_core haL.1 hdS.1 hdS.2 had).elim
        · have huniq := large_prime_core_decomposition_unique (x := b) (y := c)
            haL.1 hdL.1 haL.2 hdL.2 hcS.1 hcS.2 (by
              simpa [Nat.mul_comm] using heq)
          right
          rcases huniq with ⟨rfl, rfl⟩
          ext z
          simp [or_comm]
      · rcases hd with hdS | hdL
        · have huniq := large_prime_core_decomposition_unique (x := b) (y := d)
            haL.1 hcL.1 haL.2 hcL.2 hdS.1 hdS.2 heq
          right
          rcases huniq with ⟨rfl, rfl⟩
          rfl
        · have hdiv : a ∣ c * d := by rw [← heq]; exact Nat.dvd_mul_right a b
          rcases haL.2.dvd_mul.mp hdiv with hac | had
          · have hac' : a = c := by
              rcases (Nat.dvd_prime hcL.2).mp hac with h1 | h
              · exact (haL.2.ne_one h1).elim
              · exact h
            subst c
            have hbd : b = d := Nat.mul_left_cancel haL.2.pos heq
            exact (not_le_of_gt hdL.1 (hbd ▸ hbS.2)).elim
          · have had' : a = d := by
              rcases (Nat.dvd_prime hdL.2).mp had with h1 | h
              · exact (haL.2.ne_one h1).elim
              · exact h
            subst d
            have hbc : b = c := by
              apply Nat.mul_left_cancel haL.2.pos
              simpa [Nat.mul_comm] using heq
            exact (not_le_of_gt hcL.1 (hbc ▸ hbS.2)).elim
    · rcases hc with hcS | hcL
      · rcases hd with hdS | hdL
        · have hdiv : a ∣ c * d := by rw [← heq]; exact Nat.dvd_mul_right a b
          rcases haL.2.dvd_mul.mp hdiv with hac | had
          · exact (large_prime_not_dvd_core haL.1 hcS.1 hcS.2 hac).elim
          · exact (large_prime_not_dvd_core haL.1 hdS.1 hdS.2 had).elim
        · have hdiv : a ∣ c * d := by rw [← heq]; exact Nat.dvd_mul_right a b
          rcases haL.2.dvd_mul.mp hdiv with hac | had
          · exact (large_prime_not_dvd_core haL.1 hcS.1 hcS.2 hac).elim
          · have had' : a = d := by
              rcases (Nat.dvd_prime hdL.2).mp had with h1 | h
              · exact (haL.2.ne_one h1).elim
              · exact h
            subst d
            have hbc : b = c := by
              apply Nat.mul_right_cancel haL.2.pos
              simpa [Nat.mul_comm] using heq
            exact (not_le_of_gt hbL.1 (hbc ▸ hcS.2)).elim
      · rcases hd with hdS | hdL
        · have hdiv : a ∣ c * d := by rw [← heq]; exact Nat.dvd_mul_right a b
          rcases haL.2.dvd_mul.mp hdiv with hac | had
          · have hac' : a = c := by
              rcases (Nat.dvd_prime hcL.2).mp hac with h1 | h
              · exact (haL.2.ne_one h1).elim
              · exact h
            subst c
            have hbd : b = d := Nat.mul_left_cancel haL.2.pos heq
            exact (not_le_of_gt hbL.1 (hbd ▸ hdS.2)).elim
          · exact (large_prime_not_dvd_core haL.1 hdS.1 hdS.2 had).elim
        · have hdiv : a ∣ c * d := by rw [← heq]; exact Nat.dvd_mul_right a b
          rcases haL.2.dvd_mul.mp hdiv with hac | had
          · have hac' : a = c := by
              rcases (Nat.dvd_prime hcL.2).mp hac with h1 | h
              · exact (haL.2.ne_one h1).elim
              · exact h
            subst c
            have hbd : b = d := Nat.mul_left_cancel haL.2.pos heq
            subst d
            exact Or.inr rfl
          · have had' : a = d := by
              rcases (Nat.dvd_prime hdL.2).mp had with h1 | h
              · exact (haL.2.ne_one h1).elim
              · exact h
            subst d
            have hbc : b = c := by
              apply Nat.mul_left_cancel haL.2.pos
              simpa [Nat.mul_comm] using heq
            subst c
            right
            ext z
            simp [or_comm]

/-- Extend a bounded core type by all primes above its cutoff through a
possibly larger capacity. -/
def primeExtendType (R J : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S ∪ (Finset.Icc (R + 1) J).filter Nat.Prime

/-- Pairwise compatibility survives independently truncating the common tail
of primes above the old cutoff. -/
theorem primeExtendType_crossCompatible
    (R J L : ℕ) (S T : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 R) (hT : T ⊆ Finset.Icc 1 R)
    (hcompat : CrossCompatible S T) :
    CrossCompatible (primeExtendType R J S) (primeExtendType R L T) := by
  apply Finset.sup_le
  intro m hm
  let U := primeExtendType R J S
  let V := primeExtendType R L T
  let P := (U ×ˢ V).filter fun z => z.1 * z.2 = m
  have statusU : ∀ z ∈ U, SmallFactor R z ∨ LargePrimeFactor R z := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzS | hzP
    · left
      have hzIcc := Finset.mem_Icc.mp (hS hzS)
      exact ⟨hzIcc.1, hzIcc.2⟩
    · right
      have hzP' := Finset.mem_filter.mp hzP
      have hzIcc := Finset.mem_Icc.mp hzP'.1
      exact ⟨by omega, hzP'.2⟩
  have statusV : ∀ z ∈ V, SmallFactor R z ∨ LargePrimeFactor R z := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzT | hzP
    · left
      have hzIcc := Finset.mem_Icc.mp (hT hzT)
      exact ⟨hzIcc.1, hzIcc.2⟩
    · right
      have hzP' := Finset.mem_filter.mp hzP
      have hzIcc := Finset.mem_Icc.mp hzP'.1
      exact ⟨by omega, hzP'.2⟩
  have smallU {z : ℕ} (hz : z ∈ U) (hzS : SmallFactor R z) : z ∈ S := by
    rcases Finset.mem_union.mp hz with hzOld | hzNew
    · exact hzOld
    · have hzIcc := Finset.mem_Icc.mp (Finset.mem_of_mem_filter z hzNew)
      omega
  have smallV {z : ℕ} (hz : z ∈ V) (hzS : SmallFactor R z) : z ∈ T := by
    rcases Finset.mem_union.mp hz with hzOld | hzNew
    · exact hzOld
    · have hzIcc := Finset.mem_Icc.mp (Finset.mem_of_mem_filter z hzNew)
      omega
  by_cases hP : P = ∅
  · simp [crossRepCount, P, U, V, hP]
  · obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hP
    rcases z₀ with ⟨a, b⟩
    have hz₀' := Finset.mem_filter.mp hz₀
    have haU : a ∈ U := (Finset.mem_product.mp hz₀'.1).1
    have hbV : b ∈ V := (Finset.mem_product.mp hz₀'.1).2
    have haStatus := statusU a haU
    have hbStatus := statusV b hbV
    by_cases habSmall : SmallFactor R a ∧ SmallFactor R b
    · let P₀ := (S ×ˢ T).filter fun z => z.1 * z.2 = m
      have hsub : P ⊆ P₀ := by
        intro z hz
        rcases z with ⟨c, d⟩
        have hz' := Finset.mem_filter.mp hz
        have hcU : c ∈ U := (Finset.mem_product.mp hz'.1).1
        have hdV : d ∈ V := (Finset.mem_product.mp hz'.1).2
        have hcStatus := statusU c hcU
        have hdStatus := statusV d hdV
        have hclass := small_large_product_classification haStatus hbStatus
          hcStatus hdStatus (hz₀'.2.trans hz'.2.symm)
        have hcdSmall : SmallFactor R c ∧ SmallFactor R d := by
          rcases hclass with hsmall | hend
          · exact hsmall.2
          · rcases pair_eq_or_swap_of_endpoint_eq hend with hsame | hswap
            · have hc : a = c := congrArg Prod.fst hsame
              have hd : b = d := congrArg Prod.snd hsame
              exact ⟨hc ▸ habSmall.1, hd ▸ habSmall.2⟩
            · have hc : c = b := (congrArg Prod.snd hswap).symm
              have hd : d = a := (congrArg Prod.fst hswap).symm
              exact ⟨hc.symm ▸ habSmall.2, hd.symm ▸ habSmall.1⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
          ⟨smallU hcU hcdSmall.1, smallV hdV hcdSmall.2⟩, hz'.2⟩
      have hle := Finset.card_le_card hsub
      have hbase : P₀.card ≤ 2 := by
        exact crossRepCount_le_two_of_compatible hcompat m
      exact le_trans hle hbase
    · have hsub : P ⊆ ({(a, b), (b, a)} : Finset (ℕ × ℕ)) := by
        intro z hz
        rcases z with ⟨c, d⟩
        have hz' := Finset.mem_filter.mp hz
        have hcU : c ∈ U := (Finset.mem_product.mp hz'.1).1
        have hdV : d ∈ V := (Finset.mem_product.mp hz'.1).2
        have hclass := small_large_product_classification haStatus hbStatus
          (statusU c hcU) (statusV d hdV) (hz₀'.2.trans hz'.2.symm)
        rcases hclass with hsmall | hend
        · exact (habSmall hsmall.1).elim
        · rcases pair_eq_or_swap_of_endpoint_eq hend with hsame | hswap
          · have : (c, d) = (a, b) := hsame.symm
            simp [this]
          · have : (c, d) = (b, a) := by
              exact Prod.ext (congrArg Prod.snd hswap).symm
                (congrArg Prod.fst hswap).symm
            simp [this]
      exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le (a, b) {(b, a)})

/-- Label/core pairs for a heterogeneous family of fibers. -/
def heterogeneousPairs (Q : Finset ℕ) (K : ℕ) (C : ℕ → Finset ℕ) :
    Finset (ℕ × ℕ) :=
  (Q ×ˢ Finset.Icc 1 K).filter fun z => z.2 ∈ C z.1

/-- Values obtained from heterogeneous prime-labelled fibers. -/
def heterogeneousLift (Q : Finset ℕ) (K : ℕ) (C : ℕ → Finset ℕ) : Finset ℕ :=
  (heterogeneousPairs Q K C).image fun z => z.1 * z.2

/-- Prime-label/core multiplication is injective on heterogeneous pairs. -/
theorem heterogeneousPairs_mul_injective
    (Q : Finset ℕ) (K : ℕ) (C : ℕ → Finset ℕ)
    (hQ : ∀ q ∈ Q, K < q ∧ q.Prime) :
    Set.InjOn (fun z : ℕ × ℕ => z.1 * z.2) (heterogeneousPairs Q K C) := by
  intro z hz w hw heq
  rcases z with ⟨q, d⟩
  rcases w with ⟨r, e⟩
  have hz' := Finset.mem_filter.mp hz
  have hw' := Finset.mem_filter.mp hw
  have hq : q ∈ Q := (Finset.mem_product.mp hz'.1).1
  have hr : r ∈ Q := (Finset.mem_product.mp hw'.1).1
  have hd := Finset.mem_Icc.mp (Finset.mem_product.mp hz'.1).2
  have he := Finset.mem_Icc.mp (Finset.mem_product.mp hw'.1).2
  obtain ⟨hqr, hde⟩ := large_prime_core_decomposition_unique
    (hQ q hq).1 (hQ r hr).1 (hQ q hq).2 (hQ r hr).2 he.1 he.2 heq
  exact Prod.ext hqr hde

/-- The heterogeneous lift has exactly one element for every label/core pair. -/
theorem heterogeneousLift_card_eq_pairs
    (Q : Finset ℕ) (K : ℕ) (C : ℕ → Finset ℕ)
    (hQ : ∀ q ∈ Q, K < q ∧ q.Prime) :
    (heterogeneousLift Q K C).card = (heterogeneousPairs Q K C).card := by
  unfold heterogeneousLift
  exact Finset.card_image_iff.mpr (heterogeneousPairs_mul_injective Q K C hQ)

/-- The number of heterogeneous pairs is the sum of the truncated fiber sizes. -/
theorem heterogeneousPairs_card_eq_sum
    (Q : Finset ℕ) (K : ℕ) (C : ℕ → Finset ℕ) :
    (heterogeneousPairs Q K C).card =
      ∑ q ∈ Q, ((Finset.Icc 1 K).filter fun d => d ∈ C q).card := by
  classical
  unfold heterogeneousPairs
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.card_filter]

/-- If every fiber already lies in the core interval, the lift cardinality is
exactly the sum of the fiber cardinalities. -/
theorem heterogeneousLift_card_eq_sum
    (Q : Finset ℕ) (K : ℕ) (C : ℕ → Finset ℕ)
    (hQ : ∀ q ∈ Q, K < q ∧ q.Prime)
    (hC : ∀ q ∈ Q, C q ⊆ Finset.Icc 1 K) :
    (heterogeneousLift Q K C).card = ∑ q ∈ Q, (C q).card := by
  rw [heterogeneousLift_card_eq_pairs Q K C hQ,
    heterogeneousPairs_card_eq_sum Q K C]
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · exact fun hd => ⟨Finset.mem_Icc.mp (hC q hq hd), hd⟩

/-- Pairwise cross-compatibility is sufficient for the heterogeneous lift to
have fewer than three representations. -/
theorem heterogeneousLift_hasRepBound
    (Q : Finset ℕ) (K : ℕ) (C : ℕ → Finset ℕ)
    (hQ : ∀ q ∈ Q, K < q ∧ q.Prime)
    (hcompat : ∀ q ∈ Q, ∀ r ∈ Q, CrossCompatible (C q) (C r)) :
    HasRepBound 3 (heterogeneousLift Q K C) := by
  intro m
  let A := heterogeneousLift Q K C
  let R := (A ×ˢ A).filter fun z => z.1 < z.2 ∧ z.1 * z.2 = m
  by_cases hR : R = ∅
  · simp [repCount, A, R, hR]
  · obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hR
    rcases z₀ with ⟨a, b⟩
    have hz₀' := Finset.mem_filter.mp hz₀
    have haA : a ∈ A := (Finset.mem_product.mp hz₀'.1).1
    have hbA : b ∈ A := (Finset.mem_product.mp hz₀'.1).2
    rcases Finset.mem_image.mp haA with ⟨⟨q, x⟩, hqx, hqxa⟩
    rcases Finset.mem_image.mp hbA with ⟨⟨r, y⟩, hry, hryb⟩
    have hqx' := Finset.mem_filter.mp hqx
    have hry' := Finset.mem_filter.mp hry
    have hq : q ∈ Q := (Finset.mem_product.mp hqx'.1).1
    have hxIcc : x ∈ Finset.Icc 1 K := (Finset.mem_product.mp hqx'.1).2
    have hx : x ∈ C q := hqx'.2
    have hr : r ∈ Q := (Finset.mem_product.mp hry'.1).1
    have hyIcc : y ∈ Finset.Icc 1 K := (Finset.mem_product.mp hry'.1).2
    have hy : y ∈ C r := hry'.2
    simp only at hqxa hryb
    subst a
    subst b
    let endpoint : ℕ × ℕ → Finset ℕ := fun z => {z.1, z.2}
    let coreEndpoint : ℕ × ℕ → Finset ℕ := fun z => {q * z.1, r * z.2}
    let CR := ((C q ×ˢ C r).filter fun z => z.1 * z.2 = x * y)
    have hendpoint_inj : Set.InjOn endpoint R := by
      intro z hz w hw he
      apply ordered_pair_eq_of_endpoint_eq
      · exact (Finset.mem_filter.mp hz).2.1
      · exact (Finset.mem_filter.mp hw).2.1
      · exact he
    have hclass : ∀ z ∈ R, endpoint z ∈ CR.image coreEndpoint := by
      intro z hz
      rcases z with ⟨c, d⟩
      have hz' := Finset.mem_filter.mp hz
      have hcA : c ∈ A := (Finset.mem_product.mp hz'.1).1
      have hdA : d ∈ A := (Finset.mem_product.mp hz'.1).2
      rcases Finset.mem_image.mp hcA with ⟨⟨s, u⟩, hsu, hsuc⟩
      rcases Finset.mem_image.mp hdA with ⟨⟨t, v⟩, htv, htvd⟩
      have hsu' := Finset.mem_filter.mp hsu
      have htv' := Finset.mem_filter.mp htv
      have hs : s ∈ Q := (Finset.mem_product.mp hsu'.1).1
      have huIcc : u ∈ Finset.Icc 1 K := (Finset.mem_product.mp hsu'.1).2
      have hu : u ∈ C s := hsu'.2
      have ht : t ∈ Q := (Finset.mem_product.mp htv'.1).1
      have hvIcc : v ∈ Finset.Icc 1 K := (Finset.mem_product.mp htv'.1).2
      have hv : v ∈ C t := htv'.2
      simp only at hsuc htvd
      subst c
      subst d
      have heq4 : (q * x) * (r * y) = (s * u) * (t * v) := by
        calc
          (q * x) * (r * y) = m := hz₀'.2.2
          _ = (s * u) * (t * v) := hz'.2.2.symm
      have huBounds := Finset.mem_Icc.mp huIcc
      have hvBounds := Finset.mem_Icc.mp hvIcc
      obtain ⟨hlab, hcore⟩ := lifted_label_product_classification Q K hQ
        hq hr hs ht huBounds.1 hvBounds.1 huBounds.2 hvBounds.2 heq4
      rcases hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · apply Finset.mem_image.mpr
        exact ⟨(u, v), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hcore.symm⟩, rfl⟩
      · apply Finset.mem_image.mpr
        refine ⟨(v, u), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hv, hu⟩, ?_⟩, ?_⟩
        · simpa [Nat.mul_comm] using hcore.symm
        · ext z
          simp [endpoint, coreEndpoint, or_comm]
    have himage : R.image endpoint ⊆ CR.image coreEndpoint := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨z, hz, rfl⟩
      exact hclass z hz
    have hcard_image : (R.image endpoint).card = R.card :=
      Finset.card_image_iff.mpr hendpoint_inj
    have hCR : CR.card ≤ 2 := by
      have hc := crossRepCount_le_two_of_compatible (hcompat q hq r hr) (x * y)
      exact hc
    have hle : R.card ≤ 2 := by
      calc
        R.card = (R.image endpoint).card := hcard_image.symm
        _ ≤ (CR.image coreEndpoint).card := Finset.card_le_card himage
        _ ≤ CR.card := Finset.card_image_le
        _ ≤ 2 := hCR
    have hrep : repCount (heterogeneousLift Q K C) m = R.card := by
      rfl
    rw [hrep]
    omega

/-- Fifteen capacity-dependent core types found by exact finite optimization.
Index `j : Fin 15` represents capacity `j+1`. -/
def fiberType15 : Fin 15 → Finset ℕ
  | ⟨0, _⟩ => {1}
  | ⟨1, _⟩ => {1, 2}
  | ⟨2, _⟩ => {1, 2, 3}
  | ⟨3, _⟩ => {1, 2, 3}
  | ⟨4, _⟩ => {1, 3, 4, 5}
  | ⟨5, _⟩ => {1, 3, 4, 5, 6}
  | ⟨6, _⟩ => {1, 3, 4, 5, 6, 7}
  | ⟨7, _⟩ => {1, 3, 5, 6, 7, 8}
  | ⟨8, _⟩ => {1, 3, 4, 5, 6, 7}
  | ⟨9, _⟩ => {1, 3, 4, 5, 6, 7}
  | ⟨10, _⟩ => {1, 3, 4, 5, 6, 7, 11}
  | ⟨11, _⟩ => {1, 2, 5, 7, 8, 9, 11, 12}
  | ⟨12, _⟩ => {1, 2, 7, 8, 9, 10, 11, 12, 13}
  | ⟨13, _⟩ => {3, 7, 8, 9, 10, 11, 12, 13, 14}
  | ⟨14, _⟩ => {1, 2, 5, 7, 8, 9, 11, 12, 13, 15}
  | ⟨n + 15, h⟩ => by omega

/-- Every pair of the fifteen types has ordered product multiplicity at most
two, including a type paired with itself. -/
theorem fiberType15_pairwise_compatible :
    ∀ i j : Fin 15, CrossCompatible (fiberType15 i) (fiberType15 j) := by
  native_decide

/-- Every element of a capacity-`j+1` type respects that capacity. -/
theorem fiberType15_bounded (j : Fin 15) (d : ℕ) (hd : d ∈ fiberType15 j) :
    d ≤ j.val + 1 := by
  fin_cases j <;> simp [fiberType15] at hd ⊢ <;> omega

/-- The layer weight for capacity `j+1`; the last layer is the bulk weight
`1/15`, while earlier layers are `1/(k(k+1))`. -/
def fiberWeight15 (j : Fin 15) : ℚ :=
  if j.val = 14 then 1 / 15 else 1 / ((j.val + 1) * (j.val + 2) : ℕ)

/-- Every certified type contains only positive naturals. -/
theorem fiberType15_positive (j : Fin 15) (d : ℕ) (hd : d ∈ fiberType15 j) :
    0 < d := by
  fin_cases j <;> simp [fiberType15] at hd ⊢ <;> omega

/-- Select the certified type appropriate to an integer capacity. -/
def baseFiber15 (J : ℕ) : Finset ℕ :=
  fiberType15 ⟨min (J - 1) 14, by omega⟩

/-- The base type always lies in `[1,15]`. -/
theorem baseFiber15_subset (J : ℕ) : baseFiber15 J ⊆ Finset.Icc 1 15 := by
  intro d hd
  have hpos := fiberType15_positive ⟨min (J - 1) 14, by omega⟩ d hd
  have hle := fiberType15_bounded ⟨min (J - 1) 14, by omega⟩ d hd
  exact Finset.mem_Icc.mpr ⟨hpos, by omega⟩

/-- At positive capacity, the chosen base type respects that capacity. -/
theorem baseFiber15_le_capacity {J d : ℕ} (hJ : 0 < J) (hd : d ∈ baseFiber15 J) :
    d ≤ J := by
  have hle := fiberType15_bounded ⟨min (J - 1) 14, by omega⟩ d hd
  change d ≤ min (J - 1) 14 + 1 at hle
  omega

/-- Add every prime from 16 through the capacity to the certified base type. -/
def extendedFiber15 (J : ℕ) : Finset ℕ :=
  primeExtendType 15 J (baseFiber15 J)

/-- Any two capacity-dependent infinite extensions are cross-compatible. -/
theorem extendedFiber15_crossCompatible (J L : ℕ) :
    CrossCompatible (extendedFiber15 J) (extendedFiber15 L) := by
  apply primeExtendType_crossCompatible
  · exact baseFiber15_subset J
  · exact baseFiber15_subset L
  · exact fiberType15_pairwise_compatible _ _

/-- At positive capacity, every element of the extended fiber is available. -/
theorem extendedFiber15_le_capacity {J d : ℕ} (hJ : 0 < J)
    (hd : d ∈ extendedFiber15 J) : d ≤ J := by
  rcases Finset.mem_union.mp hd with hdBase | hdPrime
  · exact baseFiber15_le_capacity hJ hdBase
  · exact (Finset.mem_Icc.mp (Finset.mem_of_mem_filter d hdPrime)).2

/-- Prime labels above `sqrt n`. -/
def sqrtPrimeLabels (n : ℕ) : Finset ℕ :=
  (Finset.Icc (n.sqrt + 1) n).filter Nat.Prime

/-- A label above `sqrt n` has core capacity at most `sqrt n`. -/
theorem div_label_le_sqrt {n q : ℕ} (hq : q ∈ sqrtPrimeLabels n) :
    n / q ≤ n.sqrt := by
  have hq' := Finset.mem_filter.mp hq
  have hqIcc := Finset.mem_Icc.mp hq'.1
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hq'.2.pos]
  have hqs : n.sqrt + 1 ≤ q := by omega
  calc
    n < (n.sqrt + 1) * (n.sqrt + 1) := by simpa using Nat.lt_succ_sqrt n
    _ ≤ (n.sqrt + 1) * q := Nat.mul_le_mul_left _ hqs

/-- The heterogeneous construction associated with the certified 15-type
family and its common prime tail. -/
def fiberType15Construction (n : ℕ) : Finset ℕ :=
  heterogeneousLift (sqrtPrimeLabels n) n.sqrt
    (fun q => extendedFiber15 (n / q))

/-- The certified heterogeneous construction is admissible. -/
theorem fiberType15Construction_hasRepBound (n : ℕ) :
    HasRepBound 3 (fiberType15Construction n) := by
  apply heterogeneousLift_hasRepBound
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqIcc := Finset.mem_Icc.mp hq'.1
    exact ⟨by omega, hq'.2⟩
  · intro q hq r hr
    exact extendedFiber15_crossCompatible (n / q) (n / r)

/-- Every element of the certified heterogeneous construction lies in
`{1,…,n}`. -/
theorem fiberType15Construction_subset_Icc (n : ℕ) :
    fiberType15Construction n ⊆ Finset.Icc 1 n := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨⟨q, d⟩, hqd, rfl⟩
  have hqd' := Finset.mem_filter.mp hqd
  have hq : q ∈ sqrtPrimeLabels n := (Finset.mem_product.mp hqd'.1).1
  have hdIcc : d ∈ Finset.Icc 1 n.sqrt := (Finset.mem_product.mp hqd'.1).2
  have hdFiber : d ∈ extendedFiber15 (n / q) := hqd'.2
  have hq' := Finset.mem_filter.mp hq
  have hqIcc := Finset.mem_Icc.mp hq'.1
  have hJpos : 0 < n / q := Nat.div_pos hqIcc.2 hq'.2.pos
  have hdle : d ≤ n / q := extendedFiber15_le_capacity hJpos hdFiber
  have hmul : q * d ≤ n := by
    simpa [Nat.mul_comm] using Nat.mul_le_of_le_div q d n hdle
  exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hq'.2.pos (Finset.mem_Icc.mp hdIcc).1, hmul⟩

/-- Exact finite lower bound supplied by the 15-type construction. -/
theorem fiberType15Construction_card_le_g (n : ℕ) :
    (fiberType15Construction n).card ≤ g 3 n := by
  classical
  unfold g
  apply Finset.le_sup
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_powerset.mpr (fiberType15Construction_subset_Icc n),
    fiberType15Construction_hasRepBound n⟩

/-- Exact objective value of the certified type family. -/
theorem fiberType15_beta_value :
    ∑ j : Fin 15, fiberWeight15 j * (fiberType15 j).card =
      (53267 : ℚ) / 20020 := by
  native_decide

/-- After subtracting reciprocal primes through 15, the certified finite
second-order gain is exactly `79/60`. -/
theorem fiberType15_gamma_value :
    (∑ j : Fin 15, fiberWeight15 j * (fiberType15 j).card) -
        ((1 : ℚ) / 2 + 1 / 3 + 1 / 5 + 1 / 7 + 1 / 11 + 1 / 13) =
      (79 : ℚ) / 60 := by
  native_decide

end Erdos796
