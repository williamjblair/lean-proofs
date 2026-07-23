import Research.CoreSidon

namespace Erdos796

/-- A large prime cannot divide a positive core lying below its threshold. -/
theorem large_prime_not_dvd_core
    {K p x : ℕ} (hpK : K < p) (hxpos : 0 < x) (hxK : x ≤ K) : ¬ p ∣ x := by
  intro h
  have := Nat.le_of_dvd hxpos h
  omega

/-- In a product of one large prime label and one small positive core, any
other large prime divisor must be that label. -/
theorem large_prime_dvd_label_mul_core
    {K p q x : ℕ} (hpK : K < p) (hp : p.Prime)
    (hq : q.Prime) (hxpos : 0 < x) (hxK : x ≤ K)
    (hdiv : p ∣ q * x) : p = q := by
  rcases hp.dvd_mul.mp hdiv with hpq | hpx
  · rcases (Nat.dvd_prime hq).mp hpq with hp1 | hpq
    · exact (hp.ne_one hp1).elim
    · exact hpq
  · exact (large_prime_not_dvd_core hpK hxpos hxK hpx).elim

/-- The representation `large prime × small core` is unique. -/
theorem large_prime_core_decomposition_unique
    {K q r x y : ℕ}
    (hqK : K < q) (hrK : K < r) (hq : q.Prime) (hr : r.Prime)
    (hypos : 0 < y) (hyK : y ≤ K)
    (heq : q * x = r * y) : q = r ∧ x = y := by
  have hqdiv : q ∣ r * y := by rw [← heq]; exact Nat.dvd_mul_right q x
  have hqr := large_prime_dvd_label_mul_core hqK hq hr hypos hyK hqdiv
  subst r
  exact ⟨rfl, Nat.mul_left_cancel hq.pos heq⟩

/-- Injectivity on ordered core pairs implies the usual two alternatives for
an equality of products of not-necessarily-ordered core elements. -/
theorem sidon_core_product_classification
    (C : Finset ℕ) (hSidon : IsMulSidonCore C)
    {x y u v : ℕ} (hx : x ∈ C) (hy : y ∈ C) (hu : u ∈ C) (hv : v ∈ C)
    (heq : x * y = u * v) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  classical
  have hinj : Set.InjOn (fun z : ℕ × ℕ => z.1 * z.2) (unorderedPairs C) :=
    Finset.card_image_iff.mp hSidon
  rcases le_total x y with hxy | hyx <;> rcases le_total u v with huv | hvu
  · have hpairs : (x, y) = (u, v) := hinj
      (by simp [unorderedPairs, hx, hy, hxy])
      (by simp [unorderedPairs, hu, hv, huv]) heq
    left
    exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩
  · have hprod : x * y = v * u := by simpa [Nat.mul_comm] using heq
    have hpairs : (x, y) = (v, u) := hinj
      (by simp [unorderedPairs, hx, hy, hxy])
      (by simp [unorderedPairs, hu, hv, hvu]) hprod
    right
    exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩
  · have hprod : y * x = u * v := by simpa [Nat.mul_comm] using heq
    have hpairs : (y, x) = (u, v) := hinj
      (by simp [unorderedPairs, hx, hy, hyx])
      (by simp [unorderedPairs, hu, hv, huv]) hprod
    right
    exact ⟨congrArg Prod.snd hpairs, congrArg Prod.fst hpairs⟩
  · have hprod : y * x = v * u := by simpa [Nat.mul_comm] using heq
    have hpairs : (y, x) = (v, u) := hinj
      (by simp [unorderedPairs, hx, hy, hyx])
      (by simp [unorderedPairs, hu, hv, hvu]) hprod
    left
    exact ⟨congrArg Prod.snd hpairs, congrArg Prod.fst hpairs⟩

/-- A Sidon core containing `1` and two nontrivial factors cannot also contain
their product.  Thus composite exceptions added to a prime-complete core must
have at least three prime factors with multiplicity. -/
theorem sidon_core_product_exclusion
    (C : Finset ℕ) (hSidon : IsMulSidonCore C)
    {p q : ℕ} (hp1 : 1 < p) (hpq : p ≤ q)
    (h1 : 1 ∈ C) (hp : p ∈ C) (hq : q ∈ C) (hpqmem : p * q ∈ C) : False := by
  have hclass := sidon_core_product_classification C hSidon
    h1 hpqmem hp hq (by simp)
  rcases hclass with h | h
  · exact (ne_of_lt hp1) h.1
  · have hq1 : 1 < q := lt_of_lt_of_le hp1 hpq
    exact (ne_of_lt hq1) h.1

/-- In an equality of products of two prime-labelled elements, the multiset
of large labels is determined and cancellation leaves equality of core
products.  No Sidon hypothesis on the cores is needed here. -/
theorem lifted_label_product_classification
    (Q : Finset ℕ) (K : ℕ)
    (hQ : ∀ q ∈ Q, K < q ∧ q.Prime)
    {q r s t x y u v : ℕ}
    (hq : q ∈ Q) (hr : r ∈ Q) (hs : s ∈ Q) (ht : t ∈ Q)
    (hupos : 0 < u) (hvpos : 0 < v) (huK : u ≤ K) (hvK : v ≤ K)
    (heq : (q * x) * (r * y) = (s * u) * (t * v)) :
    ((q = s ∧ r = t) ∨ (q = t ∧ r = s)) ∧ x * y = u * v := by
  obtain ⟨hqK, hqprime⟩ := hQ q hq
  obtain ⟨hrK, hrprime⟩ := hQ r hr
  obtain ⟨_, hsprime⟩ := hQ s hs
  obtain ⟨_, htprime⟩ := hQ t ht
  have hqdiv : q ∣ (s * u) * (t * v) := by
    rw [← heq]
    exact ⟨x * (r * y), by ac_rfl⟩
  rcases hqprime.dvd_mul.mp hqdiv with hqsu | hqtv
  · have hqs : q = s := large_prime_dvd_label_mul_core hqK hqprime hsprime
        hupos huK hqsu
    subst s
    have hcancelq : x * (r * y) = u * (t * v) := by
      apply Nat.mul_left_cancel hqprime.pos
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using heq
    have hrdiv : r ∣ t * v := by
      have : r ∣ u * (t * v) := by
        rw [← hcancelq]
        exact ⟨x * y, by ac_rfl⟩
      rcases hrprime.dvd_mul.mp this with hru | hrtv
      · exact (large_prime_not_dvd_core hrK hupos huK hru).elim
      · exact hrtv
    have hrt : r = t := large_prime_dvd_label_mul_core hrK hrprime htprime
      hvpos hvK hrdiv
    subst t
    have hcore : x * y = u * v := by
      apply Nat.mul_left_cancel hrprime.pos
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcancelq
    exact ⟨Or.inl ⟨rfl, rfl⟩, hcore⟩
  · have hqt : q = t := large_prime_dvd_label_mul_core hqK hqprime htprime
        hvpos hvK hqtv
    subst t
    have hcancelq : x * (r * y) = v * (s * u) := by
      apply Nat.mul_left_cancel hqprime.pos
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using heq
    have hrdiv : r ∣ s * u := by
      have : r ∣ v * (s * u) := by
        rw [← hcancelq]
        exact ⟨x * y, by ac_rfl⟩
      rcases hrprime.dvd_mul.mp this with hrv | hrsu
      · exact (large_prime_not_dvd_core hrK hvpos hvK hrv).elim
      · exact hrsu
    have hrs : r = s := large_prime_dvd_label_mul_core hrK hrprime hsprime
      hupos huK hrdiv
    subst s
    have hcore : x * y = u * v := by
      apply Nat.mul_left_cancel hrprime.pos
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcancelq
    exact ⟨Or.inr ⟨rfl, rfl⟩, hcore⟩

/-- Equality of products of two lifted elements has only the expected label
matching and the two possible assignments of a unique unordered core pair. -/
theorem lifted_four_factor_classification
    (C Q : Finset ℕ) (K : ℕ)
    (hSidon : IsMulSidonCore C)
    (hCpos : ∀ x ∈ C, 0 < x) (hCbound : ∀ x ∈ C, x ≤ K)
    (hQ : ∀ q ∈ Q, K < q ∧ q.Prime)
    {q r s t x y u v : ℕ}
    (hq : q ∈ Q) (hr : r ∈ Q) (hs : s ∈ Q) (ht : t ∈ Q)
    (hx : x ∈ C) (hy : y ∈ C) (hu : u ∈ C) (hv : v ∈ C)
    (heq : (q * x) * (r * y) = (s * u) * (t * v)) :
    ((q = s ∧ r = t) ∨ (q = t ∧ r = s)) ∧
      ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
  obtain ⟨hqK, hqprime⟩ := hQ q hq
  obtain ⟨hrK, hrprime⟩ := hQ r hr
  obtain ⟨hsK, hsprime⟩ := hQ s hs
  obtain ⟨htK, htprime⟩ := hQ t ht
  have hqdiv : q ∣ (s * u) * (t * v) := by
    rw [← heq]
    exact ⟨x * (r * y), by ac_rfl⟩
  rcases hqprime.dvd_mul.mp hqdiv with hqsu | hqtv
  · have hqs : q = s := large_prime_dvd_label_mul_core hqK hqprime hsprime
        (hCpos u hu) (hCbound u hu) hqsu
    subst s
    have hcancelq : x * (r * y) = u * (t * v) := by
      apply Nat.mul_left_cancel hqprime.pos
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using heq
    have hrdiv : r ∣ t * v := by
      have : r ∣ u * (t * v) := by
        rw [← hcancelq]
        exact ⟨x * y, by ac_rfl⟩
      rcases hrprime.dvd_mul.mp this with hru | hrtv
      · exact (large_prime_not_dvd_core hrK (hCpos u hu) (hCbound u hu) hru).elim
      · exact hrtv
    have hrt : r = t := large_prime_dvd_label_mul_core hrK hrprime htprime
      (hCpos v hv) (hCbound v hv) hrdiv
    subst t
    have hcore : x * y = u * v := by
      apply Nat.mul_left_cancel hrprime.pos
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcancelq
    exact ⟨Or.inl ⟨rfl, rfl⟩,
      sidon_core_product_classification C hSidon hx hy hu hv hcore⟩
  · have hqt : q = t := large_prime_dvd_label_mul_core hqK hqprime htprime
        (hCpos v hv) (hCbound v hv) hqtv
    subst t
    have hcancelq : x * (r * y) = v * (s * u) := by
      apply Nat.mul_left_cancel hqprime.pos
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using heq
    have hrdiv : r ∣ s * u := by
      have : r ∣ v * (s * u) := by
        rw [← hcancelq]
        exact ⟨x * y, by ac_rfl⟩
      rcases hrprime.dvd_mul.mp this with hrv | hrsu
      · exact (large_prime_not_dvd_core hrK (hCpos v hv) (hCbound v hv) hrv).elim
      · exact hrsu
    have hrs : r = s := large_prime_dvd_label_mul_core hrK hrprime hsprime
      (hCpos u hu) (hCbound u hu) hrdiv
    subst s
    have hcore : x * y = u * v := by
      apply Nat.mul_left_cancel hrprime.pos
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcancelq
    exact ⟨Or.inr ⟨rfl, rfl⟩,
      sidon_core_product_classification C hSidon hx hy hu hv hcore⟩

/-- Forgetting the order of a strictly increasing natural pair is injective. -/
theorem ordered_pair_eq_of_endpoint_eq
    {a b c d : ℕ} (hab : a < b) (hcd : c < d)
    (h : ({a, b} : Finset ℕ) = {c, d}) : (a, b) = (c, d) := by
  have ha : a = c ∨ a = d := by
    have : a ∈ ({c, d} : Finset ℕ) := by rw [← h]; simp
    simpa using this
  have hb : b = c ∨ b = d := by
    have : b ∈ ({c, d} : Finset ℕ) := by rw [← h]; simp
    simpa using this
  rcases ha with hac | had <;> rcases hb with hbc | hbd
  · omega
  · apply Prod.ext <;> simp_all
  · omega
  · omega

/-- Equality of two two-element endpoint finsets determines an ordered pair
up to swapping. -/
theorem pair_eq_or_swap_of_endpoint_eq
    {a b c d : ℕ} (h : ({a, b} : Finset ℕ) = {c, d}) :
    (a, b) = (c, d) ∨ (a, b) = (d, c) := by
  have ha : a = c ∨ a = d := by
    have : a ∈ ({c, d} : Finset ℕ) := by rw [← h]; simp
    simpa using this
  have hb : b = c ∨ b = d := by
    have : b ∈ ({c, d} : Finset ℕ) := by rw [← h]; simp
    simpa using this
  rcases ha with hac | had <;> rcases hb with hbc | hbd
  · have : b = d := by
      have hdmem : d ∈ ({a, b} : Finset ℕ) := by rw [h]; simp
      simp [hac, hbc] at hdmem
      exact hbc.trans hdmem.symm
    exact Or.inl (Prod.ext hac this)
  · exact Or.inl (Prod.ext hac hbd)
  · exact Or.inr (Prod.ext had hbc)
  · have : b = c := by
      have hcmem : c ∈ ({a, b} : Finset ℕ) := by rw [h]; simp
      simp [had, hbd] at hcmem
      exact hbd.trans hcmem.symm
    exact Or.inr (Prod.ext had this)

/-- Products of a finite set of prime labels above `K` with a positive
multiplicative-Sidon core below `K` have fewer than three representations. -/
def liftedSet (Q C : Finset ℕ) : Finset ℕ :=
  (Q ×ˢ C).image fun z => z.1 * z.2

/-- The abstract large-prime/core lifting theorem. -/
theorem liftedSet_hasRepBound
    (C Q : Finset ℕ) (K : ℕ)
    (hSidon : IsMulSidonCore C)
    (hCpos : ∀ x ∈ C, 0 < x) (hCbound : ∀ x ∈ C, x ≤ K)
    (hQ : ∀ q ∈ Q, K < q ∧ q.Prime) :
    HasRepBound 3 (liftedSet Q C) := by
  intro m
  let R := ((liftedSet Q C) ×ˢ (liftedSet Q C)).filter
    fun z => z.1 < z.2 ∧ z.1 * z.2 = m
  by_cases hR : R = ∅
  · simp [repCount, R, hR]
  · obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hR
    rcases z₀ with ⟨a, b⟩
    have hz₀' := Finset.mem_filter.mp hz₀
    have haA : a ∈ liftedSet Q C := (Finset.mem_product.mp hz₀'.1).1
    have hbA : b ∈ liftedSet Q C := (Finset.mem_product.mp hz₀'.1).2
    rcases Finset.mem_image.mp haA with ⟨⟨q, x⟩, hqx, hqxa⟩
    rcases Finset.mem_image.mp hbA with ⟨⟨r, y⟩, hry, hryb⟩
    have hq : q ∈ Q := (Finset.mem_product.mp hqx).1
    have hx : x ∈ C := (Finset.mem_product.mp hqx).2
    have hr : r ∈ Q := (Finset.mem_product.mp hry).1
    have hy : y ∈ C := (Finset.mem_product.mp hry).2
    simp only at hqxa hryb
    subst a
    subst b
    let endpoint : ℕ × ℕ → Finset ℕ := fun z => {z.1, z.2}
    let E₁ : Finset ℕ := {q * x, r * y}
    let E₂ : Finset ℕ := {q * y, r * x}
    have hendpoint_inj : Set.InjOn endpoint R := by
      intro z hz w hw he
      apply ordered_pair_eq_of_endpoint_eq
      · exact (Finset.mem_filter.mp hz).2.1
      · exact (Finset.mem_filter.mp hw).2.1
      · exact he
    have hclass : ∀ z ∈ R, endpoint z = E₁ ∨ endpoint z = E₂ := by
      intro z hz
      rcases z with ⟨c, d⟩
      have hz' := Finset.mem_filter.mp hz
      have hcA : c ∈ liftedSet Q C := (Finset.mem_product.mp hz'.1).1
      have hdA : d ∈ liftedSet Q C := (Finset.mem_product.mp hz'.1).2
      rcases Finset.mem_image.mp hcA with ⟨⟨s, u⟩, hsu, hsuc⟩
      rcases Finset.mem_image.mp hdA with ⟨⟨t, v⟩, htv, htvd⟩
      have hs : s ∈ Q := (Finset.mem_product.mp hsu).1
      have hu : u ∈ C := (Finset.mem_product.mp hsu).2
      have ht : t ∈ Q := (Finset.mem_product.mp htv).1
      have hv : v ∈ C := (Finset.mem_product.mp htv).2
      simp only at hsuc htvd
      subst c
      subst d
      have heq4 : (q * x) * (r * y) = (s * u) * (t * v) := by
        calc
          (q * x) * (r * y) = m := hz₀'.2.2
          _ = (s * u) * (t * v) := hz'.2.2.symm
      obtain ⟨hlab, hcore⟩ := lifted_four_factor_classification C Q K
        hSidon hCpos hCbound hQ hq hr hs ht hx hy hu hv heq4
      rcases hlab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hcore with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · right
        ext z
        simp [endpoint, E₂, or_comm]
      · left
        ext z
        simp [endpoint, E₁, or_comm]
    have himage : R.image endpoint ⊆ ({E₁, E₂} : Finset (Finset ℕ)) := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨z, hz, rfl⟩
      rcases hclass z hz with h | h
      · simp [h]
      · simp [h]
    have hcard_image : (R.image endpoint).card = R.card :=
      Finset.card_image_iff.mpr hendpoint_inj
    have hle : R.card ≤ 2 := by
      calc
        R.card = (R.image endpoint).card := hcard_image.symm
        _ ≤ ({E₁, E₂} : Finset (Finset ℕ)).card := Finset.card_le_card himage
        _ ≤ 2 := by exact Finset.card_insert_le E₁ {E₂}
    have : repCount (liftedSet Q C) m = R.card := by rfl
    omega

/-- The representation bound is inherited by subsets. -/
theorem HasRepBound.mono {A B : Finset ℕ} {k : ℕ}
    (hBA : B ⊆ A) (hA : HasRepBound k A) : HasRepBound k B := by
  intro m
  have hsub :
      ((B ×ˢ B).filter fun z => z.1 < z.2 ∧ z.1 * z.2 = m) ⊆
        ((A ×ˢ A).filter fun z => z.1 < z.2 ∧ z.1 * z.2 = m) := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hzprod := Finset.mem_product.mp hz'.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hBA hzprod.1, hBA hzprod.2⟩, hz'.2⟩
  have hle := Finset.card_le_card hsub
  exact lt_of_le_of_lt hle (hA m)

/-- Restrict the certified infinite core to `[1,K]`. -/
def certifiedCoreBelow (K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter infiniteCorePredicate

/-- Prime labels strictly above `K` and at most `n`. -/
def primeLabelsAbove (n K : ℕ) : Finset ℕ :=
  (Finset.Icc (K + 1) n).filter Nat.Prime

/-- The explicit augmented construction, with products truncated back to
`[1,n]`. -/
def augmentedConstruction (n K : ℕ) : Finset ℕ :=
  (liftedSet (primeLabelsAbove n K) (certifiedCoreBelow K)).filter fun a => a ≤ n

/-- Every finite restriction of the certified infinite core is Sidon. -/
theorem certifiedCoreBelow_is_sidon (K : ℕ) :
    IsMulSidonCore (certifiedCoreBelow K) := by
  classical
  apply Finset.card_image_iff.mpr
  intro z hz w hw heq
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  have hz' := Finset.mem_filter.mp hz
  have hw' := Finset.mem_filter.mp hw
  have hab : a ≤ b := hz'.2
  have hcd : c ≤ d := hw'.2
  have haC : a ∈ certifiedCoreBelow K := (Finset.mem_product.mp hz'.1).1
  have hbC : b ∈ certifiedCoreBelow K := (Finset.mem_product.mp hz'.1).2
  have hcC : c ∈ certifiedCoreBelow K := (Finset.mem_product.mp hw'.1).1
  have hdC : d ∈ certifiedCoreBelow K := (Finset.mem_product.mp hw'.1).2
  have ha := (Finset.mem_filter.mp haC).2
  have hb := (Finset.mem_filter.mp hbC).2
  have hc := (Finset.mem_filter.mp hcC).2
  have hd := (Finset.mem_filter.mp hdC).2
  exact infiniteCore_mul_unique a b c d hab hcd ha hb hc hd heq

/-- For every `n,K`, the augmented construction has fewer than three product
representations. -/
theorem augmentedConstruction_hasRepBound (n K : ℕ) :
    HasRepBound 3 (augmentedConstruction n K) := by
  have hCpos : ∀ x ∈ certifiedCoreBelow K, 0 < x := by
    intro x hx
    exact (Finset.mem_Icc.mp (Finset.mem_of_mem_filter x hx)).1
  have hCbound : ∀ x ∈ certifiedCoreBelow K, x ≤ K := by
    intro x hx
    exact (Finset.mem_Icc.mp (Finset.mem_of_mem_filter x hx)).2
  have hQ : ∀ q ∈ primeLabelsAbove n K, K < q ∧ q.Prime := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqIcc := Finset.mem_Icc.mp hq'.1
    exact ⟨by omega, hq'.2⟩
  apply HasRepBound.mono (A := liftedSet (primeLabelsAbove n K) (certifiedCoreBelow K))
  · intro a ha
    exact Finset.mem_of_mem_filter a ha
  · exact liftedSet_hasRepBound (certifiedCoreBelow K) (primeLabelsAbove n K) K
      (certifiedCoreBelow_is_sidon K) hCpos hCbound hQ

/-- Every member of the construction lies in the required interval. -/
theorem augmentedConstruction_subset_Icc (n K : ℕ) :
    augmentedConstruction n K ⊆ Finset.Icc 1 n := by
  intro a ha
  have ha' := Finset.mem_filter.mp ha
  have haLift := Finset.mem_image.mp ha'.1
  rcases haLift with ⟨⟨q, d⟩, hqd, rfl⟩
  have hq := (Finset.mem_product.mp hqd).1
  have hd := (Finset.mem_product.mp hqd).2
  have hqprime := (Finset.mem_filter.mp hq).2
  have hdpos := (Finset.mem_Icc.mp (Finset.mem_of_mem_filter d hd)).1
  exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hqprime.pos hdpos, ha'.2⟩

/-- Label/core pairs whose product survives the cutoff at `n`. -/
def augmentedConstructionPairs (n K : ℕ) : Finset (ℕ × ℕ) :=
  ((primeLabelsAbove n K) ×ˢ (certifiedCoreBelow K)).filter
    fun z => z.1 * z.2 ≤ n

/-- The construction has exactly one element per surviving label/core pair. -/
theorem augmentedConstruction_card_eq_pairs (n K : ℕ) :
    (augmentedConstruction n K).card = (augmentedConstructionPairs n K).card := by
  let mul : ℕ × ℕ → ℕ := fun z => z.1 * z.2
  have hsets :
      augmentedConstruction n K = (augmentedConstructionPairs n K).image mul := by
    ext a
    constructor
    · intro ha
      have ha' := Finset.mem_filter.mp ha
      rcases Finset.mem_image.mp ha'.1 with ⟨z, hz, rfl⟩
      apply Finset.mem_image.mpr
      exact ⟨z, Finset.mem_filter.mpr ⟨hz, ha'.2⟩, rfl⟩
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨z, hz, rfl⟩
      have hz' := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨z, hz'.1, rfl⟩, hz'.2⟩
  rw [hsets]
  apply Finset.card_image_iff.mpr
  intro z hz w hw heq
  rcases z with ⟨q, d⟩
  rcases w with ⟨r, e⟩
  have hzprod := Finset.mem_product.mp (Finset.mem_of_mem_filter (q, d) hz)
  have hwprod := Finset.mem_product.mp (Finset.mem_of_mem_filter (r, e) hw)
  have hqdata := Finset.mem_filter.mp hzprod.1
  have hrdata := Finset.mem_filter.mp hwprod.1
  have hdIcc := Finset.mem_Icc.mp
    (Finset.mem_of_mem_filter d hzprod.2)
  have heIcc := Finset.mem_Icc.mp
    (Finset.mem_of_mem_filter e hwprod.2)
  have hqr := large_prime_core_decomposition_unique
    (by have := Finset.mem_Icc.mp hqdata.1; omega)
    (by have := Finset.mem_Icc.mp hrdata.1; omega)
    hqdata.2 hrdata.2 heIcc.1 heIcc.2 heq
  exact Prod.ext hqr.1 hqr.2

/-- The exact extremal function is at least the cardinality of every member of
the explicit two-parameter construction. -/
theorem augmentedConstruction_card_le_g (n K : ℕ) :
    (augmentedConstruction n K).card ≤ g 3 n := by
  classical
  unfold g
  apply Finset.le_sup
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_powerset.mpr (augmentedConstruction_subset_Icc n K),
    augmentedConstruction_hasRepBound n K⟩

end Erdos796
