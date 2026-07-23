import Research.UpperRemainder

namespace Erdos796

/-- Three nontrivial factors above a threshold. -/
def HasThreeLargeFactors (z d : ℕ) : Prop :=
  ∃ x y w : ℕ, z < x ∧ z < y ∧ z < w ∧ d = x * y * w

/-- Prime factors at most the threshold, with multiplicity. -/
def smallPrimeList (z d : ℕ) : List ℕ :=
  d.primeFactorsList.filter fun p => decide (p ≤ z)

/-- Prime factors above the threshold, with multiplicity. -/
def largePrimeList (z d : ℕ) : List ℕ :=
  d.primeFactorsList.filter fun p => !(decide (p ≤ z))

lemma smallPrimeList_append_large_perm (z d : ℕ) :
    (smallPrimeList z d ++ largePrimeList z d).Perm d.primeFactorsList := by
  exact List.filter_append_perm (fun p => decide (p ≤ z)) d.primeFactorsList

lemma smallPrimeList_prod_mul_largePrimeList_prod
    {z d : ℕ} (hd : d ≠ 0) :
    (smallPrimeList z d).prod * (largePrimeList z d).prod = d := by
  calc
    _ = (smallPrimeList z d ++ largePrimeList z d).prod :=
      List.prod_append.symm
    _ = d.primeFactorsList.prod :=
      (smallPrimeList_append_large_perm z d).prod_eq
    _ = d := Nat.prod_primeFactorsList hd

lemma mem_smallPrimeList {z d p : ℕ} (hp : p ∈ smallPrimeList z d) :
    p.Prime ∧ p ≤ z := by
  have hp' := List.mem_filter.mp hp
  exact ⟨Nat.prime_of_mem_primeFactorsList hp'.1, by simpa using hp'.2⟩

lemma mem_largePrimeList {z d p : ℕ} (hp : p ∈ largePrimeList z d) :
    p.Prime ∧ z < p := by
  have hp' := List.mem_filter.mp hp
  have hnot : ¬p ≤ z := by
    simpa using hp'.2
  exact ⟨Nat.prime_of_mem_primeFactorsList hp'.1, by omega⟩

lemma smallPrimeList_prod_pos (z d : ℕ) : 0 < (smallPrimeList z d).prod := by
  apply List.prod_pos
  intro p hp
  exact (mem_smallPrimeList hp).1.pos

lemma largePrimeList_prod_pos (z d : ℕ) : 0 < (largePrimeList z d).prod := by
  apply List.prod_pos
  intro p hp
  exact (mem_largePrimeList hp).1.pos

lemma primeFactors_smallPrimeList_prod_le
    {z d p : ℕ} (hp : p.Prime) (hpd : p ∣ (smallPrimeList z d).prod) :
    p ≤ z := by
  rcases (Prime.dvd_prod_iff hp.prime).mp hpd with ⟨a, ha, hpa⟩
  have ha' := mem_smallPrimeList ha
  rcases (Nat.dvd_prime ha'.1).mp hpa with h1 | hEq
  · exact (hp.ne_one h1).elim
  · simpa [hEq] using ha'.2

/-- If the small-prime kernel exceeds `z^6`, the whole integer has three
factors above `z`. -/
theorem threeLarge_of_smallKernel_gt
    {z d : ℕ} (hz : 1 < z) (hd : d ≠ 0)
    (hsmall : z ^ 6 < (smallPrimeList z d).prod) :
    HasThreeLargeFactors z d := by
  let t := (smallPrimeList z d).prod
  let v := (largePrimeList z d).prod
  have hall : ∀ p : ℕ, p.Prime → p ∣ t → p ≤ z := by
    intro p hp hpt
    exact primeFactors_smallPrimeList_prod_le hp hpt
  rcases exists_three_large_of_primeFactors_le hz hsmall hall with
    ⟨x, y, w, hx, hy, hw, ht⟩
  change t = x * y * w at ht
  have hv : 0 < v := largePrimeList_prod_pos z d
  have hdprod : t * v = d := smallPrimeList_prod_mul_largePrimeList_prod hd
  exact ⟨x, y, w * v, hx, hy, by
    exact lt_of_lt_of_le hw (Nat.le_mul_of_pos_right w hv), by
    calc
      d = t * v := hdprod.symm
      _ = (x * y * w) * v := by rw [ht]
      _ = x * y * (w * v) := by ring⟩

/-- Three large prime factors already give three large factors. -/
theorem threeLarge_of_largePrimeList_three
    {z d p q r : ℕ} {L : List ℕ} (hd : d ≠ 0)
    (hlist : largePrimeList z d = p :: q :: r :: L) :
    HasThreeLargeFactors z d := by
  have hpMem : p ∈ largePrimeList z d := by rw [hlist]; simp
  have hqMem : q ∈ largePrimeList z d := by rw [hlist]; simp
  have hrMem : r ∈ largePrimeList z d := by rw [hlist]; simp
  have hp : p.Prime ∧ z < p := mem_largePrimeList hpMem
  have hq : q.Prime ∧ z < q := mem_largePrimeList hqMem
  have hr : r.Prime ∧ z < r := mem_largePrimeList hrMem
  let t := (smallPrimeList z d).prod
  have ht : 0 < t := smallPrimeList_prod_pos z d
  have hdprod := smallPrimeList_prod_mul_largePrimeList_prod (z := z) hd
  rw [hlist] at hdprod
  simp only [List.prod_cons] at hdprod
  exact ⟨p, q, t * (r * L.prod), hp.2, hq.2, by
    have : r ≤ t * (r * L.prod) := by
      have hL : 0 < L.prod := by
        apply List.prod_pos
        intro a ha
        have haMem : a ∈ largePrimeList z d := by
          rw [hlist]
          simp [ha]
        exact (mem_largePrimeList haMem).1.pos
      have hmult : 0 < t * L.prod := Nat.mul_pos ht hL
      have hrle := Nat.le_mul_of_pos_right r hmult
      simpa [mul_assoc, mul_comm, mul_left_comm] using hrle
    omega, by
    dsimp [t]
    calc
      d = (smallPrimeList z d).prod * (p * (q * (r * L.prod))) := by
        simpa [mul_assoc] using hdprod.symm
      _ = p * q * ((smallPrimeList z d).prod * (r * L.prod)) := by ring⟩

/-- Every positive integer either has three factors above `z`, or is a bounded
small-prime kernel times at most two primes above `z`. -/
theorem threeLarge_or_smallKernel_twoPrimes
    {z d : ℕ} (hz : 1 < z) (hd : 0 < d) :
    HasThreeLargeFactors z d ∨
      ∃ t p q : ℕ,
        t ≤ z ^ 6 ∧
        (p = 1 ∨ (p.Prime ∧ z < p)) ∧
        (q = 1 ∨ (q.Prime ∧ z < q)) ∧
        d = t * p * q := by
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd
  by_cases hsmall : (smallPrimeList z d).prod ≤ z ^ 6
  · generalize hL : largePrimeList z d = L
    cases L with
    | nil =>
        right
        refine ⟨(smallPrimeList z d).prod, 1, 1, hsmall,
          Or.inl rfl, Or.inl rfl, ?_⟩
        have hp := smallPrimeList_prod_mul_largePrimeList_prod (z := z) hd0
        rw [hL] at hp
        simpa using hp.symm
    | cons p L =>
        cases L with
        | nil =>
            right
            have hpz := mem_largePrimeList (z := z) (d := d) (p := p) (by simp [hL])
            refine ⟨(smallPrimeList z d).prod, p, 1, hsmall,
              Or.inr hpz, Or.inl rfl, ?_⟩
            have hprod := smallPrimeList_prod_mul_largePrimeList_prod (z := z) hd0
            rw [hL] at hprod
            simpa using hprod.symm
        | cons q L =>
            cases L with
            | nil =>
                right
                have hpz := mem_largePrimeList (z := z) (d := d) (p := p)
                  (by simp [hL])
                have hqz := mem_largePrimeList (z := z) (d := d) (p := q)
                  (by simp [hL])
                refine ⟨(smallPrimeList z d).prod, p, q, hsmall,
                  Or.inr hpz, Or.inr hqz, ?_⟩
                have hprod := smallPrimeList_prod_mul_largePrimeList_prod (z := z) hd0
                rw [hL] at hprod
                simpa [mul_assoc] using hprod.symm
            | cons r L =>
                left
                exact threeLarge_of_largePrimeList_three hd0 hL
  · left
    exact threeLarge_of_smallKernel_gt hz hd0 (by omega)

/-- Allowed large-prime-or-one factors in the smooth exceptional forms. -/
def smoothPrimeOptions (n z : ℕ) : Finset ℕ :=
  {1} ∪ (Finset.Icc (z + 1) n.sqrt).filter Nat.Prime

/-- All bounded-kernel, at-most-two-large-prime forms. -/
def smoothExceptionalForms (n z : ℕ) : Finset ℕ :=
  ((((Finset.Icc 1 (z ^ 6)).product (smoothPrimeOptions n z)).product
      (smoothPrimeOptions n z)).filter fun u => u.1.1 * u.1.2 * u.2 ≤ n).image
    fun u => u.1.1 * u.1.2 * u.2

lemma mem_smoothPrimeOptions_iff {n z p : ℕ} :
    p ∈ smoothPrimeOptions n z ↔
      p = 1 ∨ (p.Prime ∧ z < p ∧ p ≤ n.sqrt) := by
  simp only [smoothPrimeOptions, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_filter, Finset.mem_Icc]
  aesop

/-- Members of `A` having three factors above `z`. -/
noncomputable def threeLargePart (A : Finset ℕ) (z : ℕ) : Finset ℕ := by
  classical
  exact A.filter fun d => HasThreeLargeFactors z d

/-- Every smooth element outside the three-large-factor class lies in the
explicit bounded-kernel exceptional family. -/
theorem smoothPart_subset_threeLarge_union_exceptional
    {A : Finset ℕ} {n z : ℕ} (hz : 1 < z)
    (hAint : A ⊆ Finset.Icc 1 n) :
    smoothPart A n ⊆
      threeLargePart A z ∪ smoothExceptionalForms n z := by
  classical
  intro d hd
  have hd' := Finset.mem_filter.mp hd
  have hdI := Finset.mem_Icc.mp (hAint hd'.1)
  have hdpos : 0 < d := hdI.1
  rcases threeLarge_or_smallKernel_twoPrimes hz hdpos with hthree | hform
  · apply Finset.mem_union_left
    unfold threeLargePart
    exact Finset.mem_filter.mpr ⟨hd'.1, hthree⟩
  · rcases hform with ⟨t, p, q, ht, hp, hq, hprod⟩
    have hppos : 0 < p := by
      rcases hp with rfl | hp
      · omega
      · exact hp.1.pos
    have hqpos : 0 < q := by
      rcases hq with rfl | hq
      · omega
      · exact hq.1.pos
    have htpos : 0 < t := by
      apply Nat.pos_of_ne_zero
      intro ht0
      rw [ht0] at hprod
      simp at hprod
      omega
    have hpdvd : p ∣ d := ⟨t * q, by rw [hprod]; ring⟩
    have hqdvd : q ∣ d := ⟨t * p, by rw [hprod]; ring⟩
    have hpopt : p ∈ smoothPrimeOptions n z := by
      rw [mem_smoothPrimeOptions_iff]
      rcases hp with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr ⟨hp.1, hp.2, hd'.2 p
          (Nat.mem_primesLE.mpr
            ⟨Nat.le_of_dvd hdpos hpdvd, hp.1⟩) hpdvd⟩
    have hqopt : q ∈ smoothPrimeOptions n z := by
      rw [mem_smoothPrimeOptions_iff]
      rcases hq with rfl | hq
      · exact Or.inl rfl
      · exact Or.inr ⟨hq.1, hq.2, hd'.2 q
          (Nat.mem_primesLE.mpr
            ⟨Nat.le_of_dvd hdpos hqdvd, hq.1⟩) hqdvd⟩
    apply Finset.mem_union_right
    unfold smoothExceptionalForms
    apply Finset.mem_image.mpr
    refine ⟨((t, p), q), Finset.mem_filter.mpr ⟨?_, ?_⟩, hprod.symm⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨htpos, ht⟩, hpopt⟩, hqopt⟩
    · change t * p * q ≤ n
      rw [← hprod]
      exact hdI.2

/-- Cardinal reduction of the smooth remainder to the cube-free and explicit
exceptional pieces. -/
theorem smoothPart_card_le_threeLarge_add_exceptional
    {A : Finset ℕ} {n z : ℕ} (hz : 1 < z)
    (hAint : A ⊆ Finset.Icc 1 n) :
    (smoothPart A n).card ≤
      (threeLargePart A z).card + (smoothExceptionalForms n z).card := by
  have hsub := smoothPart_subset_threeLarge_union_exceptional hz hAint
  exact (Finset.card_le_card hsub).trans
    (Finset.card_union_le (threeLargePart A z) (smoothExceptionalForms n z))

end Erdos796
