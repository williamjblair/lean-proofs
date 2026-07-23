import Research.Basic

namespace Erdos796

/-- Unordered pairs (with repetition) from a finite core. -/
def unorderedPairs (D : Finset ℕ) : Finset (ℕ × ℕ) :=
  (D ×ˢ D).filter fun x => x.1 ≤ x.2

/-- A finite multiplicative Sidon core: multiplication is injective on its
unordered pairs.  Equality of these cardinalities is equivalent to injectivity
because `Finset.image` can only decrease cardinality. -/
abbrev IsMulSidonCore (D : Finset ℕ) : Prop :=
  ((unorderedPairs D).image fun x => x.1 * x.2).card = (unorderedPairs D).card

/-- A machine-found set of composite core elements. -/
def extraCore1000 : Finset ℕ :=
  {8, 27, 30, 36, 98, 100, 125, 128, 225, 242, 338, 357, 456, 520, 578, 616,
   665, 672, 693, 722, 736, 812, 816, 836, 858, 880, 884, 891, 897, 910, 935, 966}

/-- The core consists of `1`, every prime, and the finite exceptional list.
The cutoff in the name only refers to the largest exceptional element. -/
abbrev infiniteCorePredicate (d : ℕ) : Prop :=
  d = 1 ∨ d.Prime ∨ d ∈ extraCore1000

/-- Its finite restriction through 1000, used for an exact certificate. -/
def sidonCore1000 : Finset ℕ :=
  (Finset.range 1001).filter infiniteCorePredicate

/-- Exact finite certificate: all unordered products from the certified core
are distinct.  Kernel reduction is delegated to the verified native evaluator. -/
theorem sidonCore1000_is_sidon : IsMulSidonCore sidonCore1000 := by
  native_decide

/-- The reciprocal weight of the added composite cores already exceeds 0.3. -/
theorem extraCore1000_reciprocal_gt_three_tenths :
    (3 : ℚ) / 10 < ∑ d ∈ extraCore1000, (1 : ℚ) / d := by
  native_decide

/-- Adjoining arbitrary primes larger than a bound to a positive finite Sidon
core below that bound preserves multiplicative Sidonicity. -/
theorem extend_sidon_core_by_large_primes
    (C : Finset ℕ) (K : ℕ)
    (hSidon : IsMulSidonCore C)
    (hpos : ∀ x ∈ C, 0 < x)
    (hbound : ∀ x ∈ C, x ≤ K)
    (a b c d : ℕ) (hab : a ≤ b) (hcd : c ≤ d)
    (ha : a ∈ C ∨ (K < a ∧ a.Prime))
    (hb : b ∈ C ∨ (K < b ∧ b.Prime))
    (hc : c ∈ C ∨ (K < c ∧ c.Prime))
    (hd : d ∈ C ∨ (K < d ∧ d.Prime))
    (heq : a * b = c * d) :
    (a, b) = (c, d) := by
  classical
  have large_dvd_eq {q z : ℕ} (hqK : K < q) (hqprime : q.Prime)
      (hz : z ∈ C ∨ (K < z ∧ z.Prime)) (hqz : q ∣ z) : q = z := by
    rcases hz with hzC | ⟨hzK, hzprime⟩
    · have hqle : q ≤ z := Nat.le_of_dvd (hpos z hzC) hqz
      exact (not_lt_of_ge (hbound z hzC) (lt_of_lt_of_le hqK hqle)).elim
    · rcases (Nat.dvd_prime hzprime).mp hqz with hq1 | hqz'
      · exact (hqprime.ne_one hq1).elim
      · exact hqz'
  rcases hb with hbC | ⟨hbK, hbprime⟩
  · have haC : a ∈ C := by
      rcases ha with haC | ⟨haK, _⟩
      · exact haC
      · have hble := hbound b hbC
        omega
    rcases hd with hdC | ⟨hdK, hdprime⟩
    · have hcC : c ∈ C := by
        rcases hc with hcC | ⟨hcK, _⟩
        · exact hcC
        · have hdle := hbound d hdC
          omega
      have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) (unorderedPairs C) :=
        Finset.card_image_iff.mp hSidon
      apply hinj
      · simp [unorderedPairs, haC, hbC, hab]
      · simp [unorderedPairs, hcC, hdC, hcd]
      · exact heq
    · have hddvd : d ∣ a * b := by
        rw [heq]
        simpa [Nat.mul_comm] using Nat.dvd_mul_right d c
      rcases hdprime.dvd_mul.mp hddvd with hda | hdb
      · have hdle : d ≤ a := Nat.le_of_dvd (hpos a haC) hda
        have hale := hbound a haC
        omega
      · have hdle : d ≤ b := Nat.le_of_dvd (hpos b hbC) hdb
        have hble := hbound b hbC
        omega
  · have hbdvd : b ∣ c * d := by
      rw [← heq]
      simpa [Nat.mul_comm] using Nat.dvd_mul_right b a
    rcases hbprime.dvd_mul.mp hbdvd with hbc | hbd
    · have hbc_eq : b = c := large_dvd_eq hbK hbprime hc hbc
      subst c
      have had : a = d := by
        apply Nat.mul_right_cancel hbprime.pos
        simpa [Nat.mul_comm] using heq
      subst d
      have hab' : b ≤ a := hcd
      have : a = b := Nat.le_antisymm hab hab'
      subst b
      rfl
    · have hbd_eq : b = d := large_dvd_eq hbK hbprime hd hbd
      subst d
      have hac : a = c := Nat.mul_right_cancel hbprime.pos heq
      subst c
      rfl

/-- The certified finite exceptional list can therefore be adjoined to `1`
and *all* primes while retaining unique unordered products. -/
theorem infiniteCore_mul_unique
    (a b c d : ℕ) (hab : a ≤ b) (hcd : c ≤ d)
    (ha : infiniteCorePredicate a) (hb : infiniteCorePredicate b)
    (hc : infiniteCorePredicate c) (hd : infiniteCorePredicate d)
    (heq : a * b = c * d) :
    (a, b) = (c, d) := by
  have hmem_iff (x : ℕ) :
      infiniteCorePredicate x ↔ x ∈ sidonCore1000 ∨ (1000 < x ∧ x.Prime) := by
    simp only [infiniteCorePredicate, sidonCore1000, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · intro hx
      rcases hx with rfl | hp | he
      · left
        norm_num
      · by_cases h : x < 1001
        · left
          exact ⟨h, Or.inr (Or.inl hp)⟩
        · right
          exact ⟨by omega, hp⟩
      · left
        have hxle : x < 1001 := by
          simp [extraCore1000] at he
          omega
        exact ⟨hxle, Or.inr (Or.inr he)⟩
    · intro hx
      rcases hx with ⟨_, hxpred⟩ | ⟨_, hp⟩
      · exact hxpred
      · exact Or.inr (Or.inl hp)
  have hposC : ∀ x ∈ sidonCore1000, 0 < x := by
    intro x hx
    have hxpred := (Finset.mem_filter.mp hx).2
    rcases hxpred with rfl | hp | he
    · norm_num
    · exact hp.pos
    · simp [extraCore1000] at he
      omega
  have hboundC : ∀ x ∈ sidonCore1000, x ≤ 1000 := by
    intro x hx
    exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hx).1)
  exact extend_sidon_core_by_large_primes sidonCore1000 1000
    sidonCore1000_is_sidon hposC hboundC a b c d hab hcd
    ((hmem_iff a).mp ha) ((hmem_iff b).mp hb)
    ((hmem_iff c).mp hc) ((hmem_iff d).mp hd) heq

end Erdos796
