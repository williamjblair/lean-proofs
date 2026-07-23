import Research.SmoothDyadic

namespace Erdos796

/-- Parameter triples whose products generate `smoothExceptionalForms`. -/
def smoothExceptionalTriples (n z : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((((Finset.Icc 1 (z ^ 6)).product (smoothPrimeOptions n z)).product
      (smoothPrimeOptions n z)).filter fun u => u.1.1 * u.1.2 * u.2 ≤ n)

@[simp] theorem smoothExceptionalForms_eq_image (n z : ℕ) :
    smoothExceptionalForms n z =
      (smoothExceptionalTriples n z).image fun u => u.1.1 * u.1.2 * u.2 := rfl

lemma smoothExceptionalForms_card_le_triples (n z : ℕ) :
    (smoothExceptionalForms n z).card ≤ (smoothExceptionalTriples n z).card := by
  rw [smoothExceptionalForms_eq_image]
  exact Finset.card_image_le

/-- The subcollection in which both optional factors are genuine primes. -/
def smoothExceptionalPrimeTriples (n z : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (smoothExceptionalTriples n z).filter fun u => u.1.2 ≠ 1 ∧ u.2 ≠ 1

/-- The subcollection in which at least one optional factor is `1`. -/
def smoothExceptionalDegenerateTriples (n z : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (smoothExceptionalTriples n z).filter fun u => u.1.2 = 1 ∨ u.2 = 1

lemma exceptionalTriples_card_eq_prime_add_degenerate (n z : ℕ) :
    (smoothExceptionalTriples n z).card =
      (smoothExceptionalPrimeTriples n z).card +
        (smoothExceptionalDegenerateTriples n z).card := by
  unfold smoothExceptionalPrimeTriples smoothExceptionalDegenerateTriples
  have h := Finset.card_filter_add_card_filter_not
    (s := smoothExceptionalTriples n z)
    (fun u : (ℕ × ℕ) × ℕ => u.1.2 ≠ 1 ∧ u.2 ≠ 1)
  simpa only [not_and_or, not_not] using h.symm

lemma smoothPrimeOptions_card_le (n z : ℕ) :
    (smoothPrimeOptions n z).card ≤ n.sqrt + 2 := by
  have hsub : smoothPrimeOptions n z ⊆ Finset.range (n.sqrt + 2) := by
    intro p hp
    rw [Finset.mem_range]
    rw [mem_smoothPrimeOptions_iff] at hp
    rcases hp with rfl | hp
    · omega
    · omega
  simpa using Finset.card_le_card hsub

/-- Degenerate exceptional triples have an elementary square-root bound; no
prime number theorem is needed for this negligible part. -/
theorem smoothExceptionalDegenerateTriples_card_le (n z : ℕ) :
    (smoothExceptionalDegenerateTriples n z).card ≤
      2 * z ^ 6 * (n.sqrt + 2) := by
  let Pone : Finset ((ℕ × ℕ) × ℕ) :=
    ((Finset.Icc 1 (z ^ 6)).product ({1} : Finset ℕ)).product
      (smoothPrimeOptions n z)
  let Qone : Finset ((ℕ × ℕ) × ℕ) :=
    ((Finset.Icc 1 (z ^ 6)).product (smoothPrimeOptions n z)).product
      ({1} : Finset ℕ)
  have hsub : smoothExceptionalDegenerateTriples n z ⊆ Pone ∪ Qone := by
    intro u hu
    have hu' := Finset.mem_filter.mp hu
    have hbase := Finset.mem_filter.mp hu'.1
    have hprod := Finset.mem_product.mp hbase.1
    have htp := Finset.mem_product.mp hprod.1
    rcases hu'.2 with hp | hq
    · apply Finset.mem_union_left
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨htp.1, by simpa [hp]⟩, hprod.2⟩
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨htp.1, htp.2⟩, by simpa [hq]⟩
  calc
    (smoothExceptionalDegenerateTriples n z).card ≤ (Pone ∪ Qone).card :=
      Finset.card_le_card hsub
    _ ≤ Pone.card + Qone.card := Finset.card_union_le _ _
    _ = 2 * (Finset.Icc 1 (z ^ 6)).card *
        (smoothPrimeOptions n z).card := by
      simp [Pone, Qone]
      ring
    _ ≤ 2 * z ^ 6 * (n.sqrt + 2) := by
      have hzcard : (Finset.Icc 1 (z ^ 6)).card = z ^ 6 := by simp
      rw [hzcard]
      gcongr
      exact smoothPrimeOptions_card_le n z

/-- Dyadic index pairs that can contain factors at most `n`. -/
def dyadicIndexSquare (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (Nat.log2 n + 1)).product
    (Finset.range (Nat.log2 n + 1))

@[simp] theorem dyadicIndexSquare_card (n : ℕ) :
    (dyadicIndexSquare n).card = (Nat.log2 n + 1) ^ 2 := by
  simp [dyadicIndexSquare, pow_two]

/-- A product box large enough to contain every exceptional triple whose two
prime factors lie in dyadic intervals `i,j`. -/
def smoothExceptionalDyadicContainer (n z i j : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  ((Finset.Icc 1 (min (z ^ 6) (n / 2 ^ (i + j)))).product
      (dyadicPrimes i)).product (dyadicPrimes j)

@[simp] theorem smoothExceptionalDyadicContainer_card (n z i j : ℕ) :
    (smoothExceptionalDyadicContainer n z i j).card =
      min (z ^ 6) (n / 2 ^ (i + j)) *
        (dyadicPrimes i).card * (dyadicPrimes j).card := by
  simp [smoothExceptionalDyadicContainer]

/-- Genuine-prime exceptional triples are covered by their dyadic product
containers. -/
theorem smoothExceptionalPrimeTriples_subset_dyadicContainers (n z : ℕ) :
    smoothExceptionalPrimeTriples n z ⊆
      (dyadicIndexSquare n).biUnion fun e =>
        smoothExceptionalDyadicContainer n z e.1 e.2 := by
  classical
  intro u hu
  have hu' := Finset.mem_filter.mp hu
  have hbase := Finset.mem_filter.mp hu'.1
  have hprod := Finset.mem_product.mp hbase.1
  have htp := Finset.mem_product.mp hprod.1
  let t := u.1.1
  let p := u.1.2
  let q := u.2
  have hpopt := htp.2
  have hqopt := hprod.2
  have hpdesc := (mem_smoothPrimeOptions_iff.mp hpopt)
  have hqdesc := (mem_smoothPrimeOptions_iff.mp hqopt)
  have hp : p.Prime ∧ z < p ∧ p ≤ n.sqrt := by
    rcases hpdesc with hp1 | hp
    · exact (hu'.2.1 hp1).elim
    · exact hp
  have hq : q.Prime ∧ z < q ∧ q ≤ n.sqrt := by
    rcases hqdesc with hq1 | hq
    · exact (hu'.2.2 hq1).elim
    · exact hq
  let i := Nat.log2 p
  let j := Nat.log2 q
  have hp0 : p ≠ 0 := hp.1.ne_zero
  have hq0 : q ≠ 0 := hq.1.ne_zero
  have hpi : p ∈ dyadicPrimes i := by
    exact Finset.mem_filter.mpr ⟨mem_dyadicInterval_log2 hp0, hp.1⟩
  have hqj : q ∈ dyadicPrimes j := by
    exact Finset.mem_filter.mpr ⟨mem_dyadicInterval_log2 hq0, hq.1⟩
  have hpn : p ≤ n := hp.2.2.trans (Nat.sqrt_le_self n)
  have hqn : q ≤ n := hq.2.2.trans (Nat.sqrt_le_self n)
  have hin : i ≤ Nat.log2 n := log2_mono_of_le hp0 hpn
  have hjn : j ≤ Nat.log2 n := log2_mono_of_le hq0 hqn
  apply Finset.mem_biUnion.mpr
  refine ⟨(i, j), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hin),
       Finset.mem_range.mpr (Nat.lt_succ_of_le hjn)⟩
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, hpi⟩, hqj⟩
    apply Finset.mem_Icc.mpr
    constructor
    · exact (Finset.mem_Icc.mp htp.1).1
    · apply le_min (Finset.mem_Icc.mp htp.1).2
      have hpLower : 2 ^ i ≤ p := (Finset.mem_Ico.mp
        (Finset.mem_filter.mp hpi).1).1
      have hqLower : 2 ^ j ≤ q := (Finset.mem_Ico.mp
        (Finset.mem_filter.mp hqj).1).1
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ (i + j))).2
      rw [pow_add]
      calc
        t * (2 ^ i * 2 ^ j) ≤ t * (p * q) := by gcongr
        _ = t * p * q := by ring
        _ ≤ n := hbase.2

/-- Exact finite dyadic majorant for all genuine-prime exceptional triples. -/
theorem smoothExceptionalPrimeTriples_card_le_dyadicSum (n z : ℕ) :
    (smoothExceptionalPrimeTriples n z).card ≤
      ∑ e ∈ dyadicIndexSquare n,
        min (z ^ 6) (n / 2 ^ (e.1 + e.2)) *
          (dyadicPrimes e.1).card * (dyadicPrimes e.2).card := by
  let U := (dyadicIndexSquare n).biUnion fun e =>
    smoothExceptionalDyadicContainer n z e.1 e.2
  have hsub : smoothExceptionalPrimeTriples n z ⊆ U :=
    smoothExceptionalPrimeTriples_subset_dyadicContainers n z
  calc
    (smoothExceptionalPrimeTriples n z).card ≤ U.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ e ∈ dyadicIndexSquare n,
        (smoothExceptionalDyadicContainer n z e.1 e.2).card :=
      Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      exact smoothExceptionalDyadicContainer_card n z e.1 e.2

/-- Dyadic indices compatible with a prime in `(2^s,sqrt n]`. -/
def smoothPrimeIndexRange (n s : ℕ) : Finset ℕ :=
  Finset.Icc s (Nat.log2 n / 2)

/-- The square of the relevant prime-index range. -/
def smoothPrimeIndexSquare (n s : ℕ) : Finset (ℕ × ℕ) :=
  (smoothPrimeIndexRange n s).product (smoothPrimeIndexRange n s)

lemma log2_le_half_of_le_sqrt {p n : ℕ} (hp0 : p ≠ 0)
    (hp : p ≤ n.sqrt) : Nat.log2 p ≤ Nat.log2 n / 2 := by
  let i := Nat.log2 p
  have hpowp : 2 ^ i ≤ p := by
    dsimp [i]
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hp0
  have hpSq : p * p ≤ n :=
    (Nat.mul_le_mul hp hp).trans (Nat.sqrt_le n)
  have hpowSq : 2 ^ (2 * i) ≤ n := by
    rw [show 2 * i = i + i by omega, pow_add]
    exact (Nat.mul_self_le_mul_self hpowp).trans hpSq
  have hlog := log2_mono_of_le (show 2 ^ (2 * i) ≠ 0 by positivity) hpowSq
  rw [Nat.log2_two_pow] at hlog
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  simpa [mul_comm] using hlog

/-- At the dyadic threshold `z=2^s`, the prime-triple cover only uses indices
between `s` and `(log₂ n)/2`. -/
theorem smoothExceptionalPrimeTriples_subset_relevantContainers (n s : ℕ) :
    smoothExceptionalPrimeTriples n (2 ^ s) ⊆
      (smoothPrimeIndexSquare n s).biUnion fun e =>
        smoothExceptionalDyadicContainer n (2 ^ s) e.1 e.2 := by
  classical
  intro u hu
  have hu' := Finset.mem_filter.mp hu
  have hbase := Finset.mem_filter.mp hu'.1
  have hprod := Finset.mem_product.mp hbase.1
  have htp := Finset.mem_product.mp hprod.1
  let t := u.1.1
  let p := u.1.2
  let q := u.2
  have hpdesc := mem_smoothPrimeOptions_iff.mp htp.2
  have hqdesc := mem_smoothPrimeOptions_iff.mp hprod.2
  have hp : p.Prime ∧ 2 ^ s < p ∧ p ≤ n.sqrt := by
    rcases hpdesc with hp1 | hp
    · exact (hu'.2.1 hp1).elim
    · exact hp
  have hq : q.Prime ∧ 2 ^ s < q ∧ q ≤ n.sqrt := by
    rcases hqdesc with hq1 | hq
    · exact (hu'.2.2 hq1).elim
    · exact hq
  let i := Nat.log2 p
  let j := Nat.log2 q
  have hp0 : p ≠ 0 := hp.1.ne_zero
  have hq0 : q ≠ 0 := hq.1.ne_zero
  have hpi : p ∈ dyadicPrimes i :=
    Finset.mem_filter.mpr ⟨mem_dyadicInterval_log2 hp0, hp.1⟩
  have hqj : q ∈ dyadicPrimes j :=
    Finset.mem_filter.mpr ⟨mem_dyadicInterval_log2 hq0, hq.1⟩
  have hsi : s ≤ i := by
    have hmono := log2_mono_of_le
      (show 2 ^ s ≠ 0 by positivity) (Nat.le_of_lt hp.2.1)
    simpa [i] using hmono
  have hsj : s ≤ j := by
    have hmono := log2_mono_of_le
      (show 2 ^ s ≠ 0 by positivity) (Nat.le_of_lt hq.2.1)
    simpa [j] using hmono
  have hin : i ≤ Nat.log2 n / 2 := log2_le_half_of_le_sqrt hp0 hp.2.2
  have hjn : j ≤ Nat.log2 n / 2 := log2_le_half_of_le_sqrt hq0 hq.2.2
  apply Finset.mem_biUnion.mpr
  refine ⟨(i, j), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hsi, hin⟩,
       Finset.mem_Icc.mpr ⟨hsj, hjn⟩⟩
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, hpi⟩, hqj⟩
    apply Finset.mem_Icc.mpr
    constructor
    · exact (Finset.mem_Icc.mp htp.1).1
    · apply le_min (Finset.mem_Icc.mp htp.1).2
      have hpLower : 2 ^ i ≤ p := (Finset.mem_Ico.mp
        (Finset.mem_filter.mp hpi).1).1
      have hqLower : 2 ^ j ≤ q := (Finset.mem_Ico.mp
        (Finset.mem_filter.mp hqj).1).1
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ (i + j))).2
      rw [pow_add]
      calc
        t * (2 ^ i * 2 ^ j) ≤ t * (p * q) := by gcongr
        _ = t * p * q := by ring
        _ ≤ n := hbase.2

/-- Specialized finite dyadic sum at a dyadic threshold. -/
theorem smoothExceptionalPrimeTriples_card_le_relevantSum (n s : ℕ) :
    (smoothExceptionalPrimeTriples n (2 ^ s)).card ≤
      ∑ e ∈ smoothPrimeIndexSquare n s,
        min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) *
          (dyadicPrimes e.1).card * (dyadicPrimes e.2).card := by
  let U := (smoothPrimeIndexSquare n s).biUnion fun e =>
    smoothExceptionalDyadicContainer n (2 ^ s) e.1 e.2
  have hsub : smoothExceptionalPrimeTriples n (2 ^ s) ⊆ U :=
    smoothExceptionalPrimeTriples_subset_relevantContainers n s
  calc
    (smoothExceptionalPrimeTriples n (2 ^ s)).card ≤ U.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ e ∈ smoothPrimeIndexSquare n s,
        (smoothExceptionalDyadicContainer n (2 ^ s) e.1 e.2).card :=
      Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      exact smoothExceptionalDyadicContainer_card n (2 ^ s) e.1 e.2

/-- Combined finite reduction of the exceptional family to a dyadic
prime-pair sum plus a negligible degenerate term. -/
theorem smoothExceptionalForms_card_le_dyadicSum (n z : ℕ) :
    (smoothExceptionalForms n z).card ≤
      (∑ e ∈ dyadicIndexSquare n,
        min (z ^ 6) (n / 2 ^ (e.1 + e.2)) *
          (dyadicPrimes e.1).card * (dyadicPrimes e.2).card) +
        2 * z ^ 6 * (n.sqrt + 2) := by
  calc
    (smoothExceptionalForms n z).card ≤
        (smoothExceptionalTriples n z).card :=
      smoothExceptionalForms_card_le_triples n z
    _ = (smoothExceptionalPrimeTriples n z).card +
        (smoothExceptionalDegenerateTriples n z).card :=
      exceptionalTriples_card_eq_prime_add_degenerate n z
    _ ≤ _ := Nat.add_le_add
      (smoothExceptionalPrimeTriples_card_le_dyadicSum n z)
      (smoothExceptionalDegenerateTriples_card_le n z)

/-- Relevant-index version of the combined bound at threshold `2^s`. -/
theorem smoothExceptionalForms_card_le_relevantSum (n s : ℕ) :
    (smoothExceptionalForms n (2 ^ s)).card ≤
      (∑ e ∈ smoothPrimeIndexSquare n s,
        min ((2 ^ s) ^ 6) (n / 2 ^ (e.1 + e.2)) *
          (dyadicPrimes e.1).card * (dyadicPrimes e.2).card) +
        2 * (2 ^ s) ^ 6 * (n.sqrt + 2) := by
  calc
    (smoothExceptionalForms n (2 ^ s)).card ≤
        (smoothExceptionalTriples n (2 ^ s)).card :=
      smoothExceptionalForms_card_le_triples n (2 ^ s)
    _ = (smoothExceptionalPrimeTriples n (2 ^ s)).card +
        (smoothExceptionalDegenerateTriples n (2 ^ s)).card :=
      exceptionalTriples_card_eq_prime_add_degenerate n (2 ^ s)
    _ ≤ _ := Nat.add_le_add
      (smoothExceptionalPrimeTriples_card_le_relevantSum n s)
      (smoothExceptionalDegenerateTriples_card_le n (2 ^ s))

end Erdos796
