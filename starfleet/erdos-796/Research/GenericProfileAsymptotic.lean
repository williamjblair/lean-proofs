import Research.VariationalLimit
import Research.SemiprimeAsymptotic

namespace Erdos796

open Filter Topology

/-- Labels whose available core capacity is exactly `c`. -/
def exactCapacityLabels (n c : ℕ) : Finset ℕ :=
  (sqrtPrimeLabels n).filter fun q => n / q = c

/-- Exact-capacity labels are the difference of two nested at-least-capacity
layers. -/
theorem exactCapacityLabels_eq_sdiff (n c : ℕ) :
    exactCapacityLabels n c = capacityLabels n c \ capacityLabels n (c + 1) := by
  ext q
  simp only [exactCapacityLabels, capacityLabels, Finset.mem_filter,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨hq, heq⟩
    exact ⟨⟨hq, by omega⟩, by omega⟩
  · rintro ⟨⟨hq, hle⟩, hnot⟩
    have hnle : ¬c + 1 ≤ n / q := fun h => hnot ⟨hq, h⟩
    exact ⟨hq, by omega⟩

lemma capacityLabels_succ_subset (n c : ℕ) :
    capacityLabels n (c + 1) ⊆ capacityLabels n c := by
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hq'.1, by omega⟩

/-- Exact capacity-layer cardinality is a difference. -/
theorem exactCapacityLabels_card (n c : ℕ) :
    (exactCapacityLabels n c).card =
      (capacityLabels n c).card - (capacityLabels n (c + 1)).card := by
  rw [exactCapacityLabels_eq_sdiff]
  exact Finset.card_sdiff_of_subset (capacityLabels_succ_subset n c)

/-- Every fixed positive exact-capacity layer has mass
`1/c - 1/(c+1) = 1/(c(c+1))`. -/
theorem tendsto_exactCapacityLabels_card_div_normalization
    (c : ℕ) (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      ((exactCapacityLabels n c).card : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds ((1 : ℝ) / c - (1 : ℝ) / (c + 1))) := by
  have h := (tendsto_capacityLabels_card_div_normalization c hc).sub
    (tendsto_capacityLabels_card_div_normalization (c + 1) (by omega))
  have h' : Tendsto (fun n : ℕ =>
      ((capacityLabels n c).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        ((capacityLabels n (c + 1)).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds ((1 : ℝ) / c - (1 : ℝ) / (c + 1))) := by
    simpa using h
  apply h'.congr'
  filter_upwards with n
  rw [exactCapacityLabels_card, Nat.cast_sub
    (Finset.card_le_card (capacityLabels_succ_subset n c))]
  ring

namespace FiberProfile

/-- Capacity index selected by the capped finite profile. -/
def capacityIndex {R : ℕ} (P : FiberProfile R) (J : ℕ) : Fin R :=
  ⟨min (J - 1) (R - 1), by have hR := P.posR; omega⟩

@[simp] theorem base_eq_fiber_capacityIndex {R : ℕ}
    (P : FiberProfile R) (J : ℕ) :
    P.base J = P.fiber (P.capacityIndex J) := rfl

/-- Prime labels selecting one given finite-profile capacity index. -/
def capacityClassLabels {R : ℕ} (P : FiberProfile R)
    (n : ℕ) (i : Fin R) : Finset ℕ :=
  (sqrtPrimeLabels n).filter fun q => P.capacityIndex (n / q) = i

/-- Before the terminal index, a profile capacity class is an exact-capacity
layer. -/
theorem capacityClassLabels_eq_exact {R : ℕ} (P : FiberProfile R)
    (n : ℕ) (i : Fin R) (hi : i.val + 1 < R) :
    P.capacityClassLabels n i = exactCapacityLabels n (i.val + 1) := by
  ext q
  simp only [capacityClassLabels, exactCapacityLabels, Finset.mem_filter]
  constructor
  · rintro ⟨hq, heq⟩
    have hq' := Finset.mem_filter.mp hq
    have hJ : 0 < n / q := Nat.div_pos
      (Finset.mem_Icc.mp hq'.1).2 hq'.2.pos
    have hval := congrArg Fin.val heq
    dsimp [capacityIndex] at hval
    exact ⟨hq, by omega⟩
  · rintro ⟨hq, hJ⟩
    have heq : P.capacityIndex (n / q) = i := by
      apply Fin.ext
      dsimp [capacityIndex]
      omega
    exact ⟨hq, heq⟩

/-- The terminal profile capacity class is the at-least-`R` layer. -/
theorem capacityClassLabels_eq_terminal {R : ℕ} (P : FiberProfile R)
    (n : ℕ) (i : Fin R) (hi : i.val + 1 = R) :
    P.capacityClassLabels n i = capacityLabels n R := by
  ext q
  simp only [capacityClassLabels, capacityLabels, Finset.mem_filter]
  constructor
  · rintro ⟨hq, heq⟩
    have hq' := Finset.mem_filter.mp hq
    have hJ : 0 < n / q := Nat.div_pos
      (Finset.mem_Icc.mp hq'.1).2 hq'.2.pos
    have hval := congrArg Fin.val heq
    dsimp [capacityIndex] at hval
    exact ⟨hq, by omega⟩
  · rintro ⟨hq, hJ⟩
    have heq : P.capacityIndex (n / q) = i := by
      apply Fin.ext
      dsimp [capacityIndex]
      omega
    exact ⟨hq, heq⟩

/-- Each profile capacity class has the layer weight used by the finite
variational objective. -/
theorem tendsto_capacityClassLabels_card_div_normalization {R : ℕ}
    (P : FiberProfile R) (i : Fin R) :
    Tendsto (fun n : ℕ =>
      ((P.capacityClassLabels n i).card : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds (profileLayerWeight i)) := by
  by_cases hi : i.val + 1 = R
  · rw [show profileLayerWeight i = (1 : ℝ) / R by
      simp [profileLayerWeight, hi]]
    have h := tendsto_capacityLabels_card_div_normalization R P.posR
    simpa [P.capacityClassLabels_eq_terminal _ i hi] using h
  · have hlt : i.val + 1 < R := by omega
    rw [show profileLayerWeight i =
        (1 : ℝ) / (((i.val + 1 : ℕ) : ℝ) * ((i.val + 2 : ℕ) : ℝ)) by
      simp [profileLayerWeight, hi]]
    have h := tendsto_exactCapacityLabels_card_div_normalization
      (i.val + 1) (by omega)
    have h' : Tendsto (fun n : ℕ =>
        ((P.capacityClassLabels n i).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop
        (nhds ((1 : ℝ) / ((i.val + 1 : ℕ) : ℝ) -
          (1 : ℝ) / (((i.val + 1 : ℕ) : ℝ) + 1))) := by
      apply h.congr'
      filter_upwards with n
      rw [P.capacityClassLabels_eq_exact n i hlt]
    convert h' using 1
    congr 1
    have h1 : (0 : ℝ) < i.val + 1 := by positivity
    have h2 : (0 : ℝ) < i.val + 2 := by positivity
    norm_num
    field_simp
    ring

lemma profileLayerWeight_eq_base_add_terminal {R : ℕ}
    (P : FiberProfile R) (i : Fin R) :
    profileLayerWeight i =
      (1 : ℝ) / (((i.val + 1 : ℕ) : ℝ) * ((i.val + 2 : ℕ) : ℝ)) +
      if i.val + 1 = R then (1 : ℝ) / (R + 1) else 0 := by
  by_cases hi : i.val + 1 = R
  · rw [if_pos hi]
    simp [profileLayerWeight, hi]
    have hR : (0 : ℝ) < R := by exact_mod_cast P.posR
    have hiR : (i.val : ℝ) + 1 = R := by exact_mod_cast hi
    field_simp
    nlinarith
  · rw [if_neg hi]
    simp [profileLayerWeight, hi]

/-- The telescoping definition of `beta` equals the direct capacity-layer
weight sum. -/
theorem beta_eq_weighted {R : ℕ} (P : FiberProfile R) :
    P.beta = ∑ i : Fin R,
      profileLayerWeight i * (P.fiber i).card := by
  let last : Fin R := ⟨R - 1, by have hR := P.posR; omega⟩
  have hiff (i : Fin R) : i.val + 1 = R ↔ i = last := by
    constructor
    · intro h
      apply Fin.ext
      dsimp [last]
      omega
    · intro h
      subst i
      dsimp [last]
      have hR := P.posR
      omega
  simp_rw [profileLayerWeight_eq_base_add_terminal P]
  simp_rw [hiff, add_mul]
  rw [Finset.sum_add_distrib]
  have hterm :
      (∑ i : Fin R,
        (if i = last then (1 : ℝ) / (R + 1) else 0) *
          (P.fiber i).card) =
        ((P.fiber last).card : ℝ) / (R + 1) := by
    simp
    ring
  rw [hterm]
  unfold FiberProfile.beta
  dsimp [last]
  have hbase :
      (∑ i : Fin R, ((P.fiber i).card : ℝ) /
        (((i.val + 1 : ℕ) : ℝ) * ((i.val + 2 : ℕ) : ℝ))) =
      ∑ i : Fin R,
        ((1 : ℝ) / (((i.val + 1 : ℕ) : ℝ) * ((i.val + 2 : ℕ) : ℝ))) *
          (P.fiber i).card := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hbase]

/-- Total incidence count contributed by the finite base types. -/
def baseCount {R : ℕ} (P : FiberProfile R) (n : ℕ) : ℕ :=
  ∑ q ∈ sqrtPrimeLabels n, (P.base (n / q)).card

/-- Exact capacity-class decomposition of the finite base incidence count. -/
theorem baseCount_eq_capacityClasses {R : ℕ} (P : FiberProfile R) (n : ℕ) :
    P.baseCount n = ∑ i : Fin R,
      (P.fiber i).card * (P.capacityClassLabels n i).card := by
  unfold baseCount
  calc
    _ = ∑ q ∈ sqrtPrimeLabels n, ∑ i : Fin R,
        if P.capacityIndex (n / q) = i then (P.fiber i).card else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      simp
    _ = ∑ i : Fin R, ∑ q ∈ sqrtPrimeLabels n,
        if P.capacityIndex (n / q) = i then (P.fiber i).card else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [capacityClassLabels, Finset.card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> simp_all

/-- The finite base incidence count of every compatible profile has normalized
limit equal to its variational objective. -/
theorem tendsto_baseCount_div_normalization {R : ℕ} (P : FiberProfile R) :
    Tendsto (fun n : ℕ =>
      (P.baseCount n : ℝ) / ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds P.beta) := by
  have hi : ∀ i : Fin R, Tendsto (fun n : ℕ =>
      ((P.fiber i).card : ℝ) *
        (((P.capacityClassLabels n i).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))) atTop
      (nhds (((P.fiber i).card : ℝ) * profileLayerWeight i)) := by
    intro i
    exact (P.tendsto_capacityClassLabels_card_div_normalization i).const_mul _
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hsum' : Tendsto (fun n : ℕ =>
      ∑ i : Fin R, ((P.fiber i).card : ℝ) *
        (((P.capacityClassLabels n i).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))) atTop
      (nhds P.beta) := by
    convert hsum using 1
    rw [P.beta_eq_weighted]
    apply congrArg nhds
    apply Finset.sum_congr rfl
    intro i hi
    ring
  apply hsum'.congr'
  filter_upwards with n
  rw [P.baseCount_eq_capacityClasses]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end FiberProfile

/-- Contribution from the finitely many primes through an arbitrary fixed
cutoff. -/
def smallPrimeCorrection (R n : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE R,
    (Nat.primeCounting (n / p) - Nat.primeCounting n.sqrt)

/-- Fixed small-prime correction at an arbitrary cutoff. -/
theorem tendsto_smallPrimeCorrection_div_normalization (R : ℕ) :
    Tendsto (fun n : ℕ =>
      (smallPrimeCorrection R n : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds (primeMass R)) := by
  have hp : ∀ p ∈ Nat.primesLE R, Tendsto (fun n : ℕ =>
      (Nat.primeCounting (n / p) - Nat.primeCounting n.sqrt : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds ((1 : ℝ) / p)) := by
    intro p hp
    exact tendsto_primeCounting_sub_sqrt_div_normalization p
      (Nat.prime_of_mem_primesLE hp).pos
  have hsum := tendsto_finsetSum (Nat.primesLE R) hp
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (R * R)] with n hn
  have hR : R ≤ n.sqrt := Nat.le_sqrt.mpr hn
  unfold smallPrimeCorrection
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Nat.mem_primesLE.mp hp
  have hle : Nat.primeCounting n.sqrt ≤ Nat.primeCounting (n / p) := by
    apply Nat.monotone_primeCounting
    apply (Nat.le_div_iff_mul_le hp'.2.pos).2
    calc
      n.sqrt * p ≤ n.sqrt * R := Nat.mul_le_mul_left _ hp'.1
      _ ≤ n.sqrt * n.sqrt := Nat.mul_le_mul_left _ hR
      _ ≤ n := Nat.sqrt_le n
  rw [Nat.cast_sub hle]

/-- Prime-tail count in the smaller-prime orientation at cutoff `R`. -/
def profilePrimeTailSmall (R n : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE n.sqrt \ Nat.primesLE R,
    (Nat.primeCounting (n / p) - Nat.primeCounting n.sqrt)

/-- The large-semiprime count splits at every fixed cutoff. -/
theorem largeSemiprimeCount_eq_small_add_tail_generic
    (R n : ℕ) (hn : R * R ≤ n) :
    largeSemiprimeCount n = smallPrimeCorrection R n +
      profilePrimeTailSmall R n := by
  have hR : R ≤ n.sqrt := Nat.le_sqrt.mpr hn
  have hsub : Nat.primesLE R ⊆ Nat.primesLE n.sqrt := Nat.primesLE_mono hR
  have h := Finset.sum_sdiff (f := fun p =>
    Nat.primeCounting (n / p) - Nat.primeCounting n.sqrt) hsub
  unfold largeSemiprimeCount smallPrimeCorrection profilePrimeTailSmall
  omega

/-- The smaller-prime tail has residual coefficient `M-primeMass R`. -/
theorem tendsto_profilePrimeTailSmall_residual (R : ℕ) :
    Tendsto (fun n : ℕ =>
      (profilePrimeTailSmall R n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ))) atTop
      (nhds (Mertens.M - primeMass R)) := by
  have h := tendsto_largeSemiprimeCount_residual.sub
    (tendsto_smallPrimeCorrection_div_normalization R)
  have h' : Tendsto (fun n : ℕ =>
      ((largeSemiprimeCount n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ))) -
      (smallPrimeCorrection R n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds (Mertens.M - primeMass R)) := h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop (R * R)] with n hn
  rw [largeSemiprimeCount_eq_small_add_tail_generic R n hn]
  push_cast
  ring

/-- Literal prime-tail incidence count in a profile construction. -/
def profileTailCount (R n : ℕ) : ℕ :=
  ∑ q ∈ sqrtPrimeLabels n,
    ((Finset.Icc (R + 1) (n / q)).filter Nat.Prime).card

/-- Common pair finset used to double-count the generic tail. -/
def profilePrimePairs (R n : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.Icc (R + 1) n.sqrt).filter Nat.Prime).product
    (sqrtPrimeLabels n)).filter fun z => z.1 * z.2 ≤ n

lemma profileSmallPrimes_eq (R n : ℕ) :
    Nat.primesLE n.sqrt \ Nat.primesLE R =
      (Finset.Icc (R + 1) n.sqrt).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hps, hp⟩, hnot⟩
    have hpR : R + 1 ≤ p := by
      by_contra h
      apply hnot
      exact ⟨by omega, hp⟩
    exact ⟨⟨hpR, hps⟩, hp⟩
  · rintro ⟨⟨hpR, hps⟩, hp⟩
    exact ⟨⟨hps, hp⟩, by omega⟩

/-- First orientation of the generic tail double count. -/
theorem profilePrimePairs_card_eq_small (R n : ℕ) :
    (profilePrimePairs R n).card = profilePrimeTailSmall R n := by
  unfold profilePrimePairs profilePrimeTailSmall
  rw [profileSmallPrimes_eq]
  rw [Finset.card_filter]
  change (∑ z ∈ ((Finset.Icc (R + 1) n.sqrt).filter Nat.Prime).product
      (sqrtPrimeLabels n), if z.1 * z.2 ≤ n then 1 else 0) = _
  rw [show (∑ z ∈ ((Finset.Icc (R + 1) n.sqrt).filter Nat.Prime).product
      (sqrtPrimeLabels n), if z.1 * z.2 ≤ n then 1 else 0) =
      ∑ p ∈ (Finset.Icc (R + 1) n.sqrt).filter Nat.Prime,
        ∑ q ∈ sqrtPrimeLabels n, if p * q ≤ n then 1 else 0 from
      Finset.sum_product _ _ _]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpI := Finset.mem_Icc.mp hp'.1
  have hppos : 0 < p := hp'.2.pos
  have hs : n.sqrt ≤ n / p := by
    apply (Nat.le_div_iff_mul_le hppos).2
    calc
      n.sqrt * p ≤ n.sqrt * n.sqrt := Nat.mul_le_mul_left _ hpI.2
      _ ≤ n := Nat.sqrt_le n
  have hfiber : (sqrtPrimeLabels n).filter (fun q => p * q ≤ n) =
      Nat.primesLE (n / p) \ Nat.primesLE n.sqrt := by
    ext q
    simp only [Finset.mem_filter, sqrtPrimeLabels, Finset.mem_Icc,
      Nat.mem_primesLE, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨⟨hqlow, hqn⟩, hqprime⟩, hpq⟩
      have hqdiv : q ≤ n / p := (Nat.le_div_iff_mul_le hppos).2 (by
        simpa [Nat.mul_comm] using hpq)
      exact ⟨⟨hqdiv, hqprime⟩, by omega⟩
    · rintro ⟨⟨hqdiv, hqprime⟩, hnot⟩
      have hpq : p * q ≤ n := by
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hppos).1 hqdiv
      have hqn : q ≤ n := le_trans hqdiv (Nat.div_le_self n p)
      have hqlow : n.sqrt + 1 ≤ q := by
        simp only [not_and_or, not_le] at hnot
        rcases hnot with h | h
        · omega
        · exact (h hqprime).elim
      exact ⟨⟨⟨hqlow, hqn⟩, hqprime⟩, hpq⟩
  rw [← Finset.card_filter, hfiber]
  rw [Finset.card_sdiff_of_subset (Nat.primesLE_mono hs)]
  simp

/-- Second orientation of the generic tail double count. -/
theorem profilePrimePairs_card_eq_tail (R n : ℕ) :
    (profilePrimePairs R n).card = profileTailCount R n := by
  unfold profilePrimePairs profileTailCount
  rw [Finset.card_filter]
  change (∑ z ∈ ((Finset.Icc (R + 1) n.sqrt).filter Nat.Prime).product
      (sqrtPrimeLabels n), if z.1 * z.2 ≤ n then 1 else 0) = _
  rw [show (∑ z ∈ ((Finset.Icc (R + 1) n.sqrt).filter Nat.Prime).product
      (sqrtPrimeLabels n), if z.1 * z.2 ≤ n then 1 else 0) =
      ∑ p ∈ (Finset.Icc (R + 1) n.sqrt).filter Nat.Prime,
        ∑ q ∈ sqrtPrimeLabels n, if p * q ≤ n then 1 else 0 from
      Finset.sum_product _ _ _]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hqpos : 0 < q := hq'.2.pos
  have hcap : n / q ≤ n.sqrt := div_label_le_sqrt hq
  have hfiber : ((Finset.Icc (R + 1) n.sqrt).filter Nat.Prime).filter
      (fun p => p * q ≤ n) =
      (Finset.Icc (R + 1) (n / q)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hpR, hps⟩, hpprime⟩, hpq⟩
      exact ⟨⟨hpR, (Nat.le_div_iff_mul_le hqpos).2 hpq⟩, hpprime⟩
    · rintro ⟨⟨hpR, hpdiv⟩, hpprime⟩
      exact ⟨⟨⟨hpR, le_trans hpdiv hcap⟩, hpprime⟩,
        (Nat.le_div_iff_mul_le hqpos).1 hpdiv⟩
  rw [← Finset.card_filter, hfiber]

/-- The literal and smaller-prime tail counts agree. -/
theorem profileTailCount_eq_small (R n : ℕ) :
    profileTailCount R n = profilePrimeTailSmall R n := by
  rw [← profilePrimePairs_card_eq_tail,
    profilePrimePairs_card_eq_small]

/-- Generic fixed-cutoff profile-tail asymptotic. -/
theorem tendsto_profileTailCount_residual (R : ℕ) :
    Tendsto (fun n : ℕ =>
      (profileTailCount R n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ))) atTop
      (nhds (Mertens.M - primeMass R)) := by
  simpa only [profileTailCount_eq_small] using
    tendsto_profilePrimeTailSmall_residual R

namespace FiberProfile

/-- Exact generic profile-construction split into finite base and prime tail. -/
theorem construction_card_decomposition_generic {R : ℕ}
    (P : FiberProfile R) (n : ℕ) :
    (P.construction n).card = P.baseCount n + profileTailCount R n := by
  unfold baseCount profileTailCount
  exact P.construction_card_decomposition n

/-- Residual of an arbitrary finite-profile construction. -/
noncomputable def constructionResidual {R : ℕ}
    (P : FiberProfile R) (n : ℕ) : ℝ :=
  ((P.construction n).card : ℝ) /
      ((n : ℝ) / Real.log (n : ℝ)) -
    Real.log (Real.log (n : ℝ))

/-- Every compatible finite profile realizes coefficient `M + gamma(P)`. -/
theorem tendsto_constructionResidual {R : ℕ} (P : FiberProfile R) :
    Tendsto P.constructionResidual atTop
      (nhds (Mertens.M + P.gamma)) := by
  have h := P.tendsto_baseCount_div_normalization.add
    (tendsto_profileTailCount_residual R)
  have h' : Tendsto (fun n : ℕ =>
      (P.baseCount n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) +
        ((profileTailCount R n : ℝ) /
            ((n : ℝ) / Real.log (n : ℝ)) -
          Real.log (Real.log (n : ℝ)))) atTop
      (nhds (Mertens.M + P.gamma)) := by
    convert h using 1
    unfold FiberProfile.gamma
    ring
  apply h'.congr'
  filter_upwards with n
  unfold constructionResidual
  rw [P.construction_card_decomposition_generic]
  push_cast
  ring

/-- Every generic profile residual is eventually below the extremal residual. -/
theorem eventually_constructionResidual_le_normalizedError {R : ℕ}
    (P : FiberProfile R) :
    ∀ᶠ n : ℕ in atTop, P.constructionResidual n ≤ normalizedError n := by
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := div_pos hnR hlog
  have hcard : ((P.construction n).card : ℝ) ≤ (g 3 n : ℝ) := by
    exact_mod_cast P.construction_card_le_g n
  unfold constructionResidual normalizedError
  calc
    ((P.construction n).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ)) =
      (((P.construction n).card : ℝ) -
          (n : ℝ) * Real.log (Real.log (n : ℝ)) /
            Real.log (n : ℝ)) /
        ((n : ℝ) / Real.log (n : ℝ)) := by field_simp
    _ ≤ ((g 3 n : ℝ) -
          (n : ℝ) * Real.log (Real.log (n : ℝ)) /
            Real.log (n : ℝ)) /
        ((n : ℝ) / Real.log (n : ℝ)) := by
      exact div_le_div_of_nonneg_right (sub_le_sub_right hcard _) hden.le

/-- Every finite-profile coefficient is an eventual strict lower bound up to
an arbitrary positive epsilon. -/
theorem eventually_profileCoefficient_sub_lt_normalizedError {R : ℕ}
    (P : FiberProfile R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Mertens.M + P.gamma - ε < normalizedError n := by
  have hnear := P.tendsto_constructionResidual.eventually
    (lt_mem_nhds (sub_lt_self _ hε))
  filter_upwards [hnear, P.eventually_constructionResidual_le_normalizedError]
      with n hn hle
  exact hn.trans_le hle

end FiberProfile

/-- The full finite variational limit is attained from below by admissible
constructions, in the eventual-epsilon sense needed for the extremal lower
bound. -/
theorem eventually_variationalLimitCoefficient_sub_lt_normalizedError
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Mertens.M + variationalLimit - ε < normalizedError n := by
  have hhalf : 0 < ε / 2 := by positivity
  have hexR : ∃ R : ℕ,
      variationalLimit - ε / 2 < optimalGamma (R + 1) := by
    unfold variationalLimit
    exact (lt_ciSup_iff optimalGammaSucc_range_bddAbove).mp
      (sub_lt_self _ hhalf)
  rcases hexR with ⟨R, hR⟩
  have hexP : ∃ x ∈ Set.range
      (fun P : FiberProfile (R + 1) => P.gamma),
      optimalGamma (R + 1) - ε / 2 < x := by
    exact (lt_csSup_iff (gammaRange_bddAbove (R + 1))
      (gammaRange_nonempty (R + 1) (by omega))).mp
      (sub_lt_self _ hhalf)
  rcases hexP with ⟨x, ⟨P, rfl⟩, hP⟩
  have hcoef : Mertens.M + variationalLimit - ε <
      Mertens.M + P.gamma := by linarith
  have hnear := P.tendsto_constructionResidual.eventually (lt_mem_nhds hcoef)
  filter_upwards [hnear, P.eventually_constructionResidual_le_normalizedError]
      with n hn hle
  exact hn.trans_le hle

end Erdos796
