import Mathlib

namespace Erdos254.GrowthPartition

noncomputable section

/-- The elements of `s` whose positions in the increasing enumeration are
congruent to `c` modulo four. -/
def balancedPart (s : Finset ℕ) (c : ℕ) : Finset ℕ :=
  ((Finset.univ.filter fun i : Fin s.card => i.val % 4 = c).map
    (s.orderEmbOfFin rfl).toEmbedding)

lemma balancedPart_subset (s : Finset ℕ) (c : ℕ) : balancedPart s c ⊆ s := by
  intro n hn
  rw [balancedPart, Finset.mem_map] at hn
  obtain ⟨i, _, rfl⟩ := hn
  exact s.orderEmbOfFin_mem rfl i

lemma balancedPart_card_ge (s : Finset ℕ) (c K : ℕ) (hc : c < 4)
    (hK : 4 * K ≤ s.card) : K ≤ (balancedPart s c).card := by
  let e : Fin K ↪ Fin s.card :=
    ⟨fun i => ⟨c + 4 * i.val, by
        have hi : i.val < K := i.isLt
        omega⟩,
      by
        intro i j hij
        apply Fin.ext
        have hval := congrArg Fin.val hij
        dsimp at hval
        omega⟩
  have hsub : Finset.univ.map e ⊆
      (Finset.univ.filter fun i : Fin s.card => i.val % 4 = c) := by
    intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [e]
    omega
  calc
    K = (Finset.univ.map e).card := by simp
    _ ≤ (Finset.univ.filter fun i : Fin s.card => i.val % 4 = c).card :=
      Finset.card_le_card hsub
    _ = (balancedPart s c).card := by simp [balancedPart]

lemma mem_some_balancedPart (s : Finset ℕ) {n : ℕ} (hn : n ∈ s) :
    ∃ c < 4, n ∈ balancedPart s c := by
  let i : Fin s.card := (s.orderIsoOfFin rfl).symm ⟨n, hn⟩
  refine ⟨i.val % 4, Nat.mod_lt _ (by decide), ?_⟩
  rw [balancedPart, Finset.mem_map]
  refine ⟨i, ?_, ?_⟩
  · simp [i]
  · exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨n, hn⟩)

lemma balancedPart_pairwise_disjoint (s : Finset ℕ) {c d : ℕ} (hcd : c ≠ d) :
    Disjoint (balancedPart s c) (balancedPart s d) := by
  rw [Finset.disjoint_left]
  intro n hnc hnd
  rw [balancedPart, Finset.mem_map] at hnc hnd
  obtain ⟨i, hi, hin⟩ := hnc
  obtain ⟨j, hj, hjn⟩ := hnd
  have hij : i = j := (s.orderEmbOfFin rfl).injective (hin.trans hjn.symm)
  subst j
  have hic : i.val % 4 = c := (Finset.mem_filter.mp hi).2
  have hid : i.val % 4 = d := (Finset.mem_filter.mp hj).2
  exact hcd (hic.symm.trans hid)

def powerShell (A : Set ℕ) (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter (fun n => n ∈ A)

def countingFunction (A : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 x).filter (fun n => n ∈ A)).card

def dyadicIncrement (A : Set ℕ) (x : ℕ) : ℕ :=
  countingFunction A (2 * x) - countingFunction A x

def shellCount (A : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc x (2 * x)).filter (fun n => n ∈ A)).card

lemma dyadicIncrement_eq_shellCard (A : Set ℕ) (x : ℕ) :
    dyadicIncrement A x = shellCount A x := by
  classical
  let s := (Finset.Icc 1 x).filter (fun n => n ∈ A)
  let t := (Finset.Icc 1 (2 * x)).filter (fun n => n ∈ A)
  have hst : s ⊆ t := by
    intro n hn
    simp only [s, t, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans (by omega)⟩, hn.2⟩
  rw [dyadicIncrement, countingFunction, countingFunction]
  change t.card - s.card = _
  rw [← Finset.card_sdiff_of_subset hst]
  apply congrArg Finset.card
  ext n
  simp only [t, s, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hA⟩, hnot⟩
    refine ⟨⟨?_, hlo.2⟩, hA⟩
    by_contra hnx
    exact hnot ⟨⟨hlo.1, Nat.le_of_not_gt hnx⟩, hA⟩
  · rintro ⟨⟨hxn, hn2x⟩, hA⟩
    refine ⟨⟨⟨by omega, hn2x⟩, hA⟩, ?_⟩
    rintro ⟨⟨_, hnx⟩, _⟩
    omega

lemma dyadic_tendsto_powerShells (A : Set ℕ)
    (hdyadic : Filter.Tendsto (dyadicIncrement A) Filter.atTop Filter.atTop) :
    ∀ᶠ j : ℕ in Filter.atTop, 16 ≤ (powerShell A j).card := by
  have hx : ∀ᶠ x : ℕ in Filter.atTop, 16 ≤ shellCount A x := by
    filter_upwards [Filter.tendsto_atTop.1 hdyadic 16] with x hx
    simpa only [dyadicIncrement_eq_shellCard] using hx
  have hj := (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by decide)).eventually hx
  filter_upwards [hj] with j hj
  simpa [powerShell, shellCount, pow_succ, mul_comm] using hj

/-- Four points of one power-of-two shell already have total sum larger than
any point of the following shell. -/
theorem previous_balancedPart_covers_next
    (A : Set ℕ) (j c n : ℕ) (hc : c < 4)
    (hcard : 16 ≤ (powerShell A j).card)
    (hn : n ∈ powerShell A (j + 1)) :
    n ≤ ∑ m ∈ balancedPart (powerShell A j) c, m := by
  have hpartcard : 4 ≤ (balancedPart (powerShell A j) c).card := by
    apply balancedPart_card_ge
    · exact hc
    · omega
  have hpartsub := balancedPart_subset (powerShell A j) c
  have hlower : ∀ m ∈ balancedPart (powerShell A j) c, 2 ^ j + 1 ≤ m := by
    intro m hm
    have hmshell := hpartsub hm
    simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hmshell
    omega
  have hsum : (2 ^ j + 1) * (balancedPart (powerShell A j) c).card ≤
      ∑ m ∈ balancedPart (powerShell A j) c, m := by
    simpa [nsmul_eq_mul, mul_comm] using
      (Finset.card_nsmul_le_sum (balancedPart (powerShell A j) c)
        (fun m => m) (2 ^ j + 1) hlower)
  have hnupper : n ≤ 2 ^ (j + 2) := by
    simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hn
    simpa [Nat.add_assoc] using hn.1.2
  calc
    n ≤ 2 ^ (j + 2) := hnupper
    _ ≤ (2 ^ j + 1) * (balancedPart (powerShell A j) c).card := by
      rw [show 2 ^ (j + 2) = 4 * 2 ^ j by ring]
      calc
        4 * 2 ^ j ≤ (2 ^ j + 1) * 4 := by omega
        _ ≤ (2 ^ j + 1) * (balancedPart (powerShell A j) c).card :=
          Nat.mul_le_mul_left (2 ^ j + 1) hpartcard
    _ ≤ ∑ m ∈ balancedPart (powerShell A j) c, m := hsum

/-- The global color class obtained by applying `balancedPart` independently
in every power-of-two shell. -/
def colorClass (A : Set ℕ) (c : ℕ) : Set ℕ :=
  {n | ∃ j : ℕ, n ∈ balancedPart (powerShell A j) c}

lemma powerShell_index_unique (A : Set ℕ) {j k n : ℕ}
    (hj : n ∈ powerShell A j) (hk : n ∈ powerShell A k) : j = k := by
  simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hj hk
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · have hp : 2 ^ (j + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · rfl
  · have hp : 2 ^ (k + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

lemma colorClass_pairwise_disjoint (A : Set ℕ) {c d : ℕ} (hcd : c ≠ d) :
    Disjoint (colorClass A c) (colorClass A d) := by
  rw [Set.disjoint_left]
  intro n hnc hnd
  obtain ⟨j, hj⟩ := hnc
  obtain ⟨k, hk⟩ := hnd
  have hjs := balancedPart_subset (powerShell A j) c hj
  have hks := balancedPart_subset (powerShell A k) d hk
  have hjk : j = k := powerShell_index_unique A hjs hks
  subst k
  exact Finset.disjoint_left.mp (balancedPart_pairwise_disjoint (powerShell A j) hcd)
    hj hk

lemma mem_some_colorClass (A : Set ℕ) {n : ℕ} (hnA : n ∈ A) (hn : 1 < n) :
    ∃ c < 4, n ∈ colorClass A c := by
  let k := Nat.clog 2 n
  have hkpos : 0 < k := Nat.clog_pos (by decide) hn
  let j := k - 1
  have hjk : j + 1 = k := Nat.sub_add_cancel hkpos
  have hjlt : j < k := by omega
  have hlower : 2 ^ j < n := by
    exact (Nat.lt_clog_iff_pow_lt (by decide)).mp (by simpa [k] using hjlt)
  have hupper : n ≤ 2 ^ (j + 1) := by
    rw [hjk]
    exact Nat.le_pow_clog (by decide) n
  have hnshell : n ∈ powerShell A j := by
    simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hlower, hupper⟩, hnA⟩
  obtain ⟨c, hc, hnc⟩ := mem_some_balancedPart (s := powerShell A j) hnshell
  exact ⟨c, hc, j, hnc⟩

def prefixFinset (B : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Iio n).filter (fun m => m ∈ B)

def prefixSum (B : Set ℕ) (n : ℕ) : ℕ :=
  ∑ m ∈ prefixFinset B n, m

lemma balancedPart_subset_prefix (A : Set ℕ) (j c n : ℕ)
    (hn : n ∈ powerShell A (j + 1)) :
    balancedPart (powerShell A j) c ⊆
      prefixFinset (colorClass A c) n := by
  intro m hm
  have hms := balancedPart_subset (powerShell A j) c hm
  simp only [powerShell, Finset.mem_filter, Finset.mem_Ioc] at hms hn
  simp only [prefixFinset, Finset.mem_filter, Finset.mem_Iio]
  refine ⟨?_, ⟨j, hm⟩⟩
  omega

lemma colorClass_growth_of_shell_card (A : Set ℕ) (j c n : ℕ) (hc : c < 4)
    (hcard : 16 ≤ (powerShell A j).card)
    (hn : n ∈ powerShell A (j + 1)) :
    n ≤ prefixSum (colorClass A c) n := by
  classical
  apply (previous_balancedPart_covers_next A j c n hc hcard hn).trans
  exact Finset.sum_le_sum_of_subset (balancedPart_subset_prefix A j c n hn)

/-- Once all sufficiently late shells have sixteen points, each global color
class satisfies the subset-sum growth inequality eventually. -/
theorem colorClass_eventual_growth (A : Set ℕ) (c : ℕ) (hc : c < 4)
    (hshell : ∀ᶠ j : ℕ in Filter.atTop, 16 ≤ (powerShell A j).card) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → n ∈ colorClass A c →
      n ≤ prefixSum (colorClass A c) n := by
  classical
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hshell
  refine ⟨2 ^ (J + 1) + 1, ?_⟩
  intro n hnlarge hnc
  obtain ⟨k, hnkpart⟩ := hnc
  have hnkshell := balancedPart_subset (powerShell A k) c hnkpart
  have hkgt : J < k := by
    by_contra hnot
    have hkle : k ≤ J := Nat.le_of_not_gt hnot
    have hnupper : n ≤ 2 ^ (k + 1) := by
      exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hnkshell).1).2
    have hp : 2 ^ (k + 1) ≤ 2 ^ (J + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  let j := k - 1
  have hjk : j + 1 = k := Nat.sub_add_cancel (by omega)
  have hcard : 16 ≤ (powerShell A j).card := hJ j (by omega)
  apply colorClass_growth_of_shell_card A j c n hc hcard
  rwa [hjk]

/-- The dyadic hypothesis produces four disjoint growth classes which cover
all members of `A` above one. -/
theorem dyadic_produces_four_growth_classes (A : Set ℕ)
    (hdyadic : Filter.Tendsto (dyadicIncrement A) Filter.atTop Filter.atTop) :
    ∃ B : Fin 4 → Set ℕ,
      (∀ i, B i ⊆ A) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ n ∈ A, 1 < n → ∃ i, n ∈ B i) ∧
      (∀ i, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → n ∈ B i →
        n ≤ prefixSum (B i) n) := by
  classical
  let B : Fin 4 → Set ℕ := fun i => colorClass A i.val
  have hshell := dyadic_tendsto_powerShells A hdyadic
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro i n hn
    obtain ⟨j, hnj⟩ := hn
    have hnshell := balancedPart_subset (powerShell A j) i.val hnj
    exact (Finset.mem_filter.mp hnshell).2
  · intro i j hij
    apply colorClass_pairwise_disjoint A
    intro hval
    apply hij
    exact Fin.ext hval
  · intro n hnA hn
    obtain ⟨c, hc, hnc⟩ := mem_some_colorClass A hnA hn
    exact ⟨⟨c, hc⟩, hnc⟩
  · intro i
    exact colorClass_eventual_growth A i.val i.isLt hshell

end

end Erdos254.GrowthPartition
