/- leanprover/lean4:v4.29.1 mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.CanonicalLargeOwnerSixCycle
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Erdős 686: canonical alternating-component trichotomy

This file packages an actual alternating component of the canonical
row/signed-diagonal support.  Its ordered cells are `a_i,b_i`; the `i`-th
row fibre is exactly `{a_i,b_i}` and the `i`-th signed-diagonal fibre is
exactly `{b_i,a_(i+1)}` with cyclic indexing.

Every such component has either two rows (a four-cycle), three rows (a
six-cycle), or at least four rows (at least eight edges).  The first two
branches expose witnesses in exactly the form consumed by the canonical
four- and six-cycle arithmetic.
-/

namespace Erdos686
namespace Erdos686Variant

private theorem existsUnique_otherOfTwo
    {α : Type*} [DecidableEq α] (s : Finset α) (x : α)
    (hx : x ∈ s) (hcard : s.card = 2) :
    ∃! y, y ∈ s ∧ y ≠ x := by
  obtain ⟨u, v, huv, hs⟩ := Finset.card_eq_two.mp hcard
  subst s
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl
  · refine ⟨v, ⟨Or.inr rfl, huv.symm⟩, ?_⟩
    intro y ⟨hy, hyu⟩
    rcases hy with rfl | rfl
    · exact (hyu rfl).elim
    · rfl
  · refine ⟨u, ⟨Or.inl rfl, huv⟩, ?_⟩
    intro y ⟨hy, hyv⟩
    rcases hy with rfl | rfl
    · rfl
    · exact (hyv rfl).elim

private noncomputable def otherOfTwo
    {α : Type*} [DecidableEq α] (s : Finset α) (x : α)
    (hx : x ∈ s) (hcard : s.card = 2) : α :=
  Classical.choose (existsUnique_otherOfTwo s x hx hcard)

private theorem otherOfTwo_mem
    {α : Type*} [DecidableEq α] (s : Finset α) (x : α)
    (hx : x ∈ s) (hcard : s.card = 2) :
    otherOfTwo s x hx hcard ∈ s :=
  (Classical.choose_spec (existsUnique_otherOfTwo s x hx hcard)).1.1

private theorem otherOfTwo_ne
    {α : Type*} [DecidableEq α] (s : Finset α) (x : α)
    (hx : x ∈ s) (hcard : s.card = 2) :
    otherOfTwo s x hx hcard ≠ x :=
  (Classical.choose_spec (existsUnique_otherOfTwo s x hx hcard)).1.2

private theorem otherOfTwo_unique
    {α : Type*} [DecidableEq α] (s : Finset α) (x y : α)
    (hx : x ∈ s) (hcard : s.card = 2)
    (hy : y ∈ s) (hyx : y ≠ x) :
    y = otherOfTwo s x hx hcard :=
  (Classical.choose_spec (existsUnique_otherOfTwo s x hx hcard)).2 y ⟨hy, hyx⟩

private theorem otherOfTwo_other
    {α : Type*} [DecidableEq α] (s : Finset α) (x : α)
    (hx : x ∈ s) (hcard : s.card = 2) :
    otherOfTwo s (otherOfTwo s x hx hcard)
      (otherOfTwo_mem s x hx hcard) hcard = x := by
  symm
  exact otherOfTwo_unique s (otherOfTwo s x hx hcard) x
    (otherOfTwo_mem s x hx hcard) hcard hx
    (otherOfTwo_ne s x hx hcard).symm

private theorem finset_eq_other_pair
    {α : Type*} [DecidableEq α] (s : Finset α) (x : α)
    (hx : x ∈ s) (hcard : s.card = 2) :
    s = {otherOfTwo s x hx hcard, x} := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    by_cases hyx : y = x
    · simp [hyx]
    · have := otherOfTwo_unique s x y hx hcard hy hyx
      simp [this]
  · simp [hcard, otherOfTwo_ne s x hx hcard]

private theorem canonicalLargeOwnerSupport_mem_rowFibre
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    e.1 ∈ canonicalLargeOwnerRowSupport data e.1.1 := by
  simp [canonicalLargeOwnerRowSupport, e.2]

private theorem canonicalLargeOwnerSupport_mem_diagonalFibre
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    e.1 ∈ canonicalLargeOwnerDiagonalSupport data
      (canonicalOwnerDiagonalIndex k e.1) := by
  simp [canonicalLargeOwnerDiagonalSupport, e.2]

noncomputable def canonicalLargeOwnerRowPartner
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    ↥(canonicalLargeOwnerSupport data) := by
  let s := canonicalLargeOwnerRowSupport data e.1.1
  have hx : e.1 ∈ s := canonicalLargeOwnerSupport_mem_rowFibre data e
  have hc : s.card = 2 := hrow e.1 e.2
  let y := otherOfTwo s e.1 hx hc
  refine ⟨y, ?_⟩
  exact (Finset.mem_filter.mp (otherOfTwo_mem s e.1 hx hc)).1

theorem canonicalLargeOwnerRowPartner_mem_fibre
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    (canonicalLargeOwnerRowPartner data hrow e).1 ∈
      canonicalLargeOwnerRowSupport data e.1.1 := by
  unfold canonicalLargeOwnerRowPartner
  dsimp
  exact otherOfTwo_mem _ _ _ _

theorem canonicalLargeOwnerRowPartner_ne
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    canonicalLargeOwnerRowPartner data hrow e ≠ e := by
  intro h
  have hv := Subtype.ext_iff.mp h
  unfold canonicalLargeOwnerRowPartner at hv
  dsimp at hv
  exact otherOfTwo_ne _ _ _ _ hv

theorem canonicalLargeOwnerRowPartner_fibre
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    canonicalLargeOwnerRowSupport data e.1.1 =
      {(canonicalLargeOwnerRowPartner data hrow e).1, e.1} := by
  unfold canonicalLargeOwnerRowPartner
  dsimp
  exact finset_eq_other_pair _ _ _ _

theorem canonicalLargeOwnerRowPartner_involutive
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    canonicalLargeOwnerRowPartner data hrow
      (canonicalLargeOwnerRowPartner data hrow e) = e := by
  let r := canonicalLargeOwnerRowPartner data hrow e
  have hsameRow := (Finset.mem_filter.mp
    (canonicalLargeOwnerRowPartner_mem_fibre data hrow e)).2
  have heMem : e.1 ∈ canonicalLargeOwnerRowSupport data r.1.1 := by
    rw [hsameRow]
    exact canonicalLargeOwnerSupport_mem_rowFibre data e
  have hpair := canonicalLargeOwnerRowPartner_fibre data hrow r
  rw [hpair] at heMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at heMem
  apply Subtype.ext
  rcases heMem with heMem | heMem
  · exact heMem.symm
  · exfalso
    apply (canonicalLargeOwnerRowPartner_ne data hrow e)
    simpa [r] using (Subtype.ext heMem).symm

noncomputable def canonicalLargeOwnerDiagonalPartner
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    ↥(canonicalLargeOwnerSupport data) := by
  let s := canonicalLargeOwnerDiagonalSupport data
    (canonicalOwnerDiagonalIndex k e.1)
  have hx : e.1 ∈ s := canonicalLargeOwnerSupport_mem_diagonalFibre data e
  have hc : s.card = 2 := hdiag e.1 e.2
  let y := otherOfTwo s e.1 hx hc
  refine ⟨y, ?_⟩
  exact (Finset.mem_filter.mp (otherOfTwo_mem s e.1 hx hc)).1

theorem canonicalLargeOwnerDiagonalPartner_mem_fibre
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    (canonicalLargeOwnerDiagonalPartner data hdiag e).1 ∈
      canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e.1) := by
  unfold canonicalLargeOwnerDiagonalPartner
  dsimp
  exact otherOfTwo_mem _ _ _ _

theorem canonicalLargeOwnerDiagonalPartner_ne
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    canonicalLargeOwnerDiagonalPartner data hdiag e ≠ e := by
  intro h
  have hv := Subtype.ext_iff.mp h
  unfold canonicalLargeOwnerDiagonalPartner at hv
  dsimp at hv
  exact otherOfTwo_ne _ _ _ _ hv

theorem canonicalLargeOwnerDiagonalPartner_fibre
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e.1) =
      {e.1, (canonicalLargeOwnerDiagonalPartner data hdiag e).1} := by
  unfold canonicalLargeOwnerDiagonalPartner
  dsimp
  rw [Finset.pair_comm]
  exact finset_eq_other_pair _ _ _ _

theorem canonicalLargeOwnerDiagonalPartner_involutive
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2)
    (e : ↥(canonicalLargeOwnerSupport data)) :
    canonicalLargeOwnerDiagonalPartner data hdiag
      (canonicalLargeOwnerDiagonalPartner data hdiag e) = e := by
  let r := canonicalLargeOwnerDiagonalPartner data hdiag e
  have hsameDiag := (Finset.mem_filter.mp
    (canonicalLargeOwnerDiagonalPartner_mem_fibre data hdiag e)).2
  have heMem : e.1 ∈ canonicalLargeOwnerDiagonalSupport data
      (canonicalOwnerDiagonalIndex k r.1) := by
    rw [hsameDiag]
    exact canonicalLargeOwnerSupport_mem_diagonalFibre data e
  have hpair := canonicalLargeOwnerDiagonalPartner_fibre data hdiag r
  rw [hpair] at heMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at heMem
  apply Subtype.ext
  rcases heMem with heMem | heMem
  · exfalso
    apply (canonicalLargeOwnerDiagonalPartner_ne data hdiag e)
    simpa [r] using (Subtype.ext heMem).symm
  · simpa [r] using heMem.symm

theorem canonicalLargeOwnerSupport_eq_of_row_diagonalIndex_eq
    {k n d t : ℕ} {data : CanonicalOwnerData k n d t}
    (a b : ↥(canonicalLargeOwnerSupport data))
    (hrow : a.1.1 = b.1.1)
    (hdiag : canonicalOwnerDiagonalIndex k a.1 =
      canonicalOwnerDiagonalIndex k b.1) :
    a = b := by
  have haSquare := Finset.mem_product.mp (Finset.mem_filter.mp a.2).1
  have hbSquare := Finset.mem_product.mp (Finset.mem_filter.mp b.2).1
  have haj := Finset.mem_Icc.mp haSquare.1
  have hai := Finset.mem_Icc.mp haSquare.2
  have hbj := Finset.mem_Icc.mp hbSquare.1
  have hbi := Finset.mem_Icc.mp hbSquare.2
  apply Subtype.ext
  apply Prod.ext
  · exact hrow
  · simp only [canonicalOwnerDiagonalIndex] at hdiag
    omega

/-- Cyclic successor on `Fin m`. -/
def alternatingCycleNext {m : ℕ} (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.1 + 1) % m, Nat.mod_lt _ hm⟩

/-- An ordered connected alternating component of the canonical large-owner
row/signed-diagonal support.  The two displayed families are injective, and
the endpoint inequalities record the distinctness used by each alternating
row or diagonal edge. -/
structure CanonicalLargeOwnerAlternatingComponent
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) (m : ℕ) where
  length_ge_two : 2 ≤ m
  a : Fin m → ℕ × ℕ
  b : Fin m → ℕ × ℕ
  mem_a : ∀ i, a i ∈ canonicalLargeOwnerSupport data
  mem_b : ∀ i, b i ∈ canonicalLargeOwnerSupport data
  a_injective : Function.Injective a
  b_injective : Function.Injective b
  a_ne_b_same : ∀ i, a i ≠ b i
  b_ne_a_next : ∀ i, b i ≠ a (alternatingCycleNext (by omega) i)
  row_fibre : ∀ i,
    canonicalLargeOwnerRowSupport data (b i).1 = {a i, b i}
  diagonal_fibre : ∀ i,
    canonicalLargeOwnerDiagonalSupport data
      (canonicalOwnerDiagonalIndex k (b i)) =
        {b i, a (alternatingCycleNext (by omega) i)}

/-- Exact degree-two row and used-diagonal fibres decompose the nonempty
canonical large-owner support into alternating cycles.  This theorem chooses
one such cycle and records it in the arithmetic-facing component interface. -/
theorem exists_canonicalLargeOwnerAlternatingComponent_of_degree_two
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hne : (canonicalLargeOwnerSupport data).Nonempty)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2) :
    ∃ m, Nonempty (CanonicalLargeOwnerAlternatingComponent data m) := by
  classical
  let rowP : ↥(canonicalLargeOwnerSupport data) →
      ↥(canonicalLargeOwnerSupport data) :=
    canonicalLargeOwnerRowPartner data hrow
  let diagP : ↥(canonicalLargeOwnerSupport data) →
      ↥(canonicalLargeOwnerSupport data) :=
    canonicalLargeOwnerDiagonalPartner data hdiag
  let tau : ↥(canonicalLargeOwnerSupport data) →
      ↥(canonicalLargeOwnerSupport data) := fun e => rowP (diagP e)
  have hrowInv : Function.Involutive rowP := by
    intro e
    simpa [rowP] using canonicalLargeOwnerRowPartner_involutive data hrow e
  have hdiagInv : Function.Involutive diagP := by
    intro e
    simpa [diagP] using canonicalLargeOwnerDiagonalPartner_involutive data hdiag e
  have hrowInj : Function.Injective rowP := hrowInv.injective
  have hdiagInj : Function.Injective diagP := hdiagInv.injective
  have htauInj : Function.Injective tau := by
    intro e f hef
    apply hdiagInj
    apply hrowInj
    exact hef
  have htauNotFixed : ∀ e, tau e ≠ e := by
    intro e he
    have hdiagEqRow : diagP e = rowP e := by
      calc
        diagP e = rowP (rowP (diagP e)) := (hrowInv (diagP e)).symm
        _ = rowP (tau e) := by rfl
        _ = rowP e := congrArg rowP he
    have hsameRow : (rowP e).1.1 = e.1.1 := by
      simpa [rowP] using (Finset.mem_filter.mp
        (canonicalLargeOwnerRowPartner_mem_fibre data hrow e)).2
    have hsameDiag : canonicalOwnerDiagonalIndex k (rowP e).1 =
        canonicalOwnerDiagonalIndex k e.1 := by
      rw [← hdiagEqRow]
      simpa [diagP] using (Finset.mem_filter.mp
        (canonicalLargeOwnerDiagonalPartner_mem_fibre data hdiag e)).2
    apply canonicalLargeOwnerRowPartner_ne data hrow e
    simpa [rowP] using
      (canonicalLargeOwnerSupport_eq_of_row_diagonalIndex_eq
        (rowP e) e hsameRow hsameDiag)
  obtain ⟨e₀, he₀⟩ := hne
  let x₀ : ↥(canonicalLargeOwnerSupport data) := ⟨e₀, he₀⟩
  have hperiodic : x₀ ∈ Function.periodicPts tau :=
    htauInj.mem_periodicPts x₀
  let m := Function.minimalPeriod tau x₀
  have hmpos : 0 < m := by
    simpa [m] using Function.minimalPeriod_pos_of_mem_periodicPts hperiodic
  have hmne : m ≠ 1 := by
    intro hm
    have hfixed : Function.IsFixedPt tau x₀ :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mp (by simpa [m] using hm)
    exact htauNotFixed x₀ hfixed
  have hm : 2 ≤ m := by omega
  let b : Fin m → ℕ × ℕ := fun i => ((tau^[i.1]) x₀).1
  let a : Fin m → ℕ × ℕ := fun i => (rowP ((tau^[i.1]) x₀)).1
  have hnext (i : Fin m) :
      (tau^[(alternatingCycleNext hmpos i).1]) x₀ =
        tau ((tau^[i.1]) x₀) := by
    change (tau^[(i.1 + 1) % m]) x₀ = tau ((tau^[i.1]) x₀)
    calc
      (tau^[(i.1 + 1) % m]) x₀ = (tau^[i.1 + 1]) x₀ := by
        simpa [m] using
          (Function.iterate_mod_minimalPeriod_eq
            (f := tau) (x := x₀) (n := i.1 + 1))
      _ = tau ((tau^[i.1]) x₀) := by
        rw [show i.1 + 1 = i.1.succ by omega,
          Function.iterate_succ_apply']
  have haNext (i : Fin m) :
      a (alternatingCycleNext hmpos i) =
        (diagP ((tau^[i.1]) x₀)).1 := by
    have hinv := hrowInv (diagP ((tau^[i.1]) x₀))
    apply congrArg Subtype.val at hinv
    simpa [a, tau, hnext i] using hinv
  have hbInj : Function.Injective b := by
    intro i j hij
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod
      (f := tau) (x := x₀)
    · simpa [m] using i.2
    · simpa [m] using j.2
    · apply Subtype.ext
      simpa [b] using hij
  have haInj : Function.Injective a := by
    intro i j hij
    apply hbInj
    have hp : rowP ((tau^[i.1]) x₀) = rowP ((tau^[j.1]) x₀) := by
      apply Subtype.ext
      simpa [a] using hij
    exact congrArg Subtype.val (hrowInj hp)
  refine ⟨m, ⟨{
    length_ge_two := hm
    a := a
    b := b
    mem_a := ?_
    mem_b := ?_
    a_injective := haInj
    b_injective := hbInj
    a_ne_b_same := ?_
    b_ne_a_next := ?_
    row_fibre := ?_
    diagonal_fibre := ?_ }⟩⟩
  · intro i
    exact (rowP ((tau^[i.1]) x₀)).2
  · intro i
    exact ((tau^[i.1]) x₀).2
  · intro i hab
    apply canonicalLargeOwnerRowPartner_ne data hrow ((tau^[i.1]) x₀)
    apply Subtype.ext
    simpa [a, b, rowP] using hab
  · intro i hab
    apply canonicalLargeOwnerDiagonalPartner_ne data hdiag ((tau^[i.1]) x₀)
    apply Subtype.ext
    simpa [b, haNext i, diagP] using hab.symm
  · intro i
    simpa [a, b, rowP] using
      canonicalLargeOwnerRowPartner_fibre data hrow ((tau^[i.1]) x₀)
  · intro i
    simpa [b, haNext i, diagP] using
      canonicalLargeOwnerDiagonalPartner_fibre data hdiag ((tau^[i.1]) x₀)

/-- Exact four-cycle witness extracted from a two-row alternating component. -/
structure CanonicalLargeOwnerFourCycleWitness
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) where
  a₁ : ℕ × ℕ
  b₁ : ℕ × ℕ
  a₂ : ℕ × ℕ
  b₂ : ℕ × ℕ
  mem_a₁ : a₁ ∈ canonicalLargeOwnerSupport data
  mem_b₁ : b₁ ∈ canonicalLargeOwnerSupport data
  mem_a₂ : a₂ ∈ canonicalLargeOwnerSupport data
  mem_b₂ : b₂ ∈ canonicalLargeOwnerSupport data
  a₁_ne_b₁ : a₁ ≠ b₁
  b₁_ne_a₂ : b₁ ≠ a₂
  a₂_ne_b₂ : a₂ ≠ b₂
  b₂_ne_a₁ : b₂ ≠ a₁
  a₁_ne_a₂ : a₁ ≠ a₂
  b₁_ne_b₂ : b₁ ≠ b₂
  row₁ : canonicalLargeOwnerRowSupport data b₁.1 = {a₁, b₁}
  row₂ : canonicalLargeOwnerRowSupport data b₂.1 = {a₂, b₂}
  diagonal₁ : canonicalLargeOwnerDiagonalSupport data
    (canonicalOwnerDiagonalIndex k b₁) = {b₁, a₂}
  diagonal₂ : canonicalLargeOwnerDiagonalSupport data
    (canonicalOwnerDiagonalIndex k b₂) = {b₂, a₁}

/-- Exact six-cycle witness in the interface consumed by
`canonicalLargeOwnerSixCycle_secant_or_crowding`. -/
structure CanonicalLargeOwnerSixCycleWitness
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t) where
  a₁ : ℕ × ℕ
  b₁ : ℕ × ℕ
  a₂ : ℕ × ℕ
  b₂ : ℕ × ℕ
  a₃ : ℕ × ℕ
  b₃ : ℕ × ℕ
  mem_a₁ : a₁ ∈ canonicalLargeOwnerSupport data
  mem_b₁ : b₁ ∈ canonicalLargeOwnerSupport data
  mem_a₂ : a₂ ∈ canonicalLargeOwnerSupport data
  mem_b₂ : b₂ ∈ canonicalLargeOwnerSupport data
  mem_a₃ : a₃ ∈ canonicalLargeOwnerSupport data
  mem_b₃ : b₃ ∈ canonicalLargeOwnerSupport data
  a₁_ne_b₁ : a₁ ≠ b₁
  b₁_ne_a₂ : b₁ ≠ a₂
  a₂_ne_b₂ : a₂ ≠ b₂
  b₂_ne_a₃ : b₂ ≠ a₃
  a₃_ne_b₃ : a₃ ≠ b₃
  b₃_ne_a₁ : b₃ ≠ a₁
  a₁_ne_a₂ : a₁ ≠ a₂
  a₁_ne_a₃ : a₁ ≠ a₃
  a₂_ne_a₃ : a₂ ≠ a₃
  row₁ : canonicalLargeOwnerRowSupport data b₁.1 = {a₁, b₁}
  row₂ : canonicalLargeOwnerRowSupport data b₂.1 = {a₂, b₂}
  row₃ : canonicalLargeOwnerRowSupport data b₃.1 = {a₃, b₃}
  diagonal₁ : canonicalLargeOwnerDiagonalSupport data
    (canonicalOwnerDiagonalIndex k b₁) = {b₁, a₂}
  diagonal₂ : canonicalLargeOwnerDiagonalSupport data
    (canonicalOwnerDiagonalIndex k b₂) = {b₂, a₃}
  diagonal₃ : canonicalLargeOwnerDiagonalSupport data
    (canonicalOwnerDiagonalIndex k b₃) = {b₃, a₁}

private theorem next_fin_two_zero :
    alternatingCycleNext (by omega : 0 < 2) (0 : Fin 2) = (1 : Fin 2) := by
  apply Fin.ext
  norm_num [alternatingCycleNext]

private theorem next_fin_two_one :
    alternatingCycleNext (by omega : 0 < 2) (1 : Fin 2) = (0 : Fin 2) := by
  apply Fin.ext
  norm_num [alternatingCycleNext]

private theorem next_fin_three_zero :
    alternatingCycleNext (by omega : 0 < 3) (0 : Fin 3) = (1 : Fin 3) := by
  apply Fin.ext
  norm_num [alternatingCycleNext]

private theorem next_fin_three_one :
    alternatingCycleNext (by omega : 0 < 3) (1 : Fin 3) = (2 : Fin 3) := by
  apply Fin.ext
  norm_num [alternatingCycleNext]

private theorem next_fin_three_two :
    alternatingCycleNext (by omega : 0 < 3) (2 : Fin 3) = (0 : Fin 3) := by
  apply Fin.ext
  norm_num [alternatingCycleNext]

private def fourCycleWitness_of_length_eq_two
    {k n d t m : ℕ} {data : CanonicalOwnerData k n d t}
    (C : CanonicalLargeOwnerAlternatingComponent data m)
    (hlen : m = 2) :
    CanonicalLargeOwnerFourCycleWitness data := by
  subst m
  let i₀ : Fin 2 := 0
  let i₁ : Fin 2 := 1
  refine
    { a₁ := C.a i₀, b₁ := C.b i₀
      a₂ := C.a i₁, b₂ := C.b i₁
      mem_a₁ := C.mem_a i₀, mem_b₁ := C.mem_b i₀
      mem_a₂ := C.mem_a i₁, mem_b₂ := C.mem_b i₁
      a₁_ne_b₁ := C.a_ne_b_same i₀
      b₁_ne_a₂ := by
        simpa [i₀, i₁, next_fin_two_zero] using C.b_ne_a_next i₀
      a₂_ne_b₂ := C.a_ne_b_same i₁
      b₂_ne_a₁ := by
        simpa [i₀, i₁, next_fin_two_one] using C.b_ne_a_next i₁
      a₁_ne_a₂ := by
        intro h; exact Fin.zero_ne_one (C.a_injective h)
      b₁_ne_b₂ := by
        intro h; exact Fin.zero_ne_one (C.b_injective h)
      row₁ := C.row_fibre i₀
      row₂ := C.row_fibre i₁
      diagonal₁ := by
        simpa [i₀, i₁, next_fin_two_zero] using C.diagonal_fibre i₀
      diagonal₂ := by
        simpa [i₀, i₁, next_fin_two_one] using C.diagonal_fibre i₁ }

private def sixCycleWitness_of_length_eq_three
    {k n d t m : ℕ} {data : CanonicalOwnerData k n d t}
    (C : CanonicalLargeOwnerAlternatingComponent data m)
    (hlen : m = 3) :
    CanonicalLargeOwnerSixCycleWitness data := by
  subst m
  let i₀ : Fin 3 := 0
  let i₁ : Fin 3 := 1
  let i₂ : Fin 3 := 2
  refine
    { a₁ := C.a i₀, b₁ := C.b i₀
      a₂ := C.a i₁, b₂ := C.b i₁
      a₃ := C.a i₂, b₃ := C.b i₂
      mem_a₁ := C.mem_a i₀, mem_b₁ := C.mem_b i₀
      mem_a₂ := C.mem_a i₁, mem_b₂ := C.mem_b i₁
      mem_a₃ := C.mem_a i₂, mem_b₃ := C.mem_b i₂
      a₁_ne_b₁ := C.a_ne_b_same i₀
      b₁_ne_a₂ := by
        simpa [i₀, i₁, next_fin_three_zero] using C.b_ne_a_next i₀
      a₂_ne_b₂ := C.a_ne_b_same i₁
      b₂_ne_a₃ := by
        simpa [i₁, i₂, next_fin_three_one] using C.b_ne_a_next i₁
      a₃_ne_b₃ := C.a_ne_b_same i₂
      b₃_ne_a₁ := by
        simpa [i₀, i₂, next_fin_three_two] using C.b_ne_a_next i₂
      a₁_ne_a₂ := by
        intro h; exact Fin.zero_ne_one (C.a_injective h)
      a₁_ne_a₃ := by
        intro h
        have hi := C.a_injective h
        norm_num [i₀, i₂] at hi
        omega
      a₂_ne_a₃ := by
        intro h
        have hi := C.a_injective h
        norm_num [i₁, i₂] at hi
        omega
      row₁ := C.row_fibre i₀
      row₂ := C.row_fibre i₁
      row₃ := C.row_fibre i₂
      diagonal₁ := by
        simpa [i₀, i₁, next_fin_three_zero] using C.diagonal_fibre i₀
      diagonal₂ := by
        simpa [i₁, i₂, next_fin_three_one] using C.diagonal_fibre i₁
      diagonal₃ := by
        simpa [i₀, i₂, next_fin_three_two] using C.diagonal_fibre i₂ }

/-- Exact component-length trichotomy with arithmetic-ready witnesses in the
small branches.  The remaining branch has at least four rows, hence at least
eight alternating owner edges. -/
theorem canonicalLargeOwnerAlternatingComponent_trichotomy
    {k n d t m : ℕ} {data : CanonicalOwnerData k n d t}
    (C : CanonicalLargeOwnerAlternatingComponent data m) :
    Nonempty (CanonicalLargeOwnerFourCycleWitness data) ∨
      Nonempty (CanonicalLargeOwnerSixCycleWitness data) ∨
        4 ≤ m := by
  by_cases htwo : m = 2
  · exact Or.inl ⟨fourCycleWitness_of_length_eq_two C htwo⟩
  · by_cases hthree : m = 3
    · exact Or.inr (Or.inl ⟨sixCycleWitness_of_length_eq_three C hthree⟩)
    · have hm := C.length_ge_two
      exact Or.inr (Or.inr (by omega))

/-- Raw nonempty degree-two support gives either an arithmetic-ready
four-cycle, an arithmetic-ready six-cycle, or a certified alternating
component with at least four rows. -/
theorem canonicalLargeOwnerSupport_degree_two_trichotomy
    {k n d t : ℕ} (data : CanonicalOwnerData k n d t)
    (hne : (canonicalLargeOwnerSupport data).Nonempty)
    (hrow : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerRowSupport data e.1).card = 2)
    (hdiag : ∀ e ∈ canonicalLargeOwnerSupport data,
      (canonicalLargeOwnerDiagonalSupport data
        (canonicalOwnerDiagonalIndex k e)).card = 2) :
    Nonempty (CanonicalLargeOwnerFourCycleWitness data) ∨
      Nonempty (CanonicalLargeOwnerSixCycleWitness data) ∨
        ∃ m, 4 ≤ m ∧
          Nonempty (CanonicalLargeOwnerAlternatingComponent data m) := by
  obtain ⟨m, ⟨C⟩⟩ :=
    exists_canonicalLargeOwnerAlternatingComponent_of_degree_two
      data hne hrow hdiag
  rcases canonicalLargeOwnerAlternatingComponent_trichotomy C with
    hfour | hsix | hlong
  · exact Or.inl hfour
  · exact Or.inr (Or.inl hsix)
  · exact Or.inr (Or.inr ⟨m, hlong, ⟨C⟩⟩)

#print axioms exists_canonicalLargeOwnerAlternatingComponent_of_degree_two
#print axioms canonicalLargeOwnerAlternatingComponent_trichotomy
#print axioms canonicalLargeOwnerSupport_degree_two_trichotomy

end Erdos686Variant
end Erdos686
