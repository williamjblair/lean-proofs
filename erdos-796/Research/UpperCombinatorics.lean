import Research.FiberTypes

namespace Erdos796

/-- Three distinct ordered pairs with the same product already contradict
cross-compatibility.  This is the basic finite certificate used in the upper
bound's rectangle and cube arguments. -/
theorem three_cross_representations_not_compatible
    {S T : Finset ℕ} {x₁ y₁ x₂ y₂ x₃ y₃ m : ℕ}
    (hx₁ : x₁ ∈ S) (hy₁ : y₁ ∈ T)
    (hx₂ : x₂ ∈ S) (hy₂ : y₂ ∈ T)
    (hx₃ : x₃ ∈ S) (hy₃ : y₃ ∈ T)
    (hprod₁ : x₁ * y₁ = m) (hprod₂ : x₂ * y₂ = m)
    (hprod₃ : x₃ * y₃ = m)
    (h₁₂ : (x₁, y₁) ≠ (x₂, y₂))
    (h₁₃ : (x₁, y₁) ≠ (x₃, y₃))
    (h₂₃ : (x₂, y₂) ≠ (x₃, y₃)) :
    ¬ CrossCompatible S T := by
  intro hcompat
  have hle := crossRepCount_le_two_of_compatible hcompat m
  let P : Finset (ℕ × ℕ) := {(x₁, y₁), (x₂, y₂), (x₃, y₃)}
  have hPcard : P.card = 3 := by
    dsimp [P]
    simp [h₁₂, h₁₃, h₂₃]
  have hsub : P ⊆ ((S ×ˢ T).filter fun z => z.1 * z.2 = m) := by
    intro z hz
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hx₁, hy₁⟩, hprod₁⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hx₂, hy₂⟩, hprod₂⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hx₃, hy₃⟩, hprod₃⟩
  have hcard := Finset.card_le_card hsub
  unfold crossRepCount at hle
  omega

/-- If two fibers both contain the two coefficient rays `t·prime` and
`u·prime` at two different large primes, then they are not cross-compatible.
Thus every coefficient-pair incidence graph in the upper-bound decomposition
is `C₄`-free. -/
theorem prime_ray_rectangle_not_compatible
    {S T : Finset ℕ} {W t u p s : ℕ}
    (ht : 0 < t) (hu : 0 < u) (htW : t ≤ W) (huW : u ≤ W)
    (htu : t ≠ u)
    (hpW : W < p) (hsW : W < s) (hp : p.Prime) (hs : s.Prime)
    (hps : p ≠ s)
    (htpS : t * p ∈ S) (hupS : u * p ∈ S)
    (htsS : t * s ∈ S) (husS : u * s ∈ S)
    (htpT : t * p ∈ T) (hupT : u * p ∈ T)
    (htsT : t * s ∈ T) (husT : u * s ∈ T) :
    ¬ CrossCompatible S T := by
  have htp_up : t * p ≠ u * p := by
    intro h
    exact htu (Nat.mul_right_cancel hp.pos h)
  have htp_ts : t * p ≠ t * s := by
    intro h
    exact hps (Nat.mul_left_cancel ht h)
  have hup_ts : u * p ≠ t * s := by
    intro h
    have heq : p * u = s * t := by simpa [Nat.mul_comm] using h
    have huniq := large_prime_core_decomposition_unique hpW hsW hp hs ht htW heq
    exact hps huniq.1
  apply three_cross_representations_not_compatible
    (S := S) (T := T) (m := t * u * p * s)
    htpS husT hupS htsT htsS hupT
  · ring
  · ring
  · ring
  · intro h
    exact htp_up (Prod.mk.inj h).1
  · intro h
    exact htp_ts (Prod.mk.inj h).1
  · intro h
    exact hup_ts (Prod.mk.inj h).1

/-- A complete `2×2` rectangle of factor products occurring in each of two
fibers is forbidden.  This is the local `2×2×2` cube obstruction used for
split composite cores. -/
theorem factor_rectangle_not_compatible
    {S T : Finset ℕ} {a₀ a₁ b₀ b₁ : ℕ}
    (h00S : a₀ * b₀ ∈ S) (h01S : a₀ * b₁ ∈ S)
    (h10S : a₁ * b₀ ∈ S) (h11S : a₁ * b₁ ∈ S)
    (h00T : a₀ * b₀ ∈ T) (h01T : a₀ * b₁ ∈ T)
    (h10T : a₁ * b₀ ∈ T) (h11T : a₁ * b₁ ∈ T)
    (h00_ne_01 : a₀ * b₀ ≠ a₀ * b₁)
    (h00_ne_11 : a₀ * b₀ ≠ a₁ * b₁)
    (h01_ne_11 : a₀ * b₁ ≠ a₁ * b₁) :
    ¬ CrossCompatible S T := by
  apply three_cross_representations_not_compatible
    (S := S) (T := T)
    (m := a₀ * a₁ * b₀ * b₁)
    h00S h11T h01S h10T h11S h00T
  · ring
  · ring
  · ring
  · intro h
    exact h00_ne_01 (Prod.mk.inj h).1
  · intro h
    exact h00_ne_11 (Prod.mk.inj h).1
  · intro h
    exact h01_ne_11 (Prod.mk.inj h).1

/-- A bipartite edge set contains no combinatorial rectangle. -/
def RectangleFree {α β : Type*} (E : Finset (α × β)) : Prop :=
  ∀ ⦃a₁ a₂ : α⦄ ⦃b₁ b₂ : β⦄, a₁ ≠ a₂ → b₁ ≠ b₂ →
    (a₁, b₁) ∈ E → (a₁, b₂) ∈ E →
    (a₂, b₁) ∈ E → (a₂, b₂) ∈ E → False

section RectangleBound

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Neighbors in the second part of a bipartite edge set. -/
def bipartiteRow (E : Finset (α × β)) (a : α) : Finset β :=
  (Finset.univ : Finset β).filter fun b => (a, b) ∈ E

/-- Ordered length-two paths whose center lies in the first part. -/
def bipartiteCorners (E : Finset (α × β)) : Finset (α × (β × β)) :=
  ((Finset.univ : Finset α).product
    (Finset.univ : Finset β).offDiag).filter fun z =>
      (z.1, z.2.1) ∈ E ∧ (z.1, z.2.2) ∈ E

lemma bipartiteRow_offDiag_eq (E : Finset (α × β)) (a : α) :
    (bipartiteRow E a).offDiag =
      (Finset.univ : Finset β).offDiag.filter fun z =>
        (a, z.1) ∈ E ∧ (a, z.2) ∈ E := by
  ext z
  simp [bipartiteRow, Finset.mem_offDiag, and_comm, and_left_comm, and_assoc]

/-- Counting edges by their first coordinate. -/
theorem card_eq_sum_bipartiteRow (E : Finset (α × β)) :
    E.card = ∑ a : α, (bipartiteRow E a).card := by
  have hE : E = ((Finset.univ : Finset α).product
      (Finset.univ : Finset β)).filter fun z => z ∈ E := by
    ext z
    simp
  calc
    E.card = (((Finset.univ : Finset α).product
        (Finset.univ : Finset β)).filter fun z => z ∈ E).card := by rw [← hE]
    _ = ∑ z ∈ (Finset.univ : Finset α).product
        (Finset.univ : Finset β), if z ∈ E then 1 else 0 := Finset.card_filter _ _
    _ = ∑ a : α, ∑ b : β, if (a, b) ∈ E then 1 else 0 :=
      Finset.sum_product _ _ _
    _ = ∑ a : α, (bipartiteRow E a).card := by
      apply Finset.sum_congr rfl
      intro a ha
      unfold bipartiteRow
      rw [Finset.card_filter]

/-- Counting ordered length-two paths row by row. -/
theorem card_bipartiteCorners_eq (E : Finset (α × β)) :
    (bipartiteCorners E).card =
      ∑ a : α, ((bipartiteRow E a).offDiag).card := by
  unfold bipartiteCorners
  rw [Finset.card_filter]
  rw [show (∑ z ∈ (Finset.univ : Finset α).product
      (Finset.univ : Finset β).offDiag,
      if (z.1, z.2.1) ∈ E ∧ (z.1, z.2.2) ∈ E then 1 else 0) =
      ∑ a : α, ∑ z ∈ (Finset.univ : Finset β).offDiag,
        if (a, z.1) ∈ E ∧ (a, z.2) ∈ E then 1 else 0 from
    Finset.sum_product _ _ _]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.card_filter, ← bipartiteRow_offDiag_eq]

/-- In a rectangle-free graph, projection of an ordered two-path to its two
endpoints is injective. -/
lemma bipartiteCorners_snd_injOn (E : Finset (α × β))
    (hfree : RectangleFree E) :
    Set.InjOn (fun z : α × (β × β) => z.2) (bipartiteCorners E) := by
  intro z hz w hw hzw
  rcases z with ⟨a, ⟨b, c⟩⟩
  rcases w with ⟨a', ⟨b', c'⟩⟩
  simp only [Prod.mk.injEq] at hzw
  rcases hzw with ⟨rfl, rfl⟩
  change (a, (b, c)) ∈ bipartiteCorners E at hz
  change (a', (b, c)) ∈ bipartiteCorners E at hw
  have hz' := Finset.mem_filter.mp hz
  have hw' := Finset.mem_filter.mp hw
  have hzbase := Finset.mem_product.mp hz'.1
  have hzoff := Finset.mem_offDiag.mp hzbase.2
  have haa : a = a' := by
    by_contra hne
    exact hfree hne hzoff.2.2 hz'.2.1 hz'.2.2 hw'.2.1 hw'.2.2
  subst a'
  rfl

/-- A rectangle-free bipartite graph has at most one center for every ordered
pair of distinct endpoints. -/
theorem card_bipartiteCorners_le (E : Finset (α × β))
    (hfree : RectangleFree E) :
    (bipartiteCorners E).card ≤ Fintype.card β * Fintype.card β := by
  have hinj := bipartiteCorners_snd_injOn E hfree
  have hcard : ((bipartiteCorners E).image
      (fun z : α × (β × β) => z.2)).card = (bipartiteCorners E).card :=
    Finset.card_image_of_injOn hinj
  have hsub : (bipartiteCorners E).image
      (fun z : α × (β × β) => z.2) ⊆
      (Finset.univ : Finset β).offDiag := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    have hwbase := (Finset.mem_filter.mp hw).1
    exact (Finset.mem_product.mp hwbase).2
  rw [← hcard]
  calc
    _ ≤ ((Finset.univ : Finset β).offDiag).card := Finset.card_le_card hsub
    _ ≤ Fintype.card β * Fintype.card β := by
      rw [Finset.offDiag_card]
      exact Nat.sub_le _ _

/-- Cauchy--Schwarz relates the edge count of any bipartite graph to its
ordered length-two paths. -/
theorem bipartite_card_sq_le_card_mul_corners (E : Finset (α × β)) :
    E.card ^ 2 ≤ Fintype.card α *
      ((bipartiteCorners E).card + E.card) := by
  have hrows := card_eq_sum_bipartiteRow E
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset α))
    (f := fun a => (bipartiteRow E a).card)
  have hsquares : (∑ a : α, (bipartiteRow E a).card ^ 2) =
      (bipartiteCorners E).card + E.card := by
    rw [card_bipartiteCorners_eq, hrows]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.offDiag_card]
    have hd : (bipartiteRow E a).card ≤
        (bipartiteRow E a).card * (bipartiteRow E a).card := by
      by_cases hzero : (bipartiteRow E a).card = 0
      · simp [hzero]
      · have : 1 ≤ (bipartiteRow E a).card := Nat.one_le_iff_ne_zero.mpr hzero
        nlinarith
    rw [Nat.sub_add_cancel hd]
    ring
  rw [← hrows] at hcauchy
  rw [Finset.card_univ, hsquares] at hcauchy
  exact hcauchy

/-- Exact polynomial Kővári--Sós--Turán inequality for a rectangle-free
bipartite graph.  It implies the familiar `e ≤ X + Y√X` estimate. -/
theorem rectangleFree_card_sq_le (E : Finset (α × β))
    (hfree : RectangleFree E) :
    E.card ^ 2 ≤ Fintype.card α *
      (Fintype.card β ^ 2 + E.card) := by
  have hrows := card_eq_sum_bipartiteRow E
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset α))
    (f := fun a => (bipartiteRow E a).card)
  have hsquares : (∑ a : α, (bipartiteRow E a).card ^ 2) =
      (bipartiteCorners E).card + E.card := by
    rw [card_bipartiteCorners_eq, hrows]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.offDiag_card]
    have hd : (bipartiteRow E a).card ≤
        (bipartiteRow E a).card * (bipartiteRow E a).card := by
      by_cases hzero : (bipartiteRow E a).card = 0
      · simp [hzero]
      · have : 1 ≤ (bipartiteRow E a).card := Nat.one_le_iff_ne_zero.mpr hzero
        nlinarith
    rw [Nat.sub_add_cancel hd]
    ring
  rw [← hrows] at hcauchy
  rw [Finset.card_univ, hsquares] at hcauchy
  calc
    E.card ^ 2 ≤ Fintype.card α *
        ((bipartiteCorners E).card + E.card) := hcauchy
    _ ≤ Fintype.card α * (Fintype.card β ^ 2 + E.card) := by
      gcongr
      simpa [pow_two] using card_bipartiteCorners_le E hfree

/-- Square-root form of the exact rectangle-free edge bound. -/
theorem rectangleFree_card_le (E : Finset (α × β))
    (hfree : RectangleFree E) :
    (E.card : ℝ) ≤ Fintype.card α +
      Fintype.card β * Real.sqrt (Fintype.card α) := by
  have hnat := rectangleFree_card_sq_le E hfree
  have h : (E.card : ℝ) ^ 2 ≤ (Fintype.card α : ℝ) *
      ((Fintype.card β : ℝ) ^ 2 + E.card) := by exact_mod_cast hnat
  have hX : (0 : ℝ) ≤ Fintype.card α := by positivity
  have hY : (0 : ℝ) ≤ Fintype.card β := by positivity
  have hs := Real.sq_sqrt hX
  have hr := Real.sqrt_nonneg (Fintype.card α)
  by_contra hn
  push Not at hn
  have h1 : (Fintype.card β : ℝ) * Real.sqrt (Fintype.card α) < E.card := by
    nlinarith
  have h2 : (Fintype.card β : ℝ) * Real.sqrt (Fintype.card α) <
      E.card - Fintype.card α := by nlinarith
  have hm : ((Fintype.card β : ℝ) * Real.sqrt (Fintype.card α)) *
      ((Fintype.card β : ℝ) * Real.sqrt (Fintype.card α)) <
      (E.card : ℝ) * (E.card - Fintype.card α) := by
    exact mul_lt_mul_of_nonneg h1 h2 (mul_nonneg hY hr) (mul_nonneg hY hr)
  nlinarith

end RectangleBound

/-- A tripartite edge set contains no complete `2×2×2` box. -/
def CubeFree {α β γ : Type*} (H : Finset (α × (β × γ))) : Prop :=
  ∀ ⦃a₀ a₁ : α⦄ ⦃b₀ b₁ : β⦄ ⦃c₀ c₁ : γ⦄,
    a₀ ≠ a₁ → b₀ ≠ b₁ → c₀ ≠ c₁ →
    (a₀, (b₀, c₀)) ∈ H → (a₀, (b₀, c₁)) ∈ H →
    (a₀, (b₁, c₀)) ∈ H → (a₀, (b₁, c₁)) ∈ H →
    (a₁, (b₀, c₀)) ∈ H → (a₁, (b₀, c₁)) ∈ H →
    (a₁, (b₁, c₀)) ∈ H → (a₁, (b₁, c₁)) ∈ H → False

section CubeBound

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Common `(β,γ)` slice of two first-coordinate vertices. -/
def commonSlice (H : Finset (α × (β × γ))) (aa : α × α) :
    Finset (β × γ) :=
  (Finset.univ : Finset (β × γ)).filter fun bc =>
    (aa.1, bc) ∈ H ∧ (aa.2, bc) ∈ H

/-- First-coordinate neighbors of one `(β,γ)` pair. -/
def alphaFiber (H : Finset (α × (β × γ))) (bc : β × γ) : Finset α :=
  (Finset.univ : Finset α).filter fun a => (a, bc) ∈ H

lemma alphaFiber_offDiag_eq (H : Finset (α × (β × γ))) (bc : β × γ) :
    (alphaFiber H bc).offDiag =
      (Finset.univ : Finset α).offDiag.filter fun aa =>
        (aa.1, bc) ∈ H ∧ (aa.2, bc) ∈ H := by
  ext aa
  simp [alphaFiber, Finset.mem_offDiag, and_comm, and_left_comm, and_assoc]

/-- A common slice of two different first vertices is rectangle-free whenever
the tripartite edge set is cube-free. -/
theorem commonSlice_rectangleFree (H : Finset (α × (β × γ)))
    (hfree : CubeFree H) {a₀ a₁ : α} (haa : a₀ ≠ a₁) :
    RectangleFree (commonSlice H (a₀, a₁)) := by
  intro b₀ b₁ c₀ c₁ hbb hcc h00 h01 h10 h11
  simp only [commonSlice, Finset.mem_filter, Finset.mem_univ, true_and] at h00 h01 h10 h11
  exact hfree haa hbb hcc
    h00.1 h01.1 h10.1 h11.1 h00.2 h01.2 h10.2 h11.2

/-- Count tripartite edges by their `(β,γ)` coordinate. -/
theorem card_eq_sum_alphaFiber (H : Finset (α × (β × γ))) :
    H.card = ∑ bc : β × γ, (alphaFiber H bc).card := by
  have hH : H = ((Finset.univ : Finset α).product
      (Finset.univ : Finset (β × γ))).filter fun z => z ∈ H := by
    ext z
    simp
  calc
    H.card = (((Finset.univ : Finset α).product
        (Finset.univ : Finset (β × γ))).filter fun z => z ∈ H).card := by
      rw [← hH]
    _ = ∑ z ∈ (Finset.univ : Finset α).product
        (Finset.univ : Finset (β × γ)), if z ∈ H then 1 else 0 :=
      Finset.card_filter _ _
    _ = ∑ a : α, ∑ bc : β × γ, if (a, bc) ∈ H then 1 else 0 :=
      Finset.sum_product _ _ _
    _ = ∑ bc : β × γ, ∑ a : α, if (a, bc) ∈ H then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ bc : β × γ, (alphaFiber H bc).card := by
      apply Finset.sum_congr rfl
      intro bc hbc
      unfold alphaFiber
      rw [Finset.card_filter]

/-- Double-count ordered pairs of first-coordinate vertices sharing an edge. -/
theorem sum_alphaFiber_offDiag_eq (H : Finset (α × (β × γ))) :
    (∑ bc : β × γ, ((alphaFiber H bc).offDiag).card) =
      ∑ aa ∈ (Finset.univ : Finset α).offDiag,
        (commonSlice H aa).card := by
  simp_rw [alphaFiber_offDiag_eq, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro aa haa
  unfold commonSlice
  rw [Finset.card_filter]

/-- Cauchy--Schwarz inequality for a tripartite edge set, in terms of common
slices of ordered first-coordinate pairs. -/
theorem cube_card_sq_le_commonSlices (H : Finset (α × (β × γ))) :
    H.card ^ 2 ≤ (Fintype.card β * Fintype.card γ) *
      ((∑ aa ∈ (Finset.univ : Finset α).offDiag,
          (commonSlice H aa).card) + H.card) := by
  have hcard := card_eq_sum_alphaFiber H
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (β × γ)))
    (f := fun bc => (alphaFiber H bc).card)
  have hsquares : (∑ bc : β × γ, (alphaFiber H bc).card ^ 2) =
      (∑ aa ∈ (Finset.univ : Finset α).offDiag,
        (commonSlice H aa).card) + H.card := by
    rw [← sum_alphaFiber_offDiag_eq, hcard]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro bc hbc
    rw [Finset.offDiag_card]
    have hd : (alphaFiber H bc).card ≤
        (alphaFiber H bc).card * (alphaFiber H bc).card := by
      by_cases hzero : (alphaFiber H bc).card = 0
      · simp [hzero]
      · have : 1 ≤ (alphaFiber H bc).card := Nat.one_le_iff_ne_zero.mpr hzero
        nlinarith
    rw [Nat.sub_add_cancel hd]
    ring
  rw [← hcard] at hcauchy
  rw [Finset.card_univ, Fintype.card_prod, hsquares] at hcauchy
  exact hcauchy

/-- Quantitative `K_{2,2,2}`-free inequality obtained by applying the
rectangle bound to every common slice.  Any of the three coordinates can be
chosen as the distinguished first coordinate by permuting the parts. -/
theorem cubeFree_card_sq_le (H : Finset (α × (β × γ)))
    (hfree : CubeFree H) :
    (H.card : ℝ) ^ 2 ≤
      ((Fintype.card β : ℝ) * Fintype.card γ) *
        (((Fintype.card α : ℝ) ^ 2) *
          (Fintype.card β +
            Fintype.card γ * Real.sqrt (Fintype.card β)) + H.card) := by
  have hnat := cube_card_sq_le_commonSlices H
  have hbase : (H.card : ℝ) ^ 2 ≤
      ((Fintype.card β : ℝ) * Fintype.card γ) *
        ((∑ aa ∈ (Finset.univ : Finset α).offDiag,
          (commonSlice H aa).card : ℕ) + H.card) := by
    exact_mod_cast hnat
  have hone : ∀ aa ∈ (Finset.univ : Finset α).offDiag,
      ((commonSlice H aa).card : ℝ) ≤
        Fintype.card β +
          Fintype.card γ * Real.sqrt (Fintype.card β) := by
    intro aa haa
    have hne := (Finset.mem_offDiag.mp haa).2.2
    exact rectangleFree_card_le _ (commonSlice_rectangleFree H hfree hne)
  have hsum : ((∑ aa ∈ (Finset.univ : Finset α).offDiag,
      (commonSlice H aa).card : ℕ) : ℝ) ≤
      (Fintype.card α : ℝ) ^ 2 *
        (Fintype.card β +
          Fintype.card γ * Real.sqrt (Fintype.card β)) := by
    push_cast
    calc
      ∑ aa ∈ (Finset.univ : Finset α).offDiag,
          ((commonSlice H aa).card : ℝ)
        ≤ ∑ _aa ∈ (Finset.univ : Finset α).offDiag,
            ((Fintype.card β : ℝ) +
              Fintype.card γ * Real.sqrt (Fintype.card β)) := by
          exact Finset.sum_le_sum hone
      _ = (((Finset.univ : Finset α).offDiag).card : ℝ) *
          ((Fintype.card β : ℝ) +
            Fintype.card γ * Real.sqrt (Fintype.card β)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card α : ℝ) ^ 2 *
          (Fintype.card β +
            Fintype.card γ * Real.sqrt (Fintype.card β)) := by
          gcongr
          have hcard : ((Finset.univ : Finset α).offDiag).card ≤
              Fintype.card α ^ 2 := by
            rw [pow_two, Finset.offDiag_card, Finset.card_univ]
            exact Nat.sub_le _ _
          exact_mod_cast hcard
  calc
    (H.card : ℝ) ^ 2 ≤
        ((Fintype.card β : ℝ) * Fintype.card γ) *
          (((∑ aa ∈ (Finset.univ : Finset α).offDiag,
            (commonSlice H aa).card : ℕ) : ℝ) + H.card) := hbase
    _ ≤ _ := by gcongr

/-- Solved form of the cube-free inequality, convenient for dyadic sums. -/
theorem cubeFree_card_le_explicit (H : Finset (α × (β × γ)))
    (hfree : CubeFree H) :
    (H.card : ℝ) ≤
      (Fintype.card β : ℝ) * Fintype.card γ +
      (Fintype.card α : ℝ) *
        Real.sqrt ((Fintype.card β : ℝ) * Fintype.card γ *
          (Fintype.card β +
            Fintype.card γ * Real.sqrt (Fintype.card β))) := by
  let e : ℝ := H.card
  let A : ℝ := Fintype.card β * Fintype.card γ
  let B : ℝ := (Fintype.card α : ℝ) ^ 2 *
    (Fintype.card β + Fintype.card γ * Real.sqrt (Fintype.card β))
  have hmain0 := cubeFree_card_sq_le H hfree
  have hmain : e ^ 2 ≤ A * (B + e) := by
    simpa [e, A, B] using hmain0
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hs := Real.sq_sqrt hAB
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hroot : e ≤ A + Real.sqrt (A * B) := by
    by_contra h
    have hgt : A + Real.sqrt (A * B) < e := lt_of_not_ge h
    have hs0 : 0 ≤ Real.sqrt (A * B) := Real.sqrt_nonneg _
    nlinarith
  have hα : (0 : ℝ) ≤ Fintype.card α := by positivity
  have hsqrt : Real.sqrt (A * B) =
      (Fintype.card α : ℝ) *
        Real.sqrt ((Fintype.card β : ℝ) * Fintype.card γ *
          (Fintype.card β +
            Fintype.card γ * Real.sqrt (Fintype.card β))) := by
    dsimp [A, B]
    rw [show ((Fintype.card β : ℝ) * Fintype.card γ) *
        ((Fintype.card α : ℝ) ^ 2 *
          (Fintype.card β + Fintype.card γ * Real.sqrt (Fintype.card β))) =
        (Fintype.card α : ℝ) ^ 2 *
          ((Fintype.card β : ℝ) * Fintype.card γ *
            (Fintype.card β + Fintype.card γ * Real.sqrt (Fintype.card β))) by ring,
      Real.sqrt_mul (sq_nonneg (Fintype.card α : ℝ)),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hα]
  rw [hsqrt] at hroot
  simpa [e, A] using hroot

end CubeBound

end Erdos796
