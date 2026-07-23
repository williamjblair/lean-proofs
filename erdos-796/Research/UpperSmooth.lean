import Research.UpperExtraction

namespace Erdos796

/-- Three distinct unordered representations of one product contradict the
original admissibility condition. -/
theorem three_unordered_representations_not_admissible
    {A : Finset ℕ} {x₁ y₁ x₂ y₂ x₃ y₃ m : ℕ}
    (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ A)
    (hx₂ : x₂ ∈ A) (hy₂ : y₂ ∈ A)
    (hx₃ : x₃ ∈ A) (hy₃ : y₃ ∈ A)
    (hne₁ : x₁ ≠ y₁) (hne₂ : x₂ ≠ y₂) (hne₃ : x₃ ≠ y₃)
    (hprod₁ : x₁ * y₁ = m) (hprod₂ : x₂ * y₂ = m)
    (hprod₃ : x₃ * y₃ = m)
    (h₁₂ : sortedPair x₁ y₁ ≠ sortedPair x₂ y₂)
    (h₁₃ : sortedPair x₁ y₁ ≠ sortedPair x₃ y₃)
    (h₂₃ : sortedPair x₂ y₂ ≠ sortedPair x₃ y₃) :
    ¬ HasRepBound 3 A := by
  intro hA
  let P : Finset (ℕ × ℕ) :=
    {sortedPair x₁ y₁, sortedPair x₂ y₂, sortedPair x₃ y₃}
  have hPcard : P.card = 3 := by
    dsimp [P]
    simp [h₁₂, h₁₃, h₂₃]
  have hsub : P ⊆ ((A ×ˢ A).filter fun z => z.1 < z.2 ∧ z.1 * z.2 = m) := by
    intro z hz
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr (by
        unfold sortedPair
        rcases le_total x₁ y₁ with h | h <;>
          simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h, hx₁, hy₁]),
        sortedPair_fst_lt_snd hne₁, by rw [sortedPair_mul, hprod₁]⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr (by
        unfold sortedPair
        rcases le_total x₂ y₂ with h | h <;>
          simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h, hx₂, hy₂]),
        sortedPair_fst_lt_snd hne₂, by rw [sortedPair_mul, hprod₂]⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr (by
        unfold sortedPair
        rcases le_total x₃ y₃ with h | h <;>
          simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h, hx₃, hy₃]),
        sortedPair_fst_lt_snd hne₃, by rw [sortedPair_mul, hprod₃]⟩
  have hcard := Finset.card_le_card hsub
  have hbound := hA m
  unfold repCount at hbound
  omega

/-- A sufficiently large integer all of whose prime factors are small has a
three-factor decomposition above the small-prime threshold. -/
theorem exists_three_large_of_primeFactors_le
    {z d : ℕ} (hz : 1 < z) (hd : z ^ 6 < d)
    (hall : ∀ p : ℕ, p.Prime → p ∣ d → p ≤ z) :
    ∃ x y w : ℕ, z < x ∧ z < y ∧ z < w ∧ d = x * y * w := by
  have hd3 : z ^ 3 < d := by
    have hzpos : 0 < z := by omega
    have hpow : z ^ 3 ≤ z ^ 6 :=
      Nat.pow_le_pow_right hzpos (by omega)
    omega
  rcases exists_large_split_of_primeFactors_le hz hd3 hall with
    ⟨a, b, ha, hb, hab⟩
  by_cases ha3 : z ^ 3 < a
  · have halla : ∀ p : ℕ, p.Prime → p ∣ a → p ≤ z := by
      intro p hp hpa
      apply hall p hp
      exact hpa.trans ⟨b, hab⟩
    rcases exists_large_split_of_primeFactors_le hz ha3 halla with
      ⟨x, y, hx, hy, haxy⟩
    exact ⟨x, y, b, hx, hy, hb, by
      calc
        d = a * b := hab
        _ = (x * y) * b := by rw [haxy]
        _ = x * y * b := by ring⟩
  · have hb3 : z ^ 3 < b := by
      by_contra h
      have ha_le : a ≤ z ^ 3 := by omega
      have hb_le : b ≤ z ^ 3 := by omega
      rw [hab] at hd
      nlinarith
    have hallb : ∀ p : ℕ, p.Prime → p ∣ b → p ≤ z := by
      intro p hp hpb
      apply hall p hp
      exact hpb.trans ⟨a, by simpa [Nat.mul_comm] using hab⟩
    rcases exists_large_split_of_primeFactors_le hz hb3 hallb with
      ⟨y, w, hy, hw, hbyw⟩
    exact ⟨a, y, w, ha, hy, hw, by
      calc
        d = a * b := hab
        _ = a * (y * w) := by rw [hbyw]
        _ = a * y * w := by ring⟩

section SmoothCube

variable {X Y Z : Type*}

/-- A canonical three-factor encoding of elements of an admissible set is
`K_{2,2,2}`-free. -/
theorem admissibleFactorHypergraph_cubeFree
    (A : Finset ℕ) (hA : HasRepBound 3 A)
    (fx : X → ℕ) (fy : Y → ℕ) (fz : Z → ℕ)
    (H : Finset (X × (Y × Z)))
    (hmem : ∀ ⦃x : X⦄ ⦃y : Y⦄ ⦃z : Z⦄,
      (x, (y, z)) ∈ H → fx x * fy y * fz z ∈ A)
    (hcanonical : ∀ ⦃x u : X⦄ ⦃y v : Y⦄ ⦃z w : Z⦄,
      (x, (y, z)) ∈ H → (u, (v, w)) ∈ H →
      fx x * fy y * fz z = fx u * fy v * fz w →
      (x, (y, z)) = (u, (v, w))) :
    CubeFree H := by
  intro x₀ x₁ y₀ y₁ z₀ z₁ hx hy hz
    h000 h001 h010 h011 h100 h101 h110 h111
  let v000 := fx x₀ * fy y₀ * fz z₀
  let v001 := fx x₀ * fy y₀ * fz z₁
  let v010 := fx x₀ * fy y₁ * fz z₀
  let v101 := fx x₁ * fy y₀ * fz z₁
  let v110 := fx x₁ * fy y₁ * fz z₀
  let v111 := fx x₁ * fy y₁ * fz z₁
  have edge_ne : ∀ ⦃a b : X × (Y × Z)⦄, a ∈ H → b ∈ H → a ≠ b →
      fx a.1 * fy a.2.1 * fz a.2.2 ≠
        fx b.1 * fy b.2.1 * fz b.2.2 := by
    intro a b ha hb hab heq
    exact hab (hcanonical ha hb heq)
  have h000_111 : v000 ≠ v111 := edge_ne h000 h111 (by
    intro h; exact hx (congrArg Prod.fst h))
  have h001_110 : v001 ≠ v110 := edge_ne h001 h110 (by
    intro h; exact hx (congrArg Prod.fst h))
  have h010_101 : v010 ≠ v101 := edge_ne h010 h101 (by
    intro h; exact hx (congrArg Prod.fst h))
  have pair_ne (a b c d : X × (Y × Z))
      (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H)
      (hac : a ≠ c) (had : a ≠ d) :
      sortedPair (fx a.1 * fy a.2.1 * fz a.2.2)
          (fx b.1 * fy b.2.1 * fz b.2.2) ≠
        sortedPair (fx c.1 * fy c.2.1 * fz c.2.2)
          (fx d.1 * fy d.2.1 * fz d.2.2) := by
    intro heq
    rcases sortedPair_eq_cases heq with hsame | hswap
    · exact (edge_ne ha hc hac) hsame.1
    · exact (edge_ne ha hd had) hswap.1
  have hp12 : sortedPair v000 v111 ≠ sortedPair v001 v110 := by
    apply pair_ne (x₀, (y₀, z₀)) (x₁, (y₁, z₁))
      (x₀, (y₀, z₁)) (x₁, (y₁, z₀)) h000 h111 h001 h110
    · intro h
      exact hz (congrArg (fun e => e.2.2) h)
    · intro h
      exact hx (congrArg Prod.fst h)
  have hp13 : sortedPair v000 v111 ≠ sortedPair v010 v101 := by
    apply pair_ne (x₀, (y₀, z₀)) (x₁, (y₁, z₁))
      (x₀, (y₁, z₀)) (x₁, (y₀, z₁)) h000 h111 h010 h101
    · intro h
      exact hy (congrArg (fun e => e.2.1) h)
    · intro h
      exact hx (congrArg Prod.fst h)
  have hp23 : sortedPair v001 v110 ≠ sortedPair v010 v101 := by
    apply pair_ne (x₀, (y₀, z₁)) (x₁, (y₁, z₀))
      (x₀, (y₁, z₀)) (x₁, (y₀, z₁)) h001 h110 h010 h101
    · intro h
      exact hy (congrArg (fun e => e.2.1) h)
    · intro h
      exact hx (congrArg Prod.fst h)
  apply (three_unordered_representations_not_admissible
    (A := A) (m := fx x₀ * fx x₁ * fy y₀ * fy y₁ * fz z₀ * fz z₁)
    (hmem h000) (hmem h111) (hmem h001) (hmem h110)
    (hmem h010) (hmem h101)
    h000_111 h001_110 h010_101)
  · ring
  · ring
  · ring
  · exact hp12
  · exact hp13
  · exact hp23
  · exact hA

/-- Quantitative bound for any injectively and canonically three-factorized
subcollection of an admissible set. -/
theorem admissibleThreeFactorEncoding_card_le
    {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (A : Finset ℕ) (hA : HasRepBound 3 A)
    (value : Δ → ℕ) (hvalue : Function.Injective value)
    (hvalueA : ∀ d : Δ, value d ∈ A)
    (enc : Δ → X × (Y × Z))
    (fx : X → ℕ) (fy : Y → ℕ) (fz : Z → ℕ)
    (hrecon : ∀ d : Δ,
      fx (enc d).1 * fy (enc d).2.1 * fz (enc d).2.2 = value d) :
    (Fintype.card Δ : ℝ) ≤
      (Fintype.card Y : ℝ) * Fintype.card Z +
      (Fintype.card X : ℝ) *
        Real.sqrt ((Fintype.card Y : ℝ) * Fintype.card Z *
          (Fintype.card Y +
            Fintype.card Z * Real.sqrt (Fintype.card Y))) := by
  let H : Finset (X × (Y × Z)) := Finset.univ.image enc
  have henc : Function.Injective enc := by
    intro d e hde
    apply hvalue
    rw [← hrecon d, ← hrecon e, hde]
  have hHcard : H.card = Fintype.card Δ := by
    unfold H
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro d hd e he hde
      exact henc hde
  have hmem : ∀ ⦃x : X⦄ ⦃y : Y⦄ ⦃z : Z⦄,
      (x, (y, z)) ∈ H → fx x * fy y * fz z ∈ A := by
    intro x y z hxyz
    rcases Finset.mem_image.mp hxyz with ⟨d, hd, heq⟩
    have hdA := hvalueA d
    rw [← hrecon d] at hdA
    simpa [heq] using hdA
  have hcanonical : ∀ ⦃x u : X⦄ ⦃y v : Y⦄ ⦃z w : Z⦄,
      (x, (y, z)) ∈ H → (u, (v, w)) ∈ H →
      fx x * fy y * fz z = fx u * fy v * fz w →
      (x, (y, z)) = (u, (v, w)) := by
    intro x u y v z w hxyz huv heq
    rcases Finset.mem_image.mp hxyz with ⟨d, hd, hdenc⟩
    rcases Finset.mem_image.mp huv with ⟨e, he, heenc⟩
    have hval : value d = value e := by
      rw [← hrecon d, ← hrecon e, hdenc, heenc]
      exact heq
    have hde := hvalue hval
    subst e
    exact hdenc.symm.trans heenc
  have hfree := admissibleFactorHypergraph_cubeFree
    A hA fx fy fz H hmem hcanonical
  rw [← hHcard]
  exact cubeFree_card_le_explicit H hfree

end SmoothCube

end Erdos796
