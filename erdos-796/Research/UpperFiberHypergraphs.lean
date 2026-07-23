import Research.UpperStructure

namespace Erdos796

/-- Sort a pair of natural numbers into the unique increasing order. -/
def sortedPair (a b : ℕ) : ℕ × ℕ := (min a b, max a b)

lemma sortedPair_eq_cases {a b c d : ℕ}
    (h : sortedPair a b = sortedPair c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases le_total a b with hab | hba <;>
    rcases le_total c d with hcd | hdc
  · left
    simpa [sortedPair, min_eq_left hab, max_eq_right hab,
      min_eq_left hcd, max_eq_right hcd] using Prod.mk.inj h
  · right
    simpa [sortedPair, min_eq_left hab, max_eq_right hab,
      min_eq_right hdc, max_eq_left hdc] using Prod.mk.inj h
  · right
    have hp : b = c ∧ a = d := by
      simpa [sortedPair, min_eq_right hba, max_eq_left hba,
        min_eq_left hcd, max_eq_right hcd] using Prod.mk.inj h
    exact ⟨hp.2, hp.1⟩
  · left
    have hp : b = d ∧ a = c := by
      simpa [sortedPair, min_eq_right hba, max_eq_left hba,
        min_eq_right hdc, max_eq_left hdc] using Prod.mk.inj h
    exact ⟨hp.2, hp.1⟩

lemma sortedPair_fst_lt_snd {a b : ℕ} (h : a ≠ b) :
    (sortedPair a b).1 < (sortedPair a b).2 := by
  unfold sortedPair
  omega

lemma sortedPair_mul (a b : ℕ) :
    (sortedPair a b).1 * (sortedPair a b).2 = a * b := by
  unfold sortedPair
  rcases le_total a b with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h, Nat.mul_comm]

/-- Extract cores at one putative large-prime label. -/
def extractedFiber (A : Finset ℕ) (K q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter fun d => q * d ∈ A

/-- Fibers extracted from an admissible set at two distinct prime labels above
the core cutoff are cross-compatible. -/
theorem extractedFiber_crossCompatible
    {A : Finset ℕ} {K q r : ℕ}
    (hA : HasRepBound 3 A)
    (hqK : K < q) (hrK : K < r)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) :
    CrossCompatible (extractedFiber A K q) (extractedFiber A K r) := by
  apply Finset.sup_le
  intro m hm
  let S := extractedFiber A K q
  let T := extractedFiber A K r
  let P := (S ×ˢ T).filter fun z => z.1 * z.2 = m
  let target := q * r * m
  let phi : ℕ × ℕ → ℕ × ℕ := fun z => sortedPair (q * z.1) (r * z.2)
  have hactual_ne : ∀ z ∈ P, q * z.1 ≠ r * z.2 := by
    intro z hz heq
    have hz' := Finset.mem_filter.mp hz
    have hdS := Finset.mem_product.mp hz'.1
    have hd := Finset.mem_filter.mp hdS.1
    have he := Finset.mem_filter.mp hdS.2
    have huniq := large_prime_core_decomposition_unique hqK hrK hq hr
      (Finset.mem_Icc.mp he.1).1 (Finset.mem_Icc.mp he.1).2 heq
    exact hqr huniq.1
  have hphi_inj : Set.InjOn phi P := by
    intro z hz w hw hzw
    rcases z with ⟨d, e⟩
    rcases w with ⟨d', e'⟩
    change sortedPair (q * d) (r * e) =
      sortedPair (q * d') (r * e') at hzw
    rcases sortedPair_eq_cases hzw with hsame | hswap
    · have hdd : d = d' := Nat.mul_left_cancel hq.pos hsame.1
      have hee : e = e' := Nat.mul_left_cancel hr.pos hsame.2
      exact Prod.ext hdd hee
    · have hw' := Finset.mem_filter.mp hw
      have hde := Finset.mem_product.mp hw'.1
      have he'T := Finset.mem_filter.mp hde.2
      have huniq := large_prime_core_decomposition_unique hqK hrK hq hr
        (Finset.mem_Icc.mp he'T.1).1 (Finset.mem_Icc.mp he'T.1).2 hswap.1
      exact (hqr huniq.1).elim
  have himage_card : (P.image phi).card = P.card :=
    Finset.card_image_of_injOn hphi_inj
  have hsub : P.image phi ⊆
      ((A ×ˢ A).filter fun z => z.1 < z.2 ∧ z.1 * z.2 = target) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨de, hde, rfl⟩
    have hde' := Finset.mem_filter.mp hde
    have hdST := Finset.mem_product.mp hde'.1
    have hdS := Finset.mem_filter.mp hdST.1
    have heT := Finset.mem_filter.mp hdST.2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      dsimp [phi, sortedPair]
      rcases le_total (q * de.1) (r * de.2) with hle | hle
      · simp [min_eq_left hle, max_eq_right hle, hdS.2, heT.2]
      · simp [min_eq_right hle, max_eq_left hle, hdS.2, heT.2]
    · constructor
      · exact sortedPair_fst_lt_snd (hactual_ne de hde)
      · rw [sortedPair_mul]
        dsimp [target]
        calc
          q * de.1 * (r * de.2) = q * r * (de.1 * de.2) := by ring
          _ = q * r * m := by rw [hde'.2]
  have hcard := Finset.card_le_card hsub
  have hrep : repCount A target < 3 := hA target
  unfold repCount at hrep
  unfold crossRepCount
  change P.card ≤ 2
  rw [← himage_card]
  omega

section FiberHypergraphs

variable {Q X Y P : Type*}
  [DecidableEq Q] [DecidableEq X] [DecidableEq Y] [DecidableEq P]

/-- A canonical factor graph for one self-compatible fiber is
rectangle-free. -/
theorem canonicalFactorGraph_rectangleFree
    (S : Finset ℕ) (fx : X → ℕ) (fy : Y → ℕ)
    (E : Finset (X × Y))
    (hcompat : CrossCompatible S S)
    (hmem : ∀ ⦃x : X⦄ ⦃y : Y⦄, (x, y) ∈ E → fx x * fy y ∈ S)
    (hcanonical : ∀ ⦃x u : X⦄ ⦃y v : Y⦄,
      (x, y) ∈ E → (u, v) ∈ E →
      fx x * fy y = fx u * fy v → (x, y) = (u, v)) :
    RectangleFree E := by
  intro x u y v hxu hyv hxy hxv huy huv
  have h00_ne_01 : fx x * fy y ≠ fx x * fy v := by
    intro h
    exact hyv (Prod.mk.inj (hcanonical hxy hxv h)).2
  have h00_ne_11 : fx x * fy y ≠ fx u * fy v := by
    intro h
    exact hxu (Prod.mk.inj (hcanonical hxy huv h)).1
  have h01_ne_11 : fx x * fy v ≠ fx u * fy v := by
    intro h
    exact hxu (Prod.mk.inj (hcanonical hxv huv h)).1
  exact (factor_rectangle_not_compatible
    (S := S) (T := S)
    (hmem hxy) (hmem hxv) (hmem huy) (hmem huv)
    (hmem hxy) (hmem hxv) (hmem huy) (hmem huv)
    h00_ne_01 h00_ne_11 h01_ne_11) hcompat

/-- Any injective finite family with a canonical factor encoding inside a
self-compatible core satisfies the quantitative rectangle-free bound. -/
theorem factorEncoding_card_le
    {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    [Fintype X] [Fintype Y]
    (S : Finset ℕ) (hcompat : CrossCompatible S S)
    (value : Δ → ℕ) (hvalue : Function.Injective value)
    (hvalueS : ∀ z : Δ, value z ∈ S)
    (enc : Δ → X × Y) (fx : X → ℕ) (fy : Y → ℕ)
    (hrecon : ∀ z : Δ, fx (enc z).1 * fy (enc z).2 = value z) :
    (Fintype.card Δ : ℝ) ≤ Fintype.card X +
      Fintype.card Y * Real.sqrt (Fintype.card X) := by
  let E : Finset (X × Y) := Finset.univ.image enc
  have henc : Function.Injective enc := by
    intro z w hzw
    apply hvalue
    rw [← hrecon z, ← hrecon w, hzw]
  have hEcard : E.card = Fintype.card Δ := by
    unfold E
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro z hz w hw hzw
      exact henc hzw
  have hmem : ∀ ⦃x : X⦄ ⦃y : Y⦄, (x, y) ∈ E → fx x * fy y ∈ S := by
    intro x y hxy
    rcases Finset.mem_image.mp hxy with ⟨z, hz, heq⟩
    have hzS := hvalueS z
    rw [← hrecon z] at hzS
    simpa [heq] using hzS
  have hcanonical : ∀ ⦃x u : X⦄ ⦃y v : Y⦄,
      (x, y) ∈ E → (u, v) ∈ E →
      fx x * fy y = fx u * fy v → (x, y) = (u, v) := by
    intro x u y v hxy huv heq
    rcases Finset.mem_image.mp hxy with ⟨z, hz, hzxy⟩
    rcases Finset.mem_image.mp huv with ⟨w, hw, hwuv⟩
    have hvw : value z = value w := by
      rw [← hrecon z, ← hrecon w, hzxy, hwuv]
      exact heq
    have hzw := hvalue hvw
    subst w
    exact hzxy.symm.trans hwuv
  have hfree := canonicalFactorGraph_rectangleFree S fx fy E hcompat hmem hcanonical
  rw [← hEcard]
  exact rectangleFree_card_le E hfree

/-- A canonically factorized collection of cores from pairwise-compatible
fibers is cube-free.  This is the abstract bridge from the multiplicative
problem to `cubeFree_card_sq_le`. -/
theorem fiberFactorHypergraph_cubeFree
    (D : Q → Finset ℕ) (fx : X → ℕ) (fy : Y → ℕ)
    (H : Finset (Q × (X × Y)))
    (hcompat : ∀ ⦃q r : Q⦄, q ≠ r → CrossCompatible (D q) (D r))
    (hmem : ∀ ⦃q : Q⦄ ⦃x : X⦄ ⦃y : Y⦄,
      (q, (x, y)) ∈ H → fx x * fy y ∈ D q)
    (hcanonical : ∀ ⦃q : Q⦄ ⦃x u : X⦄ ⦃y v : Y⦄,
      (q, (x, y)) ∈ H → (q, (u, v)) ∈ H →
      fx x * fy y = fx u * fy v → (x, y) = (u, v)) :
    CubeFree H := by
  intro q r x u y v hqr hxu hyv hqxy hqxv hquy hquv
    hrxy hrxv hruy hruv
  have h00_ne_01 : fx x * fy y ≠ fx x * fy v := by
    intro h
    have hp := hcanonical hqxy hqxv h
    exact hyv (Prod.mk.inj hp).2
  have h00_ne_11 : fx x * fy y ≠ fx u * fy v := by
    intro h
    have hp := hcanonical hqxy hquv h
    exact hxu (Prod.mk.inj hp).1
  have h01_ne_11 : fx x * fy v ≠ fx u * fy v := by
    intro h
    have hp := hcanonical hqxv hquv h
    exact hxu (Prod.mk.inj hp).1
  have hnot := factor_rectangle_not_compatible
    (S := D q) (T := D r)
    (a₀ := fx x) (a₁ := fx u) (b₀ := fy y) (b₁ := fy v)
    (hmem hqxy) (hmem hqxv) (hmem hquy) (hmem hquv)
    (hmem hrxy) (hmem hrxv) (hmem hruy) (hmem hruv)
    h00_ne_01 h00_ne_11 h01_ne_11
  exact hnot (hcompat hqr)

/-- For fixed distinct coefficients `t,u`, the cells `(q,p)` at which both
prime-ray cores occur form a rectangle-free bipartite graph. -/
theorem primeRayIncidence_rectangleFree
    (D : Q → Finset ℕ) (primeValue : P → ℕ)
    (E : Finset (Q × P)) {W t u : ℕ}
    (ht : 0 < t) (hu : 0 < u) (htW : t ≤ W) (huW : u ≤ W)
    (htu : t ≠ u)
    (hprime : ∀ p : P, W < primeValue p ∧ (primeValue p).Prime)
    (hprime_inj : Function.Injective primeValue)
    (hcompat : ∀ ⦃q r : Q⦄, q ≠ r → CrossCompatible (D q) (D r))
    (hmem : ∀ ⦃q : Q⦄ ⦃p : P⦄, (q, p) ∈ E →
      t * primeValue p ∈ D q ∧ u * primeValue p ∈ D q) :
    RectangleFree E := by
  intro q r p s hqr hps hqp hqs hrp hrs
  have hp_ne : primeValue p ≠ primeValue s := fun h => hps (hprime_inj h)
  have hnot := prime_ray_rectangle_not_compatible
    (S := D q) (T := D r) (W := W) (t := t) (u := u)
    ht hu htW huW htu
    (hprime p).1 (hprime s).1 (hprime p).2 (hprime s).2 hp_ne
    (hmem hqp).1 (hmem hqp).2 (hmem hqs).1 (hmem hqs).2
    (hmem hrp).1 (hmem hrp).2 (hmem hrs).1 (hmem hrs).2
  exact hnot (hcompat hqr)

end FiberHypergraphs

end Erdos796
