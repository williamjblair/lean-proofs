import Research.EdgeDigits

namespace Erdos123

/-- Total value of the fixed `c-1`-term edge block before translating it to a
larger homogeneous degree. -/
def edgeDigitMass (a b c : ℕ) : ℕ :=
  (Finset.range (c - 1)).sum (correctionTerm c a b (c - 1))

/-- Every nested digit is bounded by the translated mass of the full reserved
edge block. -/
theorem edgeDigit_le_mass {a b c E r : ℕ} (hr : r ≤ c - 1) :
    edgeDigit a b c E r ≤
      a ^ (E - edgeDigitDepth c) * edgeDigitMass a b c := by
  have hsub : Finset.range r ⊆ Finset.range (c - 1) := by
    intro t ht
    simp only [Finset.mem_range] at ht ⊢
    omega
  have hsum := Finset.sum_le_sum_of_subset (f := correctionTerm c a b (c - 1)) hsub
  rw [edgeDigit, edgeDigitMass]
  simp only [edgeDigitTerm, ← Finset.mul_sum]
  exact Nat.mul_le_mul_left _ hsum

private theorem geom_edge_sum_le_pow {a c n : ℕ} (hac : a < c) :
    (Finset.range n).sum (fun i => c ^ i * a ^ (n - 1 - i)) ≤ c ^ n := by
  let S := (Finset.range n).sum (fun i => c ^ i * a ^ (n - 1 - i))
  have hgeom : S * (c - a) = c ^ n - a ^ n := by
    dsimp [S]
    exact geom_sum₂_mul_of_ge (Nat.le_of_lt hac) n
  have hfactor : 1 ≤ c - a := by omega
  have hSleMul : S ≤ S * (c - a) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left S hfactor
  rw [hgeom] at hSleMul
  exact hSleMul.trans (Nat.sub_le _ _)

/-- Uniform carry bound for the homogeneous edge radix code. Although it has
`c^n` different residue words, every evaluation is at most a fixed block mass
times `c^n`. -/
theorem edgeCodeEval_le_mass_mul_pow {a b c n : ℕ} (hac : a < c)
    (word : Fin n → Fin c) :
    edgeCodeEval a b c n word ≤ edgeDigitMass a b c * c ^ n := by
  rw [edgeCodeEval, radixEval]
  calc
    (∑ i : Fin n, c ^ (i : ℕ) *
        edgeDigit a b c (edgeCodeDegree c n i) (word i : ℕ))
        ≤ ∑ i : Fin n, c ^ (i : ℕ) *
          (a ^ (n - 1 - (i : ℕ)) * edgeDigitMass a b c) := by
            apply Finset.sum_le_sum
            intro i _hi
            apply Nat.mul_le_mul_left
            have hr : (word i : ℕ) ≤ c - 1 := by omega
            have h := edgeDigit_le_mass
              (a := a) (b := b) (c := c) (E := edgeCodeDegree c n i) hr
            have hdeg : edgeCodeDegree c n i - edgeDigitDepth c =
                n - 1 - (i : ℕ) := by
              simp [edgeCodeDegree]
            simpa [hdeg] using h
    _ = edgeDigitMass a b c *
        (∑ i : Fin n, c ^ (i : ℕ) * a ^ (n - 1 - (i : ℕ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          ac_rfl
    _ = edgeDigitMass a b c *
        (Finset.range n).sum (fun i => c ^ i * a ^ (n - 1 - i)) := by
          congr 1
          exact Fin.sum_univ_eq_sum_range
            (fun i : ℕ => c ^ i * a ^ (n - 1 - i)) n
    _ ≤ edgeDigitMass a b c * c ^ n :=
      Nat.mul_le_mul_left _ (geom_edge_sum_le_pow hac)

/-- The complete residue code and its uniform carry bound force two distinct
homogeneous subset evaluations to differ by a positive constant bounded only
by the fixed edge-block mass, independently of the level depth. -/
theorem edgeCode_bounded_difference {a b c n : ℕ}
    (hc : 1 < c) (hac : a < c)
    (hca : Nat.Coprime c a) (hcb : Nat.Coprime c b)
    (hn : edgeDigitMass a b c + 2 ≤ c ^ n) :
    ∃ x y : Fin n → Fin c, x ≠ y ∧
      0 < Nat.dist (edgeCodeEval a b c n x) (edgeCodeEval a b c n y) ∧
      Nat.dist (edgeCodeEval a b c n x) (edgeCodeEval a b c n y) ≤
        edgeDigitMass a b c + 1 := by
  let Q := c ^ n
  let A := edgeDigitMass a b c
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  let residue : (Fin n → Fin c) → Fin Q := fun w =>
    ⟨edgeCodeEval a b c n w % Q, Nat.mod_lt _ hQ⟩
  have hresInj : Function.Injective residue := by
    intro x y hxy
    apply edgeCodeEval_mod_injective hc hca hcb
    exact congrArg Fin.val hxy
  have hcard : Fintype.card (Fin n → Fin c) = Fintype.card (Fin Q) := by
    simp [Q]
  have hresSurj : Function.Surjective residue :=
    (Fintype.bijective_iff_injective_and_card residue).2 ⟨hresInj, hcard⟩ |>.2
  let liftResidue : Fin Q → (Fin n → Fin c) := fun r =>
    Classical.choose (hresSurj r)
  have hlift (r : Fin Q) : residue (liftResidue r) = r :=
    Classical.choose_spec (hresSurj r)
  have hsmall : A + 2 ≤ Q := by simpa [A, Q] using hn
  let word : Fin (A + 2) → (Fin n → Fin c) := fun r =>
    liftResidue (Fin.castLE hsmall r)
  have hwordResidue (r : Fin (A + 2)) :
      edgeCodeEval a b c n (word r) % Q = (r : ℕ) := by
    have h := congrArg Fin.val (hlift (Fin.castLE hsmall r))
    simpa [residue, word] using h
  let carry : Fin (A + 2) → Fin (A + 1) := fun r =>
    ⟨edgeCodeEval a b c n (word r) / Q, by
      have heval := edgeCodeEval_le_mass_mul_pow
        (a := a) (b := b) (c := c) (n := n) hac (word r)
      have hdiv : edgeCodeEval a b c n (word r) / Q ≤ A := by
        apply Nat.div_le_of_le_mul
        simpa [A, Q, Nat.mul_comm] using heval
      exact Nat.lt_succ_of_le hdiv⟩
  obtain ⟨r, s, hrs, hcarry⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt carry (by simp)
  have hquot : edgeCodeEval a b c n (word r) / Q =
      edgeCodeEval a b c n (word s) / Q :=
    congrArg Fin.val hcarry
  have hrmod := hwordResidue r
  have hsmod := hwordResidue s
  have hrdecomp := Nat.mod_add_div (edgeCodeEval a b c n (word r)) Q
  have hsdecomp := Nat.mod_add_div (edgeCodeEval a b c n (word s)) Q
  have hwordNe : word r ≠ word s := by
    intro hws
    apply hrs
    apply Fin.ext
    rw [← hrmod, ← hsmod, hws]
  have her : (r : ℕ) + Q * (edgeCodeEval a b c n (word r) / Q) =
      edgeCodeEval a b c n (word r) := by
    simpa [hrmod] using hrdecomp
  have hes : (s : ℕ) + Q * (edgeCodeEval a b c n (word s) / Q) =
      edgeCodeEval a b c n (word s) := by
    simpa [hsmod] using hsdecomp
  rw [hquot] at her
  have hdist :
      Nat.dist (edgeCodeEval a b c n (word r))
          (edgeCodeEval a b c n (word s)) =
        Nat.dist (r : ℕ) (s : ℕ) := by
    by_cases hle : (r : ℕ) ≤ (s : ℕ)
    · have hevalle : edgeCodeEval a b c n (word r) ≤
          edgeCodeEval a b c n (word s) := by omega
      rw [Nat.dist_eq_sub_of_le hevalle, Nat.dist_eq_sub_of_le hle]
      omega
    · have hle' : (s : ℕ) ≤ (r : ℕ) := by omega
      have hevalle : edgeCodeEval a b c n (word s) ≤
          edgeCodeEval a b c n (word r) := by omega
      rw [Nat.dist_eq_sub_of_le_right hevalle,
        Nat.dist_eq_sub_of_le_right hle']
      omega
  refine ⟨word r, word s, hwordNe, ?_, ?_⟩
  · rw [hdist]
    have hvalNe : (r : ℕ) ≠ (s : ℕ) := fun h => hrs (Fin.ext h)
    simp only [Nat.dist]
    omega
  · rw [hdist]
    have hrBound : (r : ℕ) ≤ A + 1 := by omega
    have hsBound : (s : ℕ) ≤ A + 1 := by omega
    simp only [Nat.dist]
    omega

end Erdos123
