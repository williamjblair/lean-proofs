import Research.Definitions

namespace Erdos123

/-- Multiply every member of a finite set by a common factor. -/
def scaleFinset (a : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.image (fun x => a * x)

private theorem scaleFinset_injOn {a : ℕ} (ha : 0 < a) (s : Finset ℕ) :
    Set.InjOn (fun x : ℕ => a * x) (s : Set ℕ) := by
  intro x _hx y _hy hxy
  exact Nat.eq_of_mul_eq_mul_left ha hxy

/-- Core gluing lemma for the Erdős--Lewin induction. A primitive old
representation may be scaled by `a` and joined to a primitive correction set,
provided every old term is smaller than every correction term and correction
terms are coprime to `a`. -/
theorem isPrimitive_scaleFinset_union {a : ℕ} {s t : Finset ℕ}
    (ha : 1 < a)
    (hsPos : ∀ x ∈ s, 0 < x)
    (hsPrimitive : IsPrimitive s)
    (htPrimitive : IsPrimitive t)
    (htCoprime : ∀ y ∈ t, Nat.Coprime a y)
    (hsep : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    IsPrimitive (scaleFinset a s ∪ t) := by
  intro z hz w hw hzw hdvd
  rcases Finset.mem_union.mp hz with hzs | hzt
  · rcases Finset.mem_image.mp hzs with ⟨x, hx, rfl⟩
    rcases Finset.mem_union.mp hw with hws | hwt
    · rcases Finset.mem_image.mp hws with ⟨y, hy, rfl⟩
      apply hsPrimitive hx hy
      · intro hxy
        subst y
        exact hzw rfl
      · exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < a)).mp hdvd
    · have haDiv : a ∣ w := (dvd_mul_right a x).trans hdvd
      have haOne := (htCoprime w hwt).eq_one_of_dvd haDiv
      omega
  · rcases Finset.mem_union.mp hw with hws | hwt
    · rcases Finset.mem_image.mp hws with ⟨y, hy, rfl⟩
      have hzDivY : z ∣ y := (htCoprime z hzt).symm.dvd_of_dvd_mul_left hdvd
      have hzLeY : z ≤ y := Nat.le_of_dvd (hsPos y hy) hzDivY
      exact (Nat.not_lt_of_ge hzLeY) (hsep y hy z hzt)
    · exact htPrimitive hzt hwt hzw hdvd

/-- Sharper gluing criterion. Numerical separation is not necessary: it is
enough that no correction term divides an old term. The reverse cross-direction
is excluded automatically because old terms are scaled by `a`, whereas every
correction is coprime to `a`. -/
theorem isPrimitive_scaleFinset_union_of_not_dvd {a : ℕ} {s t : Finset ℕ}
    (ha : 1 < a)
    (hsPrimitive : IsPrimitive s)
    (htPrimitive : IsPrimitive t)
    (htCoprime : ∀ y ∈ t, Nat.Coprime a y)
    (hcross : ∀ x ∈ s, ∀ y ∈ t, ¬ y ∣ x) :
    IsPrimitive (scaleFinset a s ∪ t) := by
  intro z hz w hw hzw hdvd
  rcases Finset.mem_union.mp hz with hzs | hzt
  · rcases Finset.mem_image.mp hzs with ⟨x, hx, rfl⟩
    rcases Finset.mem_union.mp hw with hws | hwt
    · rcases Finset.mem_image.mp hws with ⟨y, hy, rfl⟩
      apply hsPrimitive hx hy
      · intro hxy
        subst y
        exact hzw rfl
      · exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < a)).mp hdvd
    · have haDiv : a ∣ w := (dvd_mul_right a x).trans hdvd
      have haOne := (htCoprime w hwt).eq_one_of_dvd haDiv
      omega
  · rcases Finset.mem_union.mp hw with hws | hwt
    · rcases Finset.mem_image.mp hws with ⟨y, hy, rfl⟩
      have hzDivY : z ∣ y := (htCoprime z hzt).symm.dvd_of_dvd_mul_left hdvd
      exact hcross y hy z hzt hzDivY
    · exact htPrimitive hzt hwt hzw hdvd

/-- The scaled old set and a coprime correction set are disjoint. -/
theorem disjoint_scaleFinset_correction {a : ℕ} {s t : Finset ℕ}
    (ha : 1 < a) (htCoprime : ∀ y ∈ t, Nat.Coprime a y) :
    Disjoint (scaleFinset a s) t := by
  rw [Finset.disjoint_left]
  intro y hyScale hyT
  rcases Finset.mem_image.mp hyScale with ⟨x, _hx, rfl⟩
  have haDiv : a ∣ a * x := dvd_mul_right a x
  have haOne := (htCoprime (a * x) hyT).eq_one_of_dvd haDiv
  omega

/-- Exact sum formula for adjoining a correction set after scaling. -/
theorem sum_scaleFinset_union {a : ℕ} {s t : Finset ℕ}
    (ha : 1 < a) (htCoprime : ∀ y ∈ t, Nat.Coprime a y) :
    (scaleFinset a s ∪ t).sum id = a * s.sum id + t.sum id := by
  rw [Finset.sum_union (disjoint_scaleFinset_correction ha htCoprime)]
  congr 1
  unfold scaleFinset
  rw [Finset.sum_image (scaleFinset_injOn (by omega) s)]
  simpa only [id_eq] using (Finset.mul_sum s id a).symm

/-- One exact representation-extension step. -/
theorem primitive_representation_extension {a m B : ℕ} {s t : Finset ℕ}
    (ha : 1 < a)
    (hsPos : ∀ x ∈ s, 0 < x)
    (hsPrimitive : IsPrimitive s)
    (hsSum : s.sum id = m)
    (htPrimitive : IsPrimitive t)
    (htCoprime : ∀ y ∈ t, Nat.Coprime a y)
    (hsep : ∀ x ∈ s, ∀ y ∈ t, x < y)
    (htSum : t.sum id = B) :
    ∃ u : Finset ℕ, IsPrimitive u ∧ u.sum id = a * m + B := by
  refine ⟨scaleFinset a s ∪ t,
    isPrimitive_scaleFinset_union ha hsPos hsPrimitive htPrimitive htCoprime hsep, ?_⟩
  rw [sum_scaleFinset_union ha htCoprime, hsSum, htSum]

end Erdos123
