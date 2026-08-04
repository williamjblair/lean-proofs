import Research.TriangularShells

/-!
# A 38-point counterexample at the triangular shell `t = 3`

Exact rational rounding of a Packomania 38-circle configuration.  After scaling,
all mutual distances are at least one, while one point has all 37 other points
at ordinary distance strictly below three.  The triangular lattice has only 36
nonzero points at distance at most three.
-/

namespace Research

/-- Six-decimal integer coordinates, with point 18 translated to the origin. -/
def packing38Raw : Fin 38 → ℤ × ℤ := ![
  (91933, -851412),
  (-194812, -833908),
  (368332, -773101),
  (-459633, -722559),
  (603280, -607789),
  (74050, -564691),
  (-212695, -547186),
  (-672729, -529896),
  (347572, -476859),
  (770337, -374078),
  (-436256, -366772),
  (-44821, -303159),
  (-810119, -277600),
  (514630, -243149),
  (228701, -215328),
  (-273883, -129783),
  (-573645, -114476),
  (850704, -98270),
  (0, 0),
  (-856340, 5936),
  (593849, 32991),
  (307921, 60812),
  (-411273, 122513),
  (835335, 188597),
  (-159864, 261518),
  (126564, 283609),
  (-806193, 288803),
  (480249, 300690),
  (-534464, 382037),
  (725961, 454240),
  (288651, 520795),
  (-283055, 521042),
  (3826, 567619),
  (534890, 668765),
  (-534201, 669315),
  (283625, 808029),
  (-282792, 808321),
  (441, 856361)
]

/-- Squared numerator after scaling every coordinate by `349 / 100000000`. -/
def packing38SqNum (i j : Fin 38) : ℤ :=
  (349 * ((packing38Raw i).1 - (packing38Raw j).1)) ^ 2 +
  (349 * ((packing38Raw i).2 - (packing38Raw j).2)) ^ 2

/-- Exact finite census: every distinct pair has squared numerator at least
`10^16`, hence distance at least one after scaling. -/
theorem packing38SqNum_separated :
    ∀ i j : Fin 38, i ≠ j → (10000000000000000 : ℤ) ≤ packing38SqNum i j := by
  decide

/-- Exact finite census: all 37 noncentral points have squared numerator below
`9·10^16`, hence distance strictly below three from point 18. -/
theorem packing38SqNum_center_lt_nine :
    ∀ i : Fin 38, i ≠ 18 →
      packing38SqNum i 18 < (90000000000000000 : ℤ) := by
  decide

/-- The exact real planar realization. -/
noncomputable def packing38 (i : Fin 38) : ℝ × ℝ :=
  (((349 * (packing38Raw i).1 : ℤ) : ℝ) / 100000000,
   ((349 * (packing38Raw i).2 : ℤ) : ℝ) / 100000000)

lemma packing38_sqDist_eq (i j : Fin 38) :
    sqDist (packing38 i) (packing38 j) =
      (packing38SqNum i j : ℝ) / (100000000 : ℝ) ^ 2 := by
  simp only [packing38, packing38SqNum, sqDist, Int.cast_add, Int.cast_mul,
    Int.cast_sub, Int.cast_pow]
  ring

/-- The 38 exact real points are one-separated. -/
theorem packing38_oneSeparated :
    ∀ i j : Fin 38, i ≠ j → 1 ≤ sqDist (packing38 i) (packing38 j) := by
  intro i j hij
  have hz := packing38SqNum_separated i j hij
  have hzR : (10000000000000000 : ℝ) ≤ (packing38SqNum i j : ℝ) := by
    exact_mod_cast hz
  rw [packing38_sqDist_eq]
  norm_num at hzR ⊢
  nlinarith

/-- Every noncentral point is at squared distance strictly below nine. -/
theorem packing38_center_sqDist_lt_nine (i : Fin 38) (hi : i ≠ 18) :
    sqDist (packing38 i) (packing38 18) < 9 := by
  have hz := packing38SqNum_center_lt_nine i hi
  have hzR : (packing38SqNum i 18 : ℝ) < 90000000000000000 := by
    exact_mod_cast hz
  rw [packing38_sqDist_eq]
  norm_num at hzR ⊢
  nlinarith

/-- Consequently all 37 are at ordinary Euclidean distance strictly below 3. -/
theorem packing38_center_distance_lt_three (i : Fin 38) (hi : i ≠ 18) :
    Real.sqrt (sqDist (packing38 i) (packing38 18)) < 3 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num
  exact packing38_center_sqDist_lt_nine i hi

/-- The direct local short-neighbour finset around point 18. -/
noncomputable def packing38CenterNeighbors : Finset (Fin 38) :=
  Finset.univ.filter fun i =>
    i ≠ 18 ∧ Real.sqrt (sqDist (packing38 i) (packing38 18)) < 3

/-- The center has exactly 37 neighbours at ordinary distance below three. -/
theorem packing38CenterNeighbors_card : packing38CenterNeighbors.card = 37 := by
  have heq : packing38CenterNeighbors = Finset.univ.erase 18 := by
    ext i
    simp only [packing38CenterNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    constructor
    · exact fun h => ⟨h.1, by simp⟩
    · rintro ⟨hi, _⟩
      exact ⟨hi, packing38_center_distance_lt_three i hi⟩
  rw [heq, Finset.card_erase_of_mem (by simp)]
  norm_num

/-- Source-facing shell counterexample: the exact one-separated configuration
has 37 local neighbours below `t=3`, whereas the triangular-lattice comparison
value at `t=3` is 36. -/
theorem triangular_shell_three_local_bound_false :
    (∀ i j : Fin 38, i ≠ j →
      1 ≤ sqDist (packing38 i) (packing38 j)) ∧
    packing38CenterNeighbors.card = 37 ∧
    (triCoordsWithin 9).card = 36 ∧
    (triCoordsWithin 9).card < packing38CenterNeighbors.card := by
  refine ⟨packing38_oneSeparated, packing38CenterNeighbors_card,
    triCoordsWithin_nine_card, ?_⟩
  rw [packing38CenterNeighbors_card, triCoordsWithin_nine_card]
  norm_num

/-- A simple uniform coordinate bound used to separate translated copies. -/
theorem packing38_coord_abs_le_four (i : Fin 38) :
    |(packing38 i).1| ≤ 4 ∧ |(packing38 i).2| ≤ 4 := by
  fin_cases i <;> norm_num [packing38, packing38Raw, abs_of_nonneg, abs_of_nonpos]

/-- `m` translated copies, twenty units apart in the horizontal direction. -/
noncomputable def packing38Blocks (m : ℕ) (q : Fin m × Fin 38) : ℝ × ℝ :=
  (20 * (q.1.val : ℝ) + (packing38 q.2).1, (packing38 q.2).2)

/-- Every replicated configuration remains one-separated. -/
theorem packing38Blocks_oneSeparated (m : ℕ) :
    ∀ q s : Fin m × Fin 38, q ≠ s →
      1 ≤ sqDist (packing38Blocks m q) (packing38Blocks m s) := by
  intro q s hqs
  by_cases hb : q.1 = s.1
  · have hi : q.2 ≠ s.2 := by
      intro hi
      exact hqs (Prod.ext hb hi)
    have h := packing38_oneSeparated q.2 s.2 hi
    simp only [packing38Blocks, sqDist] at h ⊢
    rw [hb]
    convert h using 1 <;> ring
  · have hbval : q.1.val ≠ s.1.val := fun h => hb (Fin.ext h)
    rcases lt_or_gt_of_ne hbval with hlt | hgt
    · have hstep : (q.1.val : ℝ) + 1 ≤ (s.1.val : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hlt)
      have hq := (abs_le.mp (packing38_coord_abs_le_four q.2).1)
      have hs := (abs_le.mp (packing38_coord_abs_le_four s.2).1)
      have hdx : 12 ≤
          (20 * (s.1.val : ℝ) + (packing38 s.2).1) -
          (20 * (q.1.val : ℝ) + (packing38 q.2).1) := by
        nlinarith
      simp only [packing38Blocks, sqDist]
      nlinarith [sq_nonneg ((packing38 q.2).2 - (packing38 s.2).2)]
    · have hstep : (s.1.val : ℝ) + 1 ≤ (q.1.val : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hgt)
      have hq := (abs_le.mp (packing38_coord_abs_le_four q.2).1)
      have hs := (abs_le.mp (packing38_coord_abs_le_four s.2).1)
      have hdx : 12 ≤
          (20 * (q.1.val : ℝ) + (packing38 q.2).1) -
          (20 * (s.1.val : ℝ) + (packing38 s.2).1) := by
        nlinarith
      simp only [packing38Blocks, sqDist]
      nlinarith [sq_nonneg ((packing38 q.2).2 - (packing38 s.2).2)]

/-- Local radius-three neighbours of the distinguished center in copy `b`. -/
noncomputable def packing38BlockCenterNeighbors (m : ℕ) (b : Fin m) :
    Finset (Fin m × Fin 38) :=
  Finset.univ.filter fun q =>
    q ≠ (b, 18) ∧
      Real.sqrt (sqDist (packing38Blocks m q)
        (packing38Blocks m (b, 18))) < 3

/-- Every replicated copy retains its 37 certified short neighbours. -/
theorem packing38BlockCenterNeighbors_card_ge (m : ℕ) (b : Fin m) :
    37 ≤ (packing38BlockCenterNeighbors m b).card := by
  let lift : Fin 38 ↪ (Fin m × Fin 38) :=
    ⟨fun i => (b, i), fun _ _ h => congrArg Prod.snd h⟩
  have hsub : packing38CenterNeighbors.map lift ⊆
      packing38BlockCenterNeighbors m b := by
    intro q hq
    rw [Finset.mem_map] at hq
    rcases hq with ⟨i, hi, rfl⟩
    have hp := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨by simp, ?_⟩
    constructor
    · change (b, i) ≠ (b, 18)
      exact fun h => hp.1 (congrArg Prod.snd h)
    · change Real.sqrt (sqDist (packing38Blocks m (b, i))
        (packing38Blocks m (b, 18))) < 3
      simpa [packing38Blocks, sqDist] using hp.2
  calc
    37 = packing38CenterNeighbors.card := packing38CenterNeighbors_card.symm
    _ = (packing38CenterNeighbors.map lift).card := (Finset.card_map _).symm
    _ ≤ (packing38BlockCenterNeighbors m b).card := Finset.card_le_card hsub

/-- Counterexamples exist above every requested cardinality, so an eventual
local bound cannot rescue the shell-three conjecture. -/
theorem arbitrarily_large_shell_three_local_counterexamples (N : ℕ) :
    N ≤ Fintype.card (Fin (N + 1) × Fin 38) ∧
      37 ≤ (packing38BlockCenterNeighbors (N + 1) 0).card := by
  constructor
  · simp
    omega
  · exact packing38BlockCenterNeighbors_card_ge (N + 1) 0

end Research
