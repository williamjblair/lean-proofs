import Research.UpperTruncation

namespace Erdos796

open Filter Topology

/-- Extracted cores strictly beyond a finite cutoff. -/
def tailExtractedFiber (A : Finset ℕ) (n R q : ℕ) : Finset ℕ :=
  (extractedFiber A n.sqrt q).filter fun d => R < d

/-- Aggregate extracted-fiber tail beyond `R`. -/
def extractedTailSum (A : Finset ℕ) (n R : ℕ) : ℕ :=
  ∑ q ∈ sqrtPrimeLabels n, (tailExtractedFiber A n R q).card

lemma extractedFiber_card_eq_truncated_add_tail
    (A : Finset ℕ) (n R q : ℕ) :
    (extractedFiber A n.sqrt q).card =
      (truncatedExtractedFiber A n R q).card +
      (tailExtractedFiber A n R q).card := by
  unfold truncatedExtractedFiber tailExtractedFiber
  have h := Finset.card_filter_add_card_filter_not
    (s := extractedFiber A n.sqrt q) (fun d => d ≤ R)
  simpa [not_le] using h.symm

/-- Exact three-way cardinal decomposition at a finite core cutoff. -/
theorem card_eq_smooth_add_truncated_add_tail
    {A : Finset ℕ} {n R : ℕ} (hA : A ⊆ Finset.Icc 1 n) :
    A.card = (smoothPart A n).card +
      (∑ q ∈ sqrtPrimeLabels n,
        (truncatedExtractedFiber A n R q).card) +
      extractedTailSum A n R := by
  have hbase := card_eq_smoothPart_add_fibers hA
  have hsum :
      (∑ q ∈ sqrtPrimeLabels n, (extractedFiber A n.sqrt q).card) =
        (∑ q ∈ sqrtPrimeLabels n,
          (truncatedExtractedFiber A n R q).card) +
        extractedTailSum A n R := by
    unfold extractedTailSum
    calc
      (∑ q ∈ sqrtPrimeLabels n, (extractedFiber A n.sqrt q).card) =
          ∑ q ∈ sqrtPrimeLabels n,
            ((truncatedExtractedFiber A n R q).card +
              (tailExtractedFiber A n R q).card) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact extractedFiber_card_eq_truncated_add_tail A n R q
      _ = _ := Finset.sum_add_distrib
  omega

/-- The remaining smooth-remainder estimate, stated uniformly over all
admissible sets. -/
def SmoothRemainderGate : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → HasRepBound 3 A →
      ((smoothPart A n).card : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ)) < ε

/-- The remaining uniform extracted-tail estimate.  It says the tail beyond a
large fixed core cutoff costs no more than the literal semiprime tail. -/
def ExtractedTailGate : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, 0 < R ∧ ∀ᶠ n : ℕ in atTop,
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → HasRepBound 3 A →
      (extractedTailSum A n R : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
        (profileTailCount R n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) + ε

/-- The two explicit remainder gates imply the desired uniform extremal upper
bound. -/
theorem remainderGates_eventually_normalizedError_lt
    (hsmooth : SmoothRemainderGate) (htail : ExtractedTailGate)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      normalizedError n < Mertens.M + variationalLimit + ε := by
  classical
  let δ := ε / 5
  have hδ : 0 < δ := by dsimp [δ]; positivity
  rcases htail δ hδ with ⟨R, hR, htailR⟩
  have hsmoothR := hsmooth δ hδ
  have hprofile : ∀ᶠ n : ℕ in atTop,
      profileApproxError R hR n < δ :=
    (tendsto_profileApproxError_zero R hR).eventually
      (gt_mem_nhds hδ)
  have hsingleton : Tendsto (fun n : ℕ =>
      ((R * 2 ^ R : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (nhds 0) := by
    have hlogdiv : Tendsto (fun n : ℕ =>
        Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1
        one_ne_zero).comp tendsto_natCast_atTop_atTop
      have heq : ((fun x : ℝ => Real.log x / x) ∘
          (fun n : ℕ => (n : ℝ))) =
          (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) := rfl
      rw [← heq]
      simpa only [pow_one, one_mul, zero_add, add_zero] using h
    have h' : Tendsto (fun n : ℕ =>
        ((R * 2 ^ R : ℕ) : ℝ) *
          (Real.log (n : ℝ) / (n : ℝ))) atTop (nhds 0) := by
      simpa using hlogdiv.const_mul ((R * 2 ^ R : ℕ) : ℝ)
    apply h'.congr'
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlog0 : Real.log (n : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    field_simp
  have hsingleton' : ∀ᶠ n : ℕ in atTop,
      ((R * 2 ^ R : ℕ) : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ)) < δ :=
    hsingleton.eventually (gt_mem_nhds hδ)
  have htailAsym : ∀ᶠ n : ℕ in atTop,
      (profileTailCount R n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ)) <
          Mertens.M - primeMass R + δ :=
    (tendsto_profileTailCount_residual R).eventually
      (gt_mem_nhds (by linarith :
        Mertens.M - primeMass R < Mertens.M - primeMass R + δ))
  filter_upwards [eventually_gt_atTop 1, hsmoothR, htailR, hprofile,
    hsingleton', htailAsym] with n hn hs ht hp he htasy
  have hnR : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := div_pos hnR hlog
  let C := ((Finset.Icc 1 n).powerset.filter fun A => HasRepBound 3 A)
  have hC : C.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by simp), ?_⟩⟩
    intro m
    simp [repCount]
  rcases Finset.exists_max_image C Finset.card hC with ⟨A, hAmem, hmax⟩
  have hAprops := Finset.mem_filter.mp hAmem
  have hAint := Finset.mem_powerset.mp hAprops.1
  have hArep := hAprops.2
  have hgcard : C.sup Finset.card = A.card := by
    apply le_antisymm
    · exact Finset.sup_le fun B hB => hmax B hB
    · exact Finset.le_sup hAmem
  unfold normalizedError g
  change (((C.sup Finset.card : ℕ) : ℝ) -
      (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) /
      ((n : ℝ) / Real.log (n : ℝ)) < _
  rw [hgcard]
  have hdecomp := card_eq_smooth_add_truncated_add_tail
    (R := R) hAint
  have htrunc := truncatedFiberSum_div_le_variational hR hn hAint hArep
  have hsA := hs A hAint hArep
  have htA := ht A hAint hArep
  push_cast at hdecomp
  rw [hdecomp]
  have hsplit :
      ((smoothPart A n).card : ℝ) /
            ((n : ℝ) / Real.log (n : ℝ)) +
          ((∑ q ∈ sqrtPrimeLabels n,
            (truncatedExtractedFiber A n R q).card : ℕ) : ℝ) /
            ((n : ℝ) / Real.log (n : ℝ)) +
          (extractedTailSum A n R : ℝ) /
            ((n : ℝ) / Real.log (n : ℝ)) -
          Real.log (Real.log (n : ℝ)) <
        Mertens.M + variationalLimit + ε := by
    dsimp [δ] at hsA htA hp he htasy ⊢
    linarith
  convert hsplit using 1
  field_simp [ne_of_gt hnR, ne_of_gt hlog]
  push_cast
  ring

/-- Solving exactly the two named remainder gates completes Problem 796 with
limit value `Mertens.M + variationalLimit`. -/
theorem remainderGates_imply_statement
    (hsmooth : SmoothRemainderGate) (htail : ExtractedTailGate) : Statement := by
  refine ⟨Mertens.M + variationalLimit, ?_⟩
  apply tendsto_order.2
  constructor
  · intro a ha
    have hε : 0 < Mertens.M + variationalLimit - a := sub_pos.mpr ha
    have h := eventually_variationalLimitCoefficient_sub_lt_normalizedError hε
    simpa only [sub_sub_cancel] using h
  · intro b hb
    have hε : 0 < b - (Mertens.M + variationalLimit) := sub_pos.mpr hb
    have h := remainderGates_eventually_normalizedError_lt hsmooth htail hε
    convert h using 1 <;> ring

end Erdos796
