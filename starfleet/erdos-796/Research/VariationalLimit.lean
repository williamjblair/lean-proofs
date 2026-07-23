import Research.VariationalBound

namespace Erdos796

/-- The all-empty compatible profile, used only to witness nonemptiness of the
finite variational class. -/
def emptyFiberProfile (R : ℕ) (hR : 0 < R) : FiberProfile R where
  posR := hR
  fiber := fun _ => ∅
  positive := by simp
  bounded := by simp
  compatible := by
    intro i j
    simp [CrossCompatible, crossMultiplicity]

/-- Optimal renormalized gain at a finite cutoff. -/
noncomputable def optimalGamma (R : ℕ) : ℝ :=
  sSup (Set.range (fun P : FiberProfile R => P.gamma))

lemma gammaRange_bddAbove (R : ℕ) :
    BddAbove (Set.range (fun P : FiberProfile R => P.gamma)) := by
  refine ⟨universalVariationalBound, ?_⟩
  rintro x ⟨P, rfl⟩
  exact P.gamma_le_universal

lemma gammaRange_nonempty (R : ℕ) (hR : 0 < R) :
    (Set.range (fun P : FiberProfile R => P.gamma)).Nonempty :=
  ⟨(emptyFiberProfile R hR).gamma, ⟨emptyFiberProfile R hR, rfl⟩⟩

/-- Every profile lies below the finite optimum. -/
theorem FiberProfile.gamma_le_optimal {R : ℕ} (P : FiberProfile R) :
    P.gamma ≤ optimalGamma R := by
  exact le_csSup (gammaRange_bddAbove R) ⟨P, rfl⟩

/-- Every positive-cutoff finite optimum obeys the universal bound. -/
theorem optimalGamma_le_universal (R : ℕ) (hR : 0 < R) :
    optimalGamma R ≤ universalVariationalBound := by
  apply csSup_le (gammaRange_nonempty R hR)
  intro x hx
  rcases hx with ⟨P, rfl⟩
  exact P.gamma_le_universal

/-- Prime extension makes finite optimal gains nondecreasing. -/
theorem optimalGamma_le_succ (R : ℕ) (hR : 0 < R) :
    optimalGamma R ≤ optimalGamma (R + 1) := by
  apply csSup_le (gammaRange_nonempty R hR)
  intro x hx
  rcases hx with ⟨P, rfl⟩
  change P.gamma ≤ optimalGamma (R + 1)
  rw [← P.gamma_extendOne]
  exact P.extendOne.gamma_le_optimal

/-- Shifted finite optima form a monotone sequence. -/
theorem monotone_optimalGamma_succ :
    Monotone (fun R : ℕ => optimalGamma (R + 1)) := by
  apply monotone_nat_of_le_succ
  intro R
  simpa [Nat.add_assoc] using optimalGamma_le_succ (R + 1) (by omega)

/-- The finite real variational limit. -/
noncomputable def variationalLimit : ℝ :=
  ⨆ R : ℕ, optimalGamma (R + 1)

lemma optimalGammaSucc_range_bddAbove :
    BddAbove (Set.range (fun R : ℕ => optimalGamma (R + 1))) := by
  refine ⟨universalVariationalBound, ?_⟩
  rintro x ⟨R, rfl⟩
  exact optimalGamma_le_universal (R + 1) (by omega)

/-- The finite optimal gains converge monotonically to the finite variational
limit. -/
theorem tendsto_optimalGamma_variationalLimit :
    Filter.Tendsto (fun R : ℕ => optimalGamma (R + 1)) Filter.atTop
      (nhds variationalLimit) := by
  exact tendsto_atTop_ciSup monotone_optimalGamma_succ
    optimalGammaSucc_range_bddAbove

/-- Every finite compatible profile has gain at most the variational limit. -/
theorem FiberProfile.gamma_le_variationalLimit {R : ℕ} (P : FiberProfile R) :
    P.gamma ≤ variationalLimit := by
  have hR : 0 < R := P.posR
  have hopt := P.gamma_le_optimal
  have hidx : R - 1 + 1 = R := Nat.sub_add_cancel (by omega)
  have hsup : optimalGamma (R - 1 + 1) ≤ variationalLimit := by
    unfold variationalLimit
    exact le_ciSup optimalGammaSucc_range_bddAbove (R - 1)
  rw [hidx] at hsup
  exact hopt.trans hsup

end Erdos796
