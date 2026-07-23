import Research.RayHyperbola

namespace Erdos796

open Filter Topology

/-- The finite reciprocal-prime baseline is the Mertens residual plus
`log log`. -/
theorem primeMass_eq_residual (n : ℕ) :
    primeMass n = primeReciprocalResidual (n : ℝ) +
      Real.log (Real.log (n : ℝ)) := by
  unfold primeMass primeReciprocalResidual
  have hs : Nat.primesLE n = (Finset.Ioc 0 n).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpn, hp⟩
      exact ⟨⟨hp.pos, hpn⟩, hp⟩
    · rintro ⟨⟨hp0, hpn⟩, hp⟩
      exact ⟨hpn, hp⟩
  rw [hs, Nat.floor_natCast]
  ring

/-- A fixed multiplicative window carries asymptotically zero reciprocal-prime
mass. -/
theorem tendsto_primeMass_mul_sub (W : ℕ) (hW : 0 < W) :
    Tendsto (fun P : ℕ => primeMass (W * P) - primeMass P)
      atTop (nhds 0) := by
  have hmulNat : Tendsto (fun P : ℕ => W * P) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with P hP
    exact hP.trans (Nat.le_mul_of_pos_left P hW)
  have hres0 : Tendsto (fun P : ℕ => primeReciprocalResidual (P : ℝ))
      atTop (nhds Mertens.M) :=
    tendsto_primeReciprocalResidual.comp tendsto_natCast_atTop_atTop
  have hresW : Tendsto (fun P : ℕ =>
      primeReciprocalResidual ((W * P : ℕ) : ℝ))
      atTop (nhds Mertens.M) :=
    tendsto_primeReciprocalResidual.comp
      (tendsto_natCast_atTop_atTop.comp hmulNat)
  have hres : Tendsto (fun P : ℕ =>
      primeReciprocalResidual ((W * P : ℕ) : ℝ) -
        primeReciprocalResidual (P : ℝ)) atTop (nhds 0) := by
    simpa using hresW.sub hres0
  have hlog : Tendsto (fun P : ℕ => Real.log (P : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun P : ℕ =>
      Real.log (W : ℝ) / Real.log (P : ℝ)) atTop (nhds 0) :=
    hlog.const_div_atTop _
  have hinside : Tendsto (fun P : ℕ =>
      1 + Real.log (W : ℝ) / Real.log (P : ℝ)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hsmall)
  have hlogdiff : Tendsto (fun P : ℕ =>
      Real.log (Real.log ((W * P : ℕ) : ℝ)) -
        Real.log (Real.log (P : ℝ))) atTop (nhds 0) := by
    have hh := (Real.continuousAt_log one_ne_zero).tendsto.comp hinside
    have hh' : Tendsto (fun P : ℕ =>
        Real.log (1 + Real.log (W : ℝ) / Real.log (P : ℝ)))
        atTop (nhds 0) := by
      convert hh using 1
      · funext P
        rfl
      · simp
    apply hh'.congr'
    filter_upwards [eventually_gt_atTop 1] with P hP
    have hP0 : (P : ℝ) ≠ 0 := by positivity
    have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hW)
    have hlP : Real.log (P : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hP))
    have hWP : 1 < W * P := by nlinarith
    have hlWP : Real.log ((W * P : ℕ) : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hWP))
    rw [← Real.log_div hlWP hlP]
    congr 1
    push_cast
    rw [Real.log_mul hW0 hP0]
    field_simp
    ring
  have hs := hres.add hlogdiff
  convert hs using 1
  · funext P
    rw [primeMass_eq_residual, primeMass_eq_residual]
    ring
  · simp

/-- Tail counts at two fixed cutoffs differ by the reciprocal-prime mass of
that cutoff window after normalization. -/
theorem tendsto_profileTailCount_cutoff_sub (P R : ℕ) :
    Tendsto (fun n : ℕ =>
      ((profileTailCount P n : ℝ) - profileTailCount R n) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop
      (nhds (primeMass R - primeMass P)) := by
  have hP := tendsto_profileTailCount_residual P
  have hR := tendsto_profileTailCount_residual R
  have h := hP.sub hR
  have h' : Tendsto (fun n : ℕ =>
      ((profileTailCount P n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ))) -
      ((profileTailCount R n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) -
        Real.log (Real.log (n : ℝ)))) atTop
      (nhds ((Mertens.M - primeMass P) -
        (Mertens.M - primeMass R))) := h
  convert h' using 1
  · funext n
    ring
  · ring

end Erdos796
