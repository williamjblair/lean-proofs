import ResearchPNT.PrimeBins
import Research.AnalyticRecurrence
import Research.Benchmark

/-! # Combining the exact recurrence with prime quotient bins -/

namespace ResearchPNT

/-- Primes for which `floor(N/p)=m`. -/
def quotientPrimeBin (N m : ℕ) : Finset ℕ :=
  (Finset.Ioc (N / (m + 1)) (N / m)).filter Nat.Prime

/-- Exact characterization of a natural floor-quotient fiber. -/
theorem mem_quotientPrimeBin_iff {N m p : ℕ} (hm : 0 < m) :
    p ∈ quotientPrimeBin N m ↔ p.Prime ∧ N / p = m := by
  rw [quotientPrimeBin, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    have hmle : m ≤ N / p := by
      rw [Nat.le_div_iff_mul_le hp.pos]
      have := (Nat.le_div_iff_mul_le hm).mp hhi
      simpa [Nat.mul_comm] using this
    have hlt : N / p < m + 1 := by
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      simpa [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).mp hlo
    exact ⟨hp, by omega⟩
  · rintro ⟨hp, hquot⟩
    refine ⟨⟨?_, ?_⟩, hp⟩
    · rw [Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)]
      have hlt : N / p < m + 1 := by omega
      simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hp.pos).mp hlt
    · rw [Nat.le_div_iff_mul_le hm]
      have : m * p ≤ N := by
        rw [← Nat.le_div_iff_mul_le hp.pos]
        omega
      simpa [Nat.mul_comm] using this

/-- If `Q=floor(N/y)`, every large prime maps to an index in `1,...,y-1`. -/
theorem largePrime_quotient_mem_Ico {N y p : ℕ} (hy : 0 < y)
    (hp : p ∈ Research.largePrimes N (N / y)) :
    N / p ∈ Finset.Ico 1 y := by
  rw [Research.largePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
  have hpPrime := hp.2
  have hpN := hp.1.2
  have hQp : N / y < p := Nat.lt_of_succ_le hp.1.1
  rw [Finset.mem_Ico]
  constructor
  · exact (Nat.le_div_iff_mul_le hpPrime.pos).mpr (by simpa using hpN)
  · rw [Nat.div_lt_iff_lt_mul hpPrime.pos]
    exact lt_of_lt_of_le (Nat.lt_mul_div_succ N hy)
      (Nat.mul_le_mul_left y (Nat.succ_le_iff.mpr hQp))

/-- In this range, a large-prime quotient fiber equals its prime interval. -/
theorem largePrime_fiber_eq_bin {N y m : ℕ}
    (hm : m ∈ Finset.Ico 1 y) :
    (Research.largePrimes N (N / y)).filter (fun p => N / p = m) =
      quotientPrimeBin N m := by
  have hmPos : 0 < m := (Finset.mem_Ico.mp hm).1
  have hmy : m < y := (Finset.mem_Ico.mp hm).2
  ext p
  constructor
  · intro hp
    rw [Finset.mem_filter] at hp
    exact (mem_quotientPrimeBin_iff hmPos).mpr ⟨
      (by
        rw [Research.largePrimes, Finset.mem_filter] at hp
        exact hp.1.2), hp.2⟩
  · intro hp
    rw [mem_quotientPrimeBin_iff hmPos] at hp
    rw [Finset.mem_filter]
    refine ⟨?_, hp.2⟩
    rw [Research.largePrimes, Finset.mem_filter, Finset.mem_Icc]
    have hbounds :
        N / (m + 1) < p ∧ p ≤ N / m := by
      simpa [quotientPrimeBin] using
        ((Finset.mem_filter.mp
          (show p ∈ quotientPrimeBin N m from
            (mem_quotientPrimeBin_iff hmPos).mpr hp)).1)
    refine ⟨⟨?_, ?_⟩, hp.1⟩
    · have hdiv : N / y ≤ N / (m + 1) :=
        Nat.div_le_div_left (by omega : m + 1 ≤ y) (by omega : 0 < m + 1)
      omega
    · exact le_trans hbounds.2 (Nat.div_le_self N m)

/-- Exact grouping of the large-prime sum by `m=floor(N/p)`. -/
theorem sum_largePrimes_eq_sum_bins (f : ℕ → ℝ) {N y : ℕ} (hy : 0 < y) :
    ∑ p ∈ Research.largePrimes N (N / y), f (N / p) =
      ∑ m ∈ Finset.Ico 1 y, (quotientPrimeBin N m).card * f m := by
  have hgroup := Finset.sum_fiberwise_of_maps_to'
    (s := Research.largePrimes N (N / y)) (t := Finset.Ico 1 y)
    (g := fun p => N / p)
    (fun p hp => largePrime_quotient_mem_Ico hy hp) f
  rw [← hgroup]
  apply Finset.sum_congr rfl
  intro m hm
  rw [largePrime_fiber_eq_bin hm]
  simp

/-- The logarithm of the counting function is nonnegative. -/
theorem logS_nonneg (N : ℕ) : 0 ≤ Research.logS N := by
  rw [Research.logS]
  exact Real.log_nonneg (by
    exact_mod_cast (Research.S_pos N))

/-- The exact real majorant for a quotient bin supplied by F-009. -/
noncomputable def quotientBinMajorant (C : ℝ) (N m : ℕ) : ℝ :=
  (((N / m : ℕ) : ℝ) - (N / (m + 1) : ℕ) +
      C * ((N / (m + 1) : ℕ) / Real.log (N / (m + 1) : ℕ) ^ 2) +
      C * ((N / m : ℕ) / Real.log (N / m : ℕ) ^ 2)) /
        Real.log (N / (m + 1) : ℕ)

/-- A simpler majorant using only the lower endpoint logarithm. -/
noncomputable def simpleBinMajorant (C : ℝ) (N m : ℕ) : ℝ :=
  (((N / m : ℕ) : ℝ) - (N / (m + 1) : ℕ) +
      2 * C * (N / m : ℕ) / Real.log (N / (m + 1) : ℕ) ^ 2) /
        Real.log (N / (m + 1) : ℕ)

/-- The gap between consecutive natural quotient endpoints is at most the
corresponding real interval length, up to one unit of flooring loss. -/
theorem floor_div_gap_lt (N m : ℕ) (hm : 0 < m) :
    ((N / m : ℕ) : ℝ) - (N / (m + 1) : ℕ) <
      (N : ℝ) / ((m : ℝ) * (m + 1)) + 1 := by
  have hv : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
  have hu : (N : ℝ) / (m + 1) < ((N / (m + 1) : ℕ) : ℝ) + 1 := by
    rw [← Nat.floor_div_eq_div (K := ℝ)]
    simpa using Nat.lt_succ_floor ((N : ℝ) / (m + 1))
  have hmid : ((N / m : ℕ) : ℝ) - (N / (m + 1) : ℕ) <
      (N : ℝ) / m - (N : ℝ) / (m + 1) + 1 := by linarith
  calc
    ((N / m : ℕ) : ℝ) - (N / (m + 1) : ℕ) <
        (N : ℝ) / m - (N : ℝ) / (m + 1) + 1 := hmid
    _ = (N : ℝ) / ((m : ℝ) * (m + 1)) + 1 := by
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
      have hs0 : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- A floor quotient has a logarithm no smaller than the logarithm of half
the corresponding real quotient. -/
theorem log_floor_div_lower (N m : ℕ) (hm : 0 < m)
    (hu2 : 2 ≤ N / (m + 1)) :
    Real.log (N : ℝ) - Real.log (m + 1 : ℕ) - Real.log 2 ≤
      Real.log (N / (m + 1) : ℕ) := by
  let u : ℕ := N / (m + 1)
  let x : ℝ := (N : ℝ) / (m + 1)
  have huReal : (u : ℝ) ≤ x := by
    dsimp [u, x]
    simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := m + 1))
  have hx2 : (2 : ℝ) ≤ x := le_trans (by exact_mod_cast hu2) huReal
  have hxlt : x < (u : ℝ) + 1 := by
    dsimp [u, x]
    rw [← Nat.floor_div_eq_div (K := ℝ)]
    simpa using Nat.lt_succ_floor ((N : ℝ) / (m + 1))
  have hhalf : x / 2 ≤ (u : ℝ) := by linarith
  have huPos : 0 < u := by omega
  have hNposNat : 0 < N := Nat.pos_of_div_pos huPos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposNat
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hlog := Real.log_le_log (div_pos hxpos (by norm_num)) hhalf
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hd0 : (m : ℝ) + 1 ≠ 0 := by positivity
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hid : Real.log (x / 2) =
      Real.log (N : ℝ) - Real.log (m + 1 : ℕ) - Real.log 2 := by
    dsimp [x]
    rw [Real.log_div (div_ne_zero hN0 hd0) htwo,
      Real.log_div hN0 hd0]
    norm_num
  rw [hid] at hlog
  exact hlog

/-- The floor-free coarse quotient-bin majorant. -/
noncomputable def coarseBinMajorant (C : ℝ) (N m : ℕ) : ℝ :=
  ((N : ℝ) / ((m : ℝ) * (m + 1)) + 1 +
      2 * C * ((N : ℝ) / m) / Real.log (N / (m + 1) : ℕ) ^ 2) /
        Real.log (N / (m + 1) : ℕ)

/-- A floor-free lower bound for the logarithm in a quotient bin. -/
noncomputable def binLogLower (N m : ℕ) : ℝ :=
  Real.log (N : ℝ) - Real.log (m + 1 : ℕ) - Real.log 2

/-- The quotient-bin majorant after replacing its last remaining floor
logarithm by `binLogLower`. -/
noncomputable def logLowerBinMajorant (C : ℝ) (N m : ℕ) : ℝ :=
  ((N : ℝ) / ((m : ℝ) * (m + 1)) + 1 +
      (2 * C * ((N : ℝ) / m)) / binLogLower N m ^ 2) /
        binLogLower N m

/-- A common-logarithm kernel, with a user-supplied relative loss `δ`. -/
noncomputable def uniformBinMajorant (C δ : ℝ) (N m : ℕ) : ℝ :=
  (1 + δ) * ((N : ℝ) / ((m : ℝ) * (m + 1)) + 1) /
      Real.log (N : ℝ) +
    16 * C * ((N : ℝ) / m) / Real.log (N : ℝ) ^ 3

/-- Abstract denominator comparison. If `log N` is at most `(1+δ)` times the
bin logarithmic lower bound, and at most twice that lower bound, then the
fully floor-free kernel has the desired common-denominator form. -/
theorem logLowerBinMajorant_le_uniform (C δ : ℝ) (N m : ℕ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hm : 0 < m)
    (hlog : 0 < Real.log (N : ℝ))
    (hL : 0 < binLogLower N m)
    (hscale : Real.log (N : ℝ) ≤ (1 + δ) * binLogLower N m)
    (hhalf : Real.log (N : ℝ) ≤ 2 * binLogLower N m) :
    logLowerBinMajorant C N m ≤ uniformBinMajorant C δ N m := by
  let ell : ℝ := Real.log (N : ℝ)
  let L : ℝ := binLogLower N m
  let A : ℝ := (N : ℝ) / ((m : ℝ) * (m + 1)) + 1
  let E : ℝ := 2 * C * ((N : ℝ) / m)
  have hAnonneg : 0 ≤ A := by dsimp [A]; positivity
  have hEnonneg : 0 ≤ E := by dsimp [E]; positivity
  have hδone : 0 ≤ 1 + δ := by linarith
  have hmain : A / L ≤ (1 + δ) * A / ell := by
    rw [div_le_div_iff₀ hL hlog]
    convert mul_le_mul_of_nonneg_left hscale hAnonneg using 1 <;> ring
  have hpow : ell ^ 3 ≤ 8 * L ^ 3 := by
    have hp := pow_le_pow_left₀ hlog.le hhalf 3
    nlinarith
  have herr : E / L ^ 3 ≤ 8 * E / ell ^ 3 := by
    rw [div_le_div_iff₀ (pow_pos hL 3) (pow_pos hlog 3)]
    nlinarith
  have hL0 : L ≠ 0 := ne_of_gt hL
  calc
    logLowerBinMajorant C N m = (A + E / L ^ 2) / L := by
      rfl
    _ = A / L + E / L ^ 3 := by
      field_simp [hL0]
    _ ≤ (1 + δ) * A / ell + 8 * E / ell ^ 3 := add_le_add hmain herr
    _ = uniformBinMajorant C δ N m := by
      dsimp [uniformBinMajorant, A, E, ell]
      ring

/-- An `m`-separable envelope for the common-logarithm kernel. -/
noncomputable def renewalKernelEnvelope (C δ : ℝ) (N m : ℕ) : ℝ :=
  (1 + δ) * ((N : ℝ) / ((m : ℝ) * (m + 1)) + 1) /
      Real.log (N : ℝ) +
    16 * C * (N : ℝ) / Real.log (N : ℝ) ^ 3

/-- Principal coefficient in the separable renewal envelope. -/
noncomputable def renewalPrincipal (δ : ℝ) (N : ℕ) : ℝ :=
  (1 + δ) * (N : ℝ) / Real.log (N : ℝ)

/-- Nonprincipal coefficient in the separable renewal envelope. -/
noncomputable def renewalError (C δ : ℝ) (N : ℕ) : ℝ :=
  (1 + δ) / Real.log (N : ℝ) +
    16 * C * (N : ℝ) / Real.log (N : ℝ) ^ 3

/-- The envelope separates exactly into a renewal weight and a constant. -/
theorem renewalKernelEnvelope_eq (C δ : ℝ) (N m : ℕ)
    (hm : 0 < m) (hlog : Real.log (N : ℝ) ≠ 0) :
    renewalKernelEnvelope C δ N m =
      renewalPrincipal δ N / ((m : ℝ) * (m + 1)) +
        renewalError C δ N := by
  rw [renewalKernelEnvelope, renewalPrincipal, renewalError]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hs0 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm0, hs0, hlog]
  ring

/-- Dropping the factor `1/m` in the PNT-error term bounds the common kernel
by a sum of a renewal weight and an `m`-independent error. -/
theorem uniformBinMajorant_le_envelope (C δ : ℝ) (N m : ℕ)
    (hC : 0 ≤ C) (hm : 1 ≤ m) (hlog : 0 < Real.log (N : ℝ)) :
    uniformBinMajorant C δ N m ≤ renewalKernelEnvelope C δ N m := by
  have hNm : (N : ℝ) / m ≤ (N : ℝ) :=
    div_le_self (by positivity) (by exact_mod_cast hm)
  rw [uniformBinMajorant, renewalKernelEnvelope]
  apply add_le_add_right
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hNm (by positivity)) (by positivity)

/-- The two endpoint PNT errors are at most twice the upper endpoint divided
by the square of the lower endpoint logarithm. -/
theorem quotientBinMajorant_le_simple (C : ℝ) (N m : ℕ)
    (hC : 0 ≤ C) (hm : 0 < m) (hu2 : 2 ≤ N / (m + 1)) :
    quotientBinMajorant C N m ≤ simpleBinMajorant C N m := by
  let u : ℕ := N / (m + 1)
  let v : ℕ := N / m
  have huvNat : u ≤ v := Nat.div_le_div_left (Nat.le_succ m) hm
  have huPos : (0 : ℝ) < u := by positivity
  have hlogPos : 0 < Real.log (u : ℝ) :=
    Real.log_pos (by exact_mod_cast hu2)
  have hlogNonneg : 0 ≤ Real.log (u : ℝ) := hlogPos.le
  have hlogLe : Real.log (u : ℝ) ≤ Real.log (v : ℝ) :=
    Real.log_le_log huPos (by exact_mod_cast huvNat)
  have hlogVNonneg : 0 ≤ Real.log (v : ℝ) := le_trans hlogNonneg hlogLe
  have hsqLe : Real.log (u : ℝ) ^ 2 ≤ Real.log (v : ℝ) ^ 2 :=
    (sq_le_sq₀ hlogNonneg hlogVNonneg).mpr hlogLe
  have hfirst :
      (u : ℝ) / Real.log u ^ 2 ≤ (v : ℝ) / Real.log u ^ 2 :=
    div_le_div_of_nonneg_right (by exact_mod_cast huvNat) (sq_nonneg _)
  have hsecond :
      (v : ℝ) / Real.log v ^ 2 ≤ (v : ℝ) / Real.log u ^ 2 :=
    div_le_div_of_nonneg_left (by positivity)
      (sq_pos_of_pos hlogPos) hsqLe
  rw [quotientBinMajorant, simpleBinMajorant]
  change (_ + C * ((u : ℝ) / Real.log u ^ 2) +
      C * ((v : ℝ) / Real.log v ^ 2)) / Real.log u ≤
    (_ + 2 * C * (v : ℝ) / Real.log u ^ 2) / Real.log u
  rw [div_le_div_iff_of_pos_right hlogPos]
  have hfirstC := mul_le_mul_of_nonneg_left hfirst hC
  have hsecondC := mul_le_mul_of_nonneg_left hsecond hC
  have herr : C * ((u : ℝ) / Real.log u ^ 2) +
      C * ((v : ℝ) / Real.log v ^ 2) ≤
        2 * C * (v : ℝ) / Real.log u ^ 2 := by
    calc
      C * ((u : ℝ) / Real.log u ^ 2) +
          C * ((v : ℝ) / Real.log v ^ 2) ≤
        C * ((v : ℝ) / Real.log u ^ 2) +
          C * ((v : ℝ) / Real.log u ^ 2) := add_le_add hfirstC hsecondC
      _ = 2 * C * (v : ℝ) / Real.log u ^ 2 := by ring
  linarith

/-- Removing the remaining floors in the numerator only increases the
simplified majorant. -/
theorem simpleBinMajorant_lt_coarse (C : ℝ) (N m : ℕ)
    (hC : 0 ≤ C) (hm : 0 < m) (hu2 : 2 ≤ N / (m + 1)) :
    simpleBinMajorant C N m < coarseBinMajorant C N m := by
  let u : ℕ := N / (m + 1)
  let v : ℕ := N / m
  have hlogPos : 0 < Real.log (u : ℝ) :=
    Real.log_pos (by exact_mod_cast hu2)
  have hv : (v : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
  have herr : 2 * C * (v : ℝ) / Real.log u ^ 2 ≤
      2 * C * ((N : ℝ) / m) / Real.log u ^ 2 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hv (by positivity)) (sq_nonneg _)
  rw [simpleBinMajorant, coarseBinMajorant]
  change (_ + 2 * C * (v : ℝ) / Real.log u ^ 2) / Real.log u <
    (_ + 2 * C * ((N : ℝ) / m) / Real.log u ^ 2) / Real.log u
  rw [div_lt_div_iff_of_pos_right hlogPos]
  have hgap := floor_div_gap_lt N m hm
  linarith

/-- Replacing the floor logarithm by its positive floor-free lower bound
increases the coarse majorant. -/
theorem coarseBinMajorant_le_logLower (C : ℝ) (N m : ℕ)
    (hC : 0 ≤ C) (hm : 0 < m) (hu2 : 2 ≤ N / (m + 1))
    (hLpos : 0 < binLogLower N m) :
    coarseBinMajorant C N m ≤ logLowerBinMajorant C N m := by
  let u : ℕ := N / (m + 1)
  let L : ℝ := binLogLower N m
  let A : ℝ := (N : ℝ) / ((m : ℝ) * (m + 1)) + 1
  let E : ℝ := 2 * C * ((N : ℝ) / m)
  have hlogPos : 0 < Real.log (u : ℝ) :=
    Real.log_pos (by exact_mod_cast hu2)
  have hLle : L ≤ Real.log (u : ℝ) := by
    exact log_floor_div_lower N m hm hu2
  have hsqLe : L ^ 2 ≤ Real.log (u : ℝ) ^ 2 :=
    (sq_le_sq₀ hLpos.le hlogPos.le).mpr hLle
  have hEnonneg : 0 ≤ E := by
    dsimp [E]
    positivity
  have hEle : E / Real.log (u : ℝ) ^ 2 ≤ E / L ^ 2 :=
    div_le_div_of_nonneg_left hEnonneg (sq_pos_of_pos hLpos) hsqLe
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  rw [coarseBinMajorant, logLowerBinMajorant]
  change (A + E / Real.log (u : ℝ) ^ 2) / Real.log u ≤
    (A + E / L ^ 2) / L
  exact div_le_div₀ (add_nonneg hAnonneg (div_nonneg hEnonneg (sq_nonneg _)))
    (add_le_add_right hEle A) hLpos hLle

/-- The high-index part of the uniform recurrence is controlled exactly by
the two discrete benchmark estimates F-016 and F-017. -/
theorem sum_uniform_mul_logS_le_discreteBenchmark
    (C δ K : ℝ) (N k M y : ℕ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hlog : 0 < Real.log (N : ℝ)) (hM : 2 ≤ M) (hMy : M ≤ y)
    (hInd : ∀ m ∈ Finset.Ico M y,
      Research.logS m ≤ K * Research.discreteRenewalBenchmark k m) :
    ∑ m ∈ Finset.Ico M y,
        uniformBinMajorant C δ N m * Research.logS m ≤
      K * (renewalPrincipal δ N *
          (Research.renewalProduct k (Research.logLogNat y) *
            (Research.logLogNat y - Research.logLogNat M)) +
        renewalError C δ N *
          ((y : ℝ) ^ 2 / Real.log M *
            Research.renewalProduct k (Research.logLogNat y))) := by
  have hP : 0 ≤ renewalPrincipal δ N := by
    rw [renewalPrincipal]
    positivity
  have hE : 0 ≤ renewalError C δ N := by
    rw [renewalError]
    positivity
  have hterm : ∀ m ∈ Finset.Ico M y,
      uniformBinMajorant C δ N m * Research.logS m ≤
        renewalKernelEnvelope C δ N m *
          (K * Research.discreteRenewalBenchmark k m) := by
    intro m hm
    have hm2 : 2 ≤ m := le_trans hM (Finset.mem_Ico.mp hm).1
    have hm1 : 1 ≤ m := le_trans (by omega) hm2
    have hB := Research.discreteRenewalBenchmark_nonneg k m hm2
    have hU : 0 ≤ uniformBinMajorant C δ N m := by
      rw [uniformBinMajorant]
      positivity
    calc
      uniformBinMajorant C δ N m * Research.logS m ≤
          uniformBinMajorant C δ N m *
            (K * Research.discreteRenewalBenchmark k m) :=
        mul_le_mul_of_nonneg_left (hInd m hm) hU
      _ ≤ renewalKernelEnvelope C δ N m *
            (K * Research.discreteRenewalBenchmark k m) :=
        mul_le_mul_of_nonneg_right
          (uniformBinMajorant_le_envelope C δ N m hC hm1 hlog)
          (mul_nonneg hK hB)
  calc
    ∑ m ∈ Finset.Ico M y,
        uniformBinMajorant C δ N m * Research.logS m ≤
      ∑ m ∈ Finset.Ico M y,
        renewalKernelEnvelope C δ N m *
          (K * Research.discreteRenewalBenchmark k m) :=
      Finset.sum_le_sum hterm
    _ = K * (renewalPrincipal δ N *
          (∑ m ∈ Finset.Ico M y,
            Research.discreteRenewalBenchmark k m /
              ((m : ℝ) * (m + 1))) +
        renewalError C δ N *
          (∑ m ∈ Finset.Ico M y,
            Research.discreteRenewalBenchmark k m)) := by
      calc
        ∑ m ∈ Finset.Ico M y,
            renewalKernelEnvelope C δ N m *
              (K * Research.discreteRenewalBenchmark k m) =
          ∑ m ∈ Finset.Ico M y, K *
            (renewalPrincipal δ N *
                (Research.discreteRenewalBenchmark k m /
                  ((m : ℝ) * (m + 1))) +
              renewalError C δ N *
                Research.discreteRenewalBenchmark k m) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [renewalKernelEnvelope_eq C δ N m
              (lt_of_lt_of_le (by omega : 0 < M) (Finset.mem_Ico.mp hm).1)
              hlog.ne']
            ring
        _ = K * (∑ m ∈ Finset.Ico M y,
            (renewalPrincipal δ N *
                (Research.discreteRenewalBenchmark k m /
                  ((m : ℝ) * (m + 1))) +
              renewalError C δ N *
                Research.discreteRenewalBenchmark k m)) := by
            rw [Finset.mul_sum]
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ K * (renewalPrincipal δ N *
          (Research.renewalProduct k (Research.logLogNat y) *
            (Research.logLogNat y - Research.logLogNat M)) +
        renewalError C δ N *
          ((y : ℝ) ^ 2 / Real.log M *
            Research.renewalProduct k (Research.logLogNat y))) := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (Research.sum_discreteRenewalBenchmark_div_le k M y hM hMy) hP)
        (mul_le_mul_of_nonneg_left
          (Research.sum_discreteRenewalBenchmark_le k M y hM hMy) hE)

/-- One full high-index renewal step. A single scalar inequality now suffices
to turn the height-`k` inductive bounds into the height-`k+1` benchmark. -/
theorem sum_uniform_mul_logS_le_next_discreteBenchmark
    (C δ K : ℝ) (N k M y : ℕ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hlog : 0 < Real.log (N : ℝ)) (hN2 : 2 ≤ N)
    (hM : 2 ≤ M) (hMy : M ≤ y)
    (hInd : ∀ m ∈ Finset.Ico M y,
      Research.logS m ≤ K * Research.discreteRenewalBenchmark k m)
    (hzT : Research.renewalThreshold < Research.logLogNat N)
    (hwy : Research.logLogNat y ≤
      Real.log (Research.logLogNat N))
    (hscalar :
      renewalPrincipal δ N *
          (Real.log (Research.logLogNat N) - Research.logLogNat M) +
        renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M) ≤
      (N : ℝ) / Real.log (N + 1 : ℕ) *
        Real.log (Research.logLogNat N)) :
    ∑ m ∈ Finset.Ico M y,
        uniformBinMajorant C δ N m * Research.logS m ≤
      K * Research.discreteRenewalBenchmark (k + 1) N := by
  let z : ℝ := Research.logLogNat N
  let L : ℝ := Real.log z
  let Py : ℝ := Research.renewalProduct k (Research.logLogNat y)
  let PL : ℝ := Research.renewalProduct k L
  have hhigh := sum_uniform_mul_logS_le_discreteBenchmark
    C δ K N k M y hC hδ hK hlog hM hMy hInd
  have hPmono : Py ≤ PL :=
    Research.monotone_renewalProduct k hwy
  have hPyNonneg : 0 ≤ Py :=
    le_trans (by norm_num)
      (Research.one_le_renewalProduct k (Research.logLogNat y))
  have hPLNonneg : 0 ≤ PL :=
    le_trans (by norm_num) (Research.one_le_renewalProduct k L)
  have hA : 0 ≤ renewalPrincipal δ N := by
    rw [renewalPrincipal]
    positivity
  have hR : 0 ≤ renewalError C δ N := by
    rw [renewalError]
    positivity
  have hmesh : 0 ≤ Research.logLogNat y - Research.logLogNat M :=
    sub_nonneg.mpr (Research.logLogNat_mono hM hMy)
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast hM)
  have hYterm : 0 ≤ (y : ℝ) ^ 2 / Real.log M := by positivity
  have hbracket : 0 ≤ renewalPrincipal δ N *
        (Research.logLogNat y - Research.logLogNat M) +
      renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M) :=
    add_nonneg (mul_nonneg hA hmesh) (mul_nonneg hR hYterm)
  have hbracketLe : renewalPrincipal δ N *
        (Research.logLogNat y - Research.logLogNat M) +
      renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M) ≤
    renewalPrincipal δ N * (L - Research.logLogNat M) +
      renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M) := by
    apply add_le_add_left
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hwy _) hA
  have hcore : Py * (renewalPrincipal δ N *
        (Research.logLogNat y - Research.logLogNat M) +
      renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M)) ≤
    PL * ((N : ℝ) / Real.log (N + 1 : ℕ) * L) := by
    calc
      Py * (renewalPrincipal δ N *
          (Research.logLogNat y - Research.logLogNat M) +
        renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M)) ≤
        PL * (renewalPrincipal δ N *
          (Research.logLogNat y - Research.logLogNat M) +
        renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M)) :=
          mul_le_mul_of_nonneg_right hPmono hbracket
      _ ≤ PL * (renewalPrincipal δ N *
          (L - Research.logLogNat M) +
        renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M)) :=
          mul_le_mul_of_nonneg_left hbracketLe hPLNonneg
      _ ≤ PL * ((N : ℝ) / Real.log (N + 1 : ℕ) * L) :=
          mul_le_mul_of_nonneg_left hscalar hPLNonneg
  have hcontinuous :
      (N : ℝ) / Real.log (N + 1 : ℕ) *
          Research.renewalProduct (k + 1) z ≤
        Research.discreteRenewalBenchmark (k + 1) N :=
    Research.div_log_succ_mul_renewalProduct_le_discrete (k + 1) N hN2
  calc
    ∑ m ∈ Finset.Ico M y,
        uniformBinMajorant C δ N m * Research.logS m ≤
      K * (renewalPrincipal δ N *
          (Py * (Research.logLogNat y - Research.logLogNat M)) +
        renewalError C δ N *
          ((y : ℝ) ^ 2 / Real.log M * Py)) := hhigh
    _ = K * (Py * (renewalPrincipal δ N *
          (Research.logLogNat y - Research.logLogNat M) +
        renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M))) := by ring
    _ ≤ K * (PL * ((N : ℝ) / Real.log (N + 1 : ℕ) * L)) :=
      mul_le_mul_of_nonneg_left hcore hK
    _ = K * ((N : ℝ) / Real.log (N + 1 : ℕ) *
        Research.renewalProduct (k + 1) z) := by
      rw [Research.renewalProduct_of_lt k hzT]
      dsimp [PL, L, z]
      ring
    _ ≤ K * Research.discreteRenewalBenchmark (k + 1) N :=
      mul_le_mul_of_nonneg_left hcontinuous hK

/-- Quantitative reserve version of the one-step renewal induction. The
extra scalar saving `D` is retained for the smooth and low-index terms. -/
theorem sum_uniform_mul_logS_add_reserve_le_next_discreteBenchmark
    (C δ K D : ℝ) (N k M y : ℕ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hlog : 0 < Real.log (N : ℝ)) (hN2 : 2 ≤ N)
    (hM : 2 ≤ M) (hMy : M ≤ y)
    (hInd : ∀ m ∈ Finset.Ico M y,
      Research.logS m ≤ K * Research.discreteRenewalBenchmark k m)
    (hzT : Research.renewalThreshold < Research.logLogNat N)
    (hwy : Research.logLogNat y ≤ Real.log (Research.logLogNat N))
    (hscalar :
      renewalPrincipal δ N *
          (Real.log (Research.logLogNat N) - Research.logLogNat M) +
        renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M) + D ≤
      (N : ℝ) / Real.log (N + 1 : ℕ) *
        Real.log (Research.logLogNat N)) :
    (∑ m ∈ Finset.Ico M y,
        uniformBinMajorant C δ N m * Research.logS m) +
      K * Research.renewalProduct k (Real.log (Research.logLogNat N)) * D ≤
        K * Research.discreteRenewalBenchmark (k + 1) N := by
  let z : ℝ := Research.logLogNat N
  let L : ℝ := Real.log z
  let Py : ℝ := Research.renewalProduct k (Research.logLogNat y)
  let PL : ℝ := Research.renewalProduct k L
  let A : ℝ := renewalPrincipal δ N
  let R : ℝ := renewalError C δ N
  let T : ℝ := (y : ℝ) ^ 2 / Real.log M
  have hhigh := sum_uniform_mul_logS_le_discreteBenchmark
    C δ K N k M y hC hδ hK hlog hM hMy hInd
  have hPmono : Py ≤ PL := Research.monotone_renewalProduct k hwy
  have hPLNonneg : 0 ≤ PL :=
    le_trans (by norm_num) (Research.one_le_renewalProduct k L)
  have hA : 0 ≤ A := by dsimp [A, renewalPrincipal]; positivity
  have hR : 0 ≤ R := by dsimp [R, renewalError]; positivity
  have hmesh : 0 ≤ Research.logLogNat y - Research.logLogNat M :=
    sub_nonneg.mpr (Research.logLogNat_mono hM hMy)
  have hT : 0 ≤ T := by
    dsimp [T]
    have : 0 < Real.log (M : ℝ) :=
      Real.log_pos (by exact_mod_cast hM)
    positivity
  have hbracket : 0 ≤ A *
        (Research.logLogNat y - Research.logLogNat M) + R * T :=
    add_nonneg (mul_nonneg hA hmesh) (mul_nonneg hR hT)
  have hbracketLe : A *
        (Research.logLogNat y - Research.logLogNat M) + R * T ≤
      A * (L - Research.logLogNat M) + R * T := by
    apply add_le_add_left
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hwy _) hA
  have hcore : Py * (A *
        (Research.logLogNat y - Research.logLogNat M) + R * T) + PL * D ≤
      PL * ((N : ℝ) / Real.log (N + 1 : ℕ) * L) := by
    calc
      Py * (A * (Research.logLogNat y - Research.logLogNat M) + R * T) +
          PL * D ≤
        PL * (A * (Research.logLogNat y - Research.logLogNat M) + R * T) +
          PL * D := by
            apply add_le_add_left
            exact mul_le_mul_of_nonneg_right hPmono hbracket
      _ ≤ PL * (A * (L - Research.logLogNat M) + R * T) + PL * D := by
            apply add_le_add_left
            exact mul_le_mul_of_nonneg_left hbracketLe hPLNonneg
      _ = PL * (A * (L - Research.logLogNat M) + R * T + D) := by ring
      _ ≤ PL * ((N : ℝ) / Real.log (N + 1 : ℕ) * L) := by
            apply mul_le_mul_of_nonneg_left _ hPLNonneg
            exact hscalar
  have hcontinuous :
      (N : ℝ) / Real.log (N + 1 : ℕ) *
          Research.renewalProduct (k + 1) z ≤
        Research.discreteRenewalBenchmark (k + 1) N :=
    Research.div_log_succ_mul_renewalProduct_le_discrete (k + 1) N hN2
  calc
    (∑ m ∈ Finset.Ico M y,
        uniformBinMajorant C δ N m * Research.logS m) +
        K * Research.renewalProduct k
          (Real.log (Research.logLogNat N)) * D ≤
      K * (A * (Py * (Research.logLogNat y - Research.logLogNat M)) +
        R * (T * Py)) + K * PL * D := by
          apply add_le_add
          · exact hhigh
          · rfl
    _ = K * (Py * (A *
          (Research.logLogNat y - Research.logLogNat M) + R * T) +
        PL * D) := by ring
    _ ≤ K * (PL * ((N : ℝ) / Real.log (N + 1 : ℕ) * L)) :=
      mul_le_mul_of_nonneg_left hcore hK
    _ = K * ((N : ℝ) / Real.log (N + 1 : ℕ) *
        Research.renewalProduct (k + 1) z) := by
      rw [Research.renewalProduct_of_lt k hzT]
      dsimp [PL, L, z]
      ring
    _ ≤ K * Research.discreteRenewalBenchmark (k + 1) N :=
      mul_le_mul_of_nonneg_left hcontinuous hK

/-- Explicit nonrecursive part of the uniform recurrence. -/
noncomputable def renewalBaseError (N y : ℕ) : ℝ :=
  Real.log 2 + Real.log N +
    (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
    2 * (Real.log 4 + 4) * N.sqrt

/-- Combining a full uniform recurrence, the F-020 reserve step, and a bound
for the smooth/fixed low-index part closes one complete height step. -/
theorem logS_le_next_discreteBenchmark_of_recurrence
    (C δ K D : ℝ) (N k M y : ℕ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hlog : 0 < Real.log (N : ℝ)) (hN2 : 2 ≤ N)
    (hM : 2 ≤ M) (hMy : M ≤ y)
    (hrec : Research.logS N ≤ renewalBaseError N y +
      ∑ m ∈ Finset.Ico 1 y,
        uniformBinMajorant C δ N m * Research.logS m)
    (hInd : ∀ m ∈ Finset.Ico M y,
      Research.logS m ≤ K * Research.discreteRenewalBenchmark k m)
    (hzT : Research.renewalThreshold < Research.logLogNat N)
    (hwy : Research.logLogNat y ≤ Real.log (Research.logLogNat N))
    (hscalar :
      renewalPrincipal δ N *
          (Real.log (Research.logLogNat N) - Research.logLogNat M) +
        renewalError C δ N * ((y : ℝ) ^ 2 / Real.log M) + D ≤
      (N : ℝ) / Real.log (N + 1 : ℕ) *
        Real.log (Research.logLogNat N))
    (hlow : renewalBaseError N y +
        ∑ m ∈ Finset.Ico 1 M,
          uniformBinMajorant C δ N m * Research.logS m ≤
      K * Research.renewalProduct k
        (Real.log (Research.logLogNat N)) * D) :
    Research.logS N ≤ K * Research.discreteRenewalBenchmark (k + 1) N := by
  have hreserve := sum_uniform_mul_logS_add_reserve_le_next_discreteBenchmark
    C δ K D N k M y hC hδ hK hD hlog hN2 hM hMy hInd hzT hwy hscalar
  have hsplit := Finset.sum_Ico_consecutive
    (fun m => uniformBinMajorant C δ N m * Research.logS m)
    (show 1 ≤ M by omega) hMy
  calc
    Research.logS N ≤ renewalBaseError N y +
        ∑ m ∈ Finset.Ico 1 y,
          uniformBinMajorant C δ N m * Research.logS m := hrec
    _ = (renewalBaseError N y +
          ∑ m ∈ Finset.Ico 1 M,
            uniformBinMajorant C δ N m * Research.logS m) +
        ∑ m ∈ Finset.Ico M y,
          uniformBinMajorant C δ N m * Research.logS m := by
      rw [← hsplit]
      ring
    _ ≤ K * Research.renewalProduct k
          (Real.log (Research.logLogNat N)) * D +
        ∑ m ∈ Finset.Ico M y,
          uniformBinMajorant C δ N m * Research.logS m :=
      add_le_add_left hlow _
    _ ≤ K * Research.discreteRenewalBenchmark (k + 1) N := by
      linarith

/-- F-007 in exact quotient-bin form. -/
theorem logS_le_error_add_binSum (N y : ℕ) (hN : 1 ≤ N) (hy : 0 < y)
    (hNQ : N ≤ (N / y) * (N / y)) :
    Research.logS N ≤ Real.log 2 + Real.log N +
      (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
      2 * (Real.log 4 + 4) * N.sqrt +
        ∑ m ∈ Finset.Ico 1 y,
          (quotientPrimeBin N m).card * Research.logS m := by
  rw [← sum_largePrimes_eq_sum_bins Research.logS hy]
  exact Research.logS_le_error_add_primeSum N (N / y) hN hNQ

/-- F-008 and the grouped recurrence give a single uniform analytic
recurrence with explicit theta-error coefficients. -/
theorem exists_logS_le_majorized_binSum :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 2 ≤ X ∧
      ∀ (N y : ℕ), 1 ≤ N → 0 < y →
        N ≤ (N / y) * (N / y) → X ≤ ((N / y : ℕ) : ℝ) →
        Research.logS N ≤ Real.log 2 + Real.log N +
          (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
          2 * (Real.log 4 + 4) * N.sqrt +
            ∑ m ∈ Finset.Ico 1 y,
              quotientBinMajorant C N m * Research.logS m := by
  obtain ⟨C, hC, X, hX, hbins⟩ := exists_prime_quotient_bin_bound
  refine ⟨C, hC, X, hX, ?_⟩
  intro N y hN hy hNQ hXQ
  calc
    Research.logS N ≤ Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt +
          ∑ m ∈ Finset.Ico 1 y,
            (quotientPrimeBin N m).card * Research.logS m :=
      logS_le_error_add_binSum N y hN hy hNQ
    _ ≤ Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt +
          ∑ m ∈ Finset.Ico 1 y,
            quotientBinMajorant C N m * Research.logS m := by
      let E : ℝ := Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt
      change E + _ ≤ E + _
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro m hm
      have hmBounds := Finset.mem_Ico.mp hm
      have hmPos : 0 < m := hmBounds.1
      have hmy : m + 1 ≤ y := Nat.succ_le_iff.mpr hmBounds.2
      have hdiv : N / y ≤ N / (m + 1) :=
        Nat.div_le_div_left hmy (by omega : 0 < m + 1)
      have hXu : X ≤ ((N / (m + 1) : ℕ) : ℝ) :=
        le_trans hXQ (by exact_mod_cast hdiv)
      exact mul_le_mul_of_nonneg_right
        (show ((quotientPrimeBin N m).card : ℝ) ≤
            quotientBinMajorant C N m by
          exact hbins N m hmPos hXu)
        (logS_nonneg m)

/-- The same recurrence with both endpoint errors replaced by a single,
simpler lower-logarithm error term. -/
theorem exists_logS_le_simple_binSum :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 2 ≤ X ∧
      ∀ (N y : ℕ), 1 ≤ N → 0 < y →
        N ≤ (N / y) * (N / y) → X ≤ ((N / y : ℕ) : ℝ) →
        Research.logS N ≤ Real.log 2 + Real.log N +
          (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
          2 * (Real.log 4 + 4) * N.sqrt +
            ∑ m ∈ Finset.Ico 1 y,
              simpleBinMajorant C N m * Research.logS m := by
  obtain ⟨C, hC, X, hX, hrec⟩ := exists_logS_le_majorized_binSum
  refine ⟨C, hC, X, hX, ?_⟩
  intro N y hN hy hNQ hXQ
  calc
    Research.logS N ≤ Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt +
          ∑ m ∈ Finset.Ico 1 y,
            quotientBinMajorant C N m * Research.logS m :=
      hrec N y hN hy hNQ hXQ
    _ ≤ Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt +
          ∑ m ∈ Finset.Ico 1 y,
            simpleBinMajorant C N m * Research.logS m := by
      let E : ℝ := Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt
      change E + _ ≤ E + _
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro m hm
      have hmBounds := Finset.mem_Ico.mp hm
      have hmPos : 0 < m := hmBounds.1
      have hmy : m + 1 ≤ y := Nat.succ_le_iff.mpr hmBounds.2
      have hdiv : N / y ≤ N / (m + 1) :=
        Nat.div_le_div_left hmy (by omega : 0 < m + 1)
      have hu2 : 2 ≤ N / (m + 1) := by
        have : (2 : ℝ) ≤ ((N / (m + 1) : ℕ) : ℝ) :=
          le_trans hX (le_trans hXQ (by exact_mod_cast hdiv))
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right
        (quotientBinMajorant_le_simple C N m hC.le hmPos hu2)
        (logS_nonneg m)

/-- A floor-free-numerator version of the analytic recurrence. -/
theorem exists_logS_le_coarse_binSum :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 2 ≤ X ∧
      ∀ (N y : ℕ), 1 ≤ N → 0 < y →
        N ≤ (N / y) * (N / y) → X ≤ ((N / y : ℕ) : ℝ) →
        Research.logS N ≤ Real.log 2 + Real.log N +
          (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
          2 * (Real.log 4 + 4) * N.sqrt +
            ∑ m ∈ Finset.Ico 1 y,
              coarseBinMajorant C N m * Research.logS m := by
  obtain ⟨C, hC, X, hX, hrec⟩ := exists_logS_le_simple_binSum
  refine ⟨C, hC, X, hX, ?_⟩
  intro N y hN hy hNQ hXQ
  calc
    Research.logS N ≤ Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt +
          ∑ m ∈ Finset.Ico 1 y,
            simpleBinMajorant C N m * Research.logS m :=
      hrec N y hN hy hNQ hXQ
    _ ≤ Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt +
          ∑ m ∈ Finset.Ico 1 y,
            coarseBinMajorant C N m * Research.logS m := by
      let E : ℝ := Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt
      change E + _ ≤ E + _
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro m hm
      have hmBounds := Finset.mem_Ico.mp hm
      have hmPos : 0 < m := hmBounds.1
      have hmy : m + 1 ≤ y := Nat.succ_le_iff.mpr hmBounds.2
      have hdiv : N / y ≤ N / (m + 1) :=
        Nat.div_le_div_left hmy (by omega : 0 < m + 1)
      have hu2 : 2 ≤ N / (m + 1) := by
        have : (2 : ℝ) ≤ ((N / (m + 1) : ℕ) : ℝ) :=
          le_trans hX (le_trans hXQ (by exact_mod_cast hdiv))
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right
        (simpleBinMajorant_lt_coarse C N m hC.le hmPos hu2).le
        (logS_nonneg m)

/-- Fully floor-free kernel recurrence, assuming its explicit logarithmic
lower bounds are positive on the selected range. -/
theorem exists_logS_le_logLower_binSum :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 2 ≤ X ∧
      ∀ (N y : ℕ), 1 ≤ N → 0 < y →
        N ≤ (N / y) * (N / y) → X ≤ ((N / y : ℕ) : ℝ) →
        (∀ m ∈ Finset.Ico 1 y, 0 < binLogLower N m) →
        Research.logS N ≤ Real.log 2 + Real.log N +
          (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
          2 * (Real.log 4 + 4) * N.sqrt +
            ∑ m ∈ Finset.Ico 1 y,
              logLowerBinMajorant C N m * Research.logS m := by
  obtain ⟨C, hC, X, hX, hrec⟩ := exists_logS_le_coarse_binSum
  refine ⟨C, hC, X, hX, ?_⟩
  intro N y hN hy hNQ hXQ hL
  calc
    Research.logS N ≤ Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt +
          ∑ m ∈ Finset.Ico 1 y,
            coarseBinMajorant C N m * Research.logS m :=
      hrec N y hN hy hNQ hXQ
    _ ≤ Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt +
          ∑ m ∈ Finset.Ico 1 y,
            logLowerBinMajorant C N m * Research.logS m := by
      let E : ℝ := Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt
      change E + _ ≤ E + _
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro m hm
      have hmBounds := Finset.mem_Ico.mp hm
      have hmPos : 0 < m := hmBounds.1
      have hmy : m + 1 ≤ y := Nat.succ_le_iff.mpr hmBounds.2
      have hdiv : N / y ≤ N / (m + 1) :=
        Nat.div_le_div_left hmy (by omega : 0 < m + 1)
      have hu2 : 2 ≤ N / (m + 1) := by
        have : (2 : ℝ) ≤ ((N / (m + 1) : ℕ) : ℝ) :=
          le_trans hX (le_trans hXQ (by exact_mod_cast hdiv))
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right
        (coarseBinMajorant_le_logLower C N m hC.le hmPos hu2 (hL m hm))
        (logS_nonneg m)

/-- Common-logarithm form of the recurrence. The elementary hypotheses
`hscale` and `hhalf` isolate the only remaining denominator comparison. -/
theorem exists_logS_le_uniform_binSum :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 2 ≤ X ∧
      ∀ (N y : ℕ) (δ : ℝ), 1 ≤ N → 0 < y →
        N ≤ (N / y) * (N / y) → X ≤ ((N / y : ℕ) : ℝ) →
        0 ≤ δ → 0 < Real.log (N : ℝ) →
        (∀ m ∈ Finset.Ico 1 y,
          Real.log (N : ℝ) ≤ (1 + δ) * binLogLower N m) →
        (∀ m ∈ Finset.Ico 1 y,
          Real.log (N : ℝ) ≤ 2 * binLogLower N m) →
        Research.logS N ≤ Real.log 2 + Real.log N +
          (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
          2 * (Real.log 4 + 4) * N.sqrt +
            ∑ m ∈ Finset.Ico 1 y,
              uniformBinMajorant C δ N m * Research.logS m := by
  obtain ⟨C, hC, X, hX, hrec⟩ := exists_logS_le_logLower_binSum
  refine ⟨C, hC, X, hX, ?_⟩
  intro N y δ hN hy hNQ hXQ hδ hlog hscale hhalf
  have hL : ∀ m ∈ Finset.Ico 1 y, 0 < binLogLower N m := by
    intro m hm
    have := hhalf m hm
    linarith
  calc
    Research.logS N ≤ Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt +
          ∑ m ∈ Finset.Ico 1 y,
            logLowerBinMajorant C N m * Research.logS m :=
      hrec N y hN hy hNQ hXQ hL
    _ ≤ Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt +
          ∑ m ∈ Finset.Ico 1 y,
            uniformBinMajorant C δ N m * Research.logS m := by
      let E : ℝ := Real.log 2 + Real.log N +
        (Real.log 4 + 4) * ((N / y : ℕ) : ℝ) +
        2 * (Real.log 4 + 4) * N.sqrt
      change E + _ ≤ E + _
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro m hm
      have hmPos : 0 < m := (Finset.mem_Ico.mp hm).1
      exact mul_le_mul_of_nonneg_right
        (logLowerBinMajorant_le_uniform C δ N m hC.le hδ hmPos hlog
          (hL m hm) (hscale m hm) (hhalf m hm))
        (logS_nonneg m)

#print axioms exists_logS_le_majorized_binSum
#print axioms exists_logS_le_simple_binSum
#print axioms exists_logS_le_coarse_binSum
#print axioms exists_logS_le_logLower_binSum
#print axioms exists_logS_le_uniform_binSum

end ResearchPNT
