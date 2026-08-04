import Research.InteriorShell
import Research.PowerDomination
import Research.OptionalIntervalExtension
import Research.EdgeCodeProgressions
import Research.FiniteSeedGate

namespace Erdos123

set_option maxHeartbeats 5000000

/-- A member of a seed construction is either on a coordinate face, or is a
strict-interior term in the bounded `b`-exponent part of one exact level. -/
def IsSeedLevelSet (a b c D J : ℕ) (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∃ i j k : ℕ,
    i + j + k = D ∧ x = eval3 a b c i j k ∧
      ((i = 0 ∨ j = 0 ∨ k = 0) ∨
        (0 < i ∧ 0 < j ∧ 0 < k ∧ j ≤ J))

/-- A seed-level set consists of smooth terms. -/
theorem seedLevelSet_subset_smooth3 {a b c D J : ℕ} {s : Finset ℕ}
    (hs : IsSeedLevelSet a b c D J s) :
    ∀ x ∈ s, x ∈ Smooth3 a b c := by
  intro x hx
  rcases hs x hx with ⟨i, j, k, _hdeg, rfl, _hshape⟩
  exact ⟨i, j, k, rfl⟩

/-- A seed-level set is primitive. -/
theorem IsSeedLevelSet.isPrimitive {a b c D J : ℕ} {s : Finset ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hs : IsSeedLevelSet a b c D J s) : IsPrimitive s := by
  apply isPrimitive_of_exact_level ha hb hc hab hac hbc
  intro x hx
  rcases hs x hx with ⟨i, j, k, hdeg, hval, _hshape⟩
  exact ⟨i, j, k, hdeg, hval⟩

/-- A seed-level set is disjoint from a strict-interior shell lying beyond its
`b`-exponent cutoff. -/
theorem seedLevelSet_disjoint_high_shell
    {a b c D J : ℕ} {s p : Finset ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hs : IsSeedLevelSet a b c D J s)
    (hp : ∀ x ∈ p, ∃ i j k : ℕ,
      0 < i ∧ 0 < j ∧ 0 < k ∧ i + j + k = D ∧ J < j ∧
        x = eval3 a b c i j k) :
    Disjoint s p := by
  rw [Finset.disjoint_left]
  intro x hxs hxp
  rcases hs x hxs with ⟨i, j, k, _hdeg, hxval, hshape⟩
  rcases hp x hxp with ⟨i', j', k', hi', hj', hk', _hdeg', hjHigh, hxval'⟩
  have heq : eval3 a b c i j k = eval3 a b c i' j' k' := by
    rw [← hxval, ← hxval']
  have hd1 : eval3 a b c i j k ∣ eval3 a b c i' j' k' := by rw [heq]
  have hd2 : eval3 a b c i' j' k' ∣ eval3 a b c i j k := by rw [heq]
  have hc1 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd1
  have hc2 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd2
  rcases hshape with hface | hinterior
  · rcases hface with rfl | rfl | rfl <;> omega
  · omega

/-- Ordered bases `a<c<b` have primitive represented intervals of arbitrarily
large multiplicative width.  The construction combines a homogeneous AP-radix
interval, exact-degree face corrections, and a long optional interior shell. -/
theorem ordered_arbitrarily_wide_primitive_seed
    {a b c R Nmin : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hacLt : a < c) (hcb : c < b)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hR : 1 < R) :
    ∃ N : ℕ, Nmin ≤ N ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n → n ≤ R * N →
      IsRepresentable (Smooth3 a b c) n := by
  let H := edgeDigitDepth c
  let u := H + 2
  have hu : 0 < u := by dsimp [u]; omega
  have huBand : edgeDigitDepth c + 1 < u := by dsimp [u, H]; omega
  rcases exists_positive_pow_multiple_le (a := a) (c := c) (K := 2 * b) hacLt with
    ⟨v, hv, hvDom⟩
  let G := u + v
  let A := a ^ G
  let B := b ^ u * c ^ v
  let q := a * b * c
  let L := 4 * A * B
  have hG : 0 < G := by dsimp [G]; omega
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hAB : A < B := by
    have hacPow : a ^ G < c ^ G := Nat.pow_lt_pow_left hacLt (Nat.ne_of_gt hG)
    have hcbPow : c ^ u < b ^ u := Nat.pow_lt_pow_left hcb (Nat.ne_of_gt hu)
    calc
      A = a ^ G := rfl
      _ < c ^ G := hacPow
      _ = c ^ u * c ^ v := by dsimp [G]; rw [pow_add]
      _ ≤ b ^ u * c ^ v := Nat.mul_le_mul_right (c ^ v) hcbPow.le
      _ = B := rfl
  have hcopAB : Nat.Coprime A B := by
    have ha_bc : Nat.Coprime a (b * c) := hab.mul_right hac
    have ha_bu : Nat.Coprime (a ^ G) (b ^ u) := hab.pow G u
    have ha_cv : Nat.Coprime (a ^ G) (c ^ v) := hac.pow G v
    exact ha_bu.mul_right ha_cv
  have hL : 1 < L := by
    change 1 < 4 * A * B
    have hA1 : 1 ≤ A := hA
    have hB1 : 1 ≤ B := hB
    nlinarith
  rcases edgeCodeEval_arbitrarily_long_progressions ha hb hc hacLt hab hac hbc L hL with
    ⟨n₀, B₀, d, hd, words, hwords⟩
  let δ := H + n₀ - 1
  have hqd : 0 < q * d := by dsimp [q]; positivity
  rcases exact_degree_bounded_face_corrections ha hb hc hacLt.le hab hac hbc hqd with
    ⟨Ccorr, D₀, hCcorr, hcorr⟩
  have hsmallShellBase : b * a ^ v < c ^ v := by
    have hpos : 0 < b * a ^ v := by positivity
    nlinarith [hvDom]
  rcases eventually_const_mul_pow_le_pow (C := a ^ δ) hsmallShellBase with
    ⟨Nshell, hNshell⟩
  have hsmallCorrBase : c ^ G < B := by
    dsimp [G, B]
    rw [pow_add]
    have hpow := Nat.pow_lt_pow_left hcb (Nat.ne_of_gt hu)
    exact Nat.mul_lt_mul_of_pos_right hpow (pow_pos (by omega) v)
  rcases eventually_const_mul_pow_le_pow
      (C := Ccorr * c ^ (δ + 3)) hsmallCorrBase with
    ⟨Ncorr, hNcorr⟩
  let Step := q * d
  let K := q * B₀ + Step * L + 1
  let T := c * R * K * B
  let M := Nshell + Ncorr + D₀ + T + Nmin + H + 3
  have hMNshell : Nshell ≤ M := by dsimp [M]; omega
  have hMNcorr : Ncorr ≤ M := by dsimp [M]; omega
  have hMDegree : D₀ ≤ δ + G * M + 3 := by
    have hD0M : D₀ ≤ M := by dsimp [M]; omega
    have hGM : M ≤ G * M := by
      simpa only [one_mul] using Nat.mul_le_mul_right M (by omega : 1 ≤ G)
    exact hD0M.trans (hGM.trans (by omega))
  have hHM : H + 2 ≤ M := by dsimp [M]; omega
  have hcardTarget : T ≤ M - (H + 2) + 1 := by dsimp [M]; omega
  have hshellDom : a ^ δ * (b * a ^ v) ^ M ≤ (c ^ v) ^ M :=
    hNshell M hMNshell
  have hcorrDom0 :
      (Ccorr * c ^ (δ + 3)) * (c ^ G) ^ M ≤ B ^ M :=
    hNcorr M hMNcorr
  let D := δ + G * M + 3
  have hcorrDom : Ccorr * c ^ D ≤ B ^ M := by
    dsimp [D]
    rw [show δ + G * M + 3 = (δ + 3) + G * M by omega, pow_add,
      show c ^ (G * M) = (c ^ G) ^ M by rw [pow_mul]]
    simpa [mul_assoc] using hcorrDom0
  rcases homogeneousRadixRep_large_interval hA hB hcopAB M with
    ⟨U, V, hUV, hwidth, hradix⟩
  let Mass := homogeneousWeightMass A B M
  let Offset := q * (B₀ * Mass)
  let Z := Ccorr * c ^ D
  let Lo := Offset + Step * U + Z
  let Hi := Offset + Step * V
  have hMass : Mass ≤ B ^ (M + 1) :=
    homogeneousWeightMass_le_pow hA hAB
  have hUbound : U ≤ L * Mass :=
    (HomogeneousRadixRep.le_mass (hradix U (le_refl U) hUV))
  have hZ : Z ≤ B ^ M := by exact hcorrDom
  have hBpowStep : B ^ M ≤ B ^ (M + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hStepWidth : Step * (2 * A * B ^ (M + 1)) ≤ Step * (V - U) :=
    Nat.mul_le_mul_left Step hwidth
  have hcoef : q + 1 ≤ Step * (2 * A * B) := by
    have hq : 0 < q := by dsimp [q]; positivity
    have hfactor : 1 ≤ d * A * B :=
      (Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (Nat.ne_of_gt hd) (Nat.ne_of_gt hA))
          (Nat.ne_of_gt hB)))
    calc
      q + 1 ≤ 2 * q := by omega
      _ ≤ (2 * q) * (d * A * B) := Nat.le_mul_of_pos_right _ hfactor
      _ = Step * (2 * A * B) := by dsimp [Step]; ring
  have hroom : Z + q * B ^ M ≤ Step * (V - U) := by
    calc
      Z + q * B ^ M ≤ (q + 1) * B ^ M := by
        have := hZ
        nlinarith
      _ ≤ (Step * (2 * A * B)) * B ^ M :=
        Nat.mul_le_mul_right _ hcoef
      _ = Step * (2 * A * B ^ (M + 1)) := by rw [pow_succ]; ring
      _ ≤ Step * (V - U) := hStepWidth
  have hLoHi : Lo ≤ Hi := by
    have hUVadd : U + (V - U) = V := Nat.add_sub_of_le hUV
    have hZroom : Z ≤ Step * (V - U) :=
      (Nat.le_add_right Z (q * B ^ M)).trans hroom
    dsimp [Lo, Hi]
    calc
      Offset + Step * U + Z = Offset + (Step * U + Z) := by omega
      _ ≤ Offset + (Step * U + Step * (V - U)) :=
        Nat.add_le_add_left (Nat.add_le_add_left hZroom _) _
      _ = Offset + Step * V := by rw [← Nat.mul_add, hUVadd]
  have hWidthX : q * B ^ M ≤ Hi - Lo := by
    apply Nat.le_sub_of_add_le
    have hUVadd : U + (V - U) = V := Nat.add_sub_of_le hUV
    dsimp [Lo, Hi]
    calc
      q * B ^ M + (Offset + Step * U + Z) =
          Offset + (Step * U + (Z + q * B ^ M)) := by omega
      _ ≤ Offset + (Step * U + Step * (V - U)) :=
        Nat.add_le_add_left (Nat.add_le_add_left hroom _) _
      _ = Offset + Step * V := by rw [← Nat.mul_add, hUVadd]
  have hLoBound : Lo ≤ K * B ^ (M + 1) := by
    have hOff : Offset ≤ (q * B₀) * B ^ (M + 1) := by
      dsimp [Offset]
      convert Nat.mul_le_mul_left (q * B₀) hMass using 1 <;> ring
    have hSU : Step * U ≤ (Step * L) * B ^ (M + 1) := by
      calc
        Step * U ≤ Step * (L * Mass) := Nat.mul_le_mul_left Step hUbound
        _ ≤ Step * (L * B ^ (M + 1)) :=
          Nat.mul_le_mul_left Step (Nat.mul_le_mul_left L hMass)
        _ = (Step * L) * B ^ (M + 1) := by ring
    have hZ' : Z ≤ B ^ (M + 1) := hZ.trans hBpowStep
    dsimp [Lo, K]
    nlinarith
  have hLoPos : 0 < Lo := by
    have hZpos : 0 < Z := by dsimp [Z]; positivity
    dsimp [Lo]
    omega
  have hsucc_le_cpow : ∀ t : ℕ, t + 1 ≤ c ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        rw [pow_succ]
        have hc2 : 2 ≤ c := by omega
        calc
          t + 1 + 1 ≤ 2 * (t + 1) := by omega
          _ ≤ c * c ^ t := Nat.mul_le_mul hc2 ih
          _ = c ^ t * c := by ring
  have hNminLo : Nmin ≤ Lo := by
    have hNminM : Nmin ≤ M := by dsimp [M]; omega
    have hMD : M ≤ D := by
      have hGM : M ≤ G * M := by
        simpa only [one_mul] using Nat.mul_le_mul_right M (by omega : 1 ≤ G)
      dsimp [D]
      omega
    have hcD : D + 1 ≤ c ^ D := hsucc_le_cpow D
    have hcZ : c ^ D ≤ Z := by
      dsimp [Z]
      exact Nat.le_mul_of_pos_left _ hCcorr
    have hDleZ : D ≤ Z := (Nat.le_add_right D 1).trans (hcD.trans hcZ)
    have hZleLo : Z ≤ Lo := by dsimp [Lo]; omega
    exact hNminM.trans (hMD.trans (hDleZ.trans hZleLo))
  rcases exists_long_interior_shell ha hb hc hacLt hcb hab hac hbc hu hv hHM
      hshellDom (H := H) with ⟨p, hpCard, hpShape, hpSmooth, hpPrim, hpBounds⟩
  have hpDegree : ∀ x ∈ p, ∃ i j k : ℕ,
      i + j + k = D ∧ x = eval3 a b c i j k := by
    intro x hx
    rcases hpShape x hx with ⟨i, j, k, _hi, _hj, _hk, hdeg, _hhigh, hval⟩
    exact ⟨i, j, k, by simpa [D] using hdeg, hval⟩
  have hpHigh : ∀ x ∈ p, ∃ i j k : ℕ,
      0 < i ∧ 0 < j ∧ 0 < k ∧ i + j + k = D ∧
        u * M + H + 1 < j ∧ x = eval3 a b c i j k := by
    intro x hx
    rcases hpShape x hx with ⟨i, j, k, hi, hj, hk, hdeg, hhigh, hval⟩
    exact ⟨i, j, k, hi, hj, hk, by simpa [D] using hdeg, by omega, hval⟩
  have hpFit : ∀ x ∈ p, x ≤ Hi - Lo + 1 := by
    intro x hx
    have hxX : x ≤ q * B ^ M := by
      simpa [q, B] using (hpBounds x hx).1
    exact hxX.trans (hWidthX.trans (Nat.le_add_right _ 1))
  have hbase : ∀ target : ℕ, Lo ≤ target → target ≤ Hi →
      ∃ s : Finset ℕ,
        (∀ x ∈ s, x ∈ Smooth3 a b c) ∧
        (∀ x ∈ s, ∃ i j k : ℕ,
          i + j + k = D ∧ x = eval3 a b c i j k) ∧
        Disjoint s p ∧ s.sum id = target := by
    intro target htLo htHi
    have hOffT : Offset ≤ target := by dsimp [Lo] at htLo; omega
    let Y := target - Offset
    have hYeq : Offset + Y = target := Nat.add_sub_of_le hOffT
    let r := Y % Step
    rcases hcorr D hMDegree r with
      ⟨corr, hcorrSmooth, hcorrShape, hcorrPrim, hcorrMod, hcorrBound⟩
    have hcorrZ : corr.sum id ≤ Z := by simpa [Z] using hcorrBound
    have hZY : Z ≤ Y := by
      dsimp [Lo] at htLo
      dsimp [Y]
      omega
    have hcorrY : corr.sum id ≤ Y := hcorrZ.trans hZY
    have hYmod : Y ≡ r [MOD Step] := (Nat.mod_modEq Y Step).symm
    have hmodEq : Y ≡ corr.sum id [MOD Step] := hYmod.trans hcorrMod.symm
    have hsubMod := hmodEq.sub hcorrY (le_refl (corr.sum id))
      (Nat.ModEq.refl (n := Step) (corr.sum id))
    have hdvd : Step ∣ Y - corr.sum id := by
      apply Nat.dvd_of_mod_eq_zero
      simpa [Nat.ModEq] using hsubMod
    let coeff := (Y - corr.sum id) / Step
    have hStepCoeff : Step * coeff = Y - corr.sum id :=
      Nat.mul_div_cancel' hdvd
    have hcoeffU : U ≤ coeff := by
      apply (Nat.le_div_iff_mul_le hqd).2
      dsimp [Lo] at htLo
      have : Step * U + corr.sum id ≤ Y := by omega
      have hmul : Step * U ≤ Y - corr.sum id := Nat.le_sub_of_add_le this
      change U * Step ≤ Y - corr.sum id
      simpa [Nat.mul_comm] using hmul
    have hcoeffV : coeff ≤ V := by
      apply Nat.le_of_mul_le_mul_left (c := Step) _ hqd
      rw [hStepCoeff]
      dsimp [Hi] at htHi
      have hYV : Y ≤ Step * V := by
        dsimp [Y]
        omega
      exact (Nat.sub_le _ _).trans hYV
    have hcoeffRep := hradix coeff hcoeffU hcoeffV
    rcases homogeneousRadixRep_realized_by_edge_AP ha hb hc hacLt hab hac hbc
        huBand words hwords hcoeffRep with ⟨ap, hapBand, hapSum⟩
    have hapSeed : IsSeedLevelSet a b c D (u * M + H + 1) ap := by
      intro x hx
      rcases hapBand x hx with ⟨i, j, k, hi, hj, hk, hdeg, hjBound, hval⟩
      exact ⟨i, j, k, by simpa [D] using hdeg, hval,
        Or.inr ⟨hi, hj, hk, hjBound⟩⟩
    have hcorrSeed : IsSeedLevelSet a b c D (u * M + H + 1) corr := by
      intro x hx
      rcases hcorrShape x hx with ⟨i, j, k, hdeg, hval, hface⟩
      exact ⟨i, j, k, hdeg, hval, Or.inl hface⟩
    have hdisAPCorr : Disjoint ap corr := by
      rw [Finset.disjoint_left]
      intro x hxap hxcorr
      rcases hapBand x hxap with ⟨i, j, k, hi, hj, hk, _hdeg, _hjB, hval⟩
      rcases hcorrShape x hxcorr with ⟨i', j', k', _hdeg', hval', hface⟩
      have heq : eval3 a b c i j k = eval3 a b c i' j' k' := by
        rw [← hval, ← hval']
      have hd1 : eval3 a b c i j k ∣ eval3 a b c i' j' k' := by rw [heq]
      have hd2 : eval3 a b c i' j' k' ∣ eval3 a b c i j k := by rw [heq]
      have hc1 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd1
      have hc2 := (eval3_dvd_iff ha hb hc hab hac hbc).mp hd2
      rcases hface with rfl | rfl | rfl <;> omega
    let s := ap ∪ corr
    have hsSeed : IsSeedLevelSet a b c D (u * M + H + 1) s := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxa | hxc
      · exact hapSeed x hxa
      · exact hcorrSeed x hxc
    refine ⟨s, seedLevelSet_subset_smooth3 hsSeed, ?_,
      seedLevelSet_disjoint_high_shell ha hb hc hab hac hbc hsSeed hpHigh, ?_⟩
    · intro x hx
      rcases hsSeed x hx with ⟨i, j, k, hdeg, hval, _hshape⟩
      exact ⟨i, j, k, hdeg, hval⟩
    · dsimp [s]
      rw [Finset.sum_union hdisAPCorr]
      have hsumEq : Step * coeff + corr.sum id = Y := by
        rw [hStepCoeff]
        exact Nat.sub_add_cancel hcorrY
      calc
        ap.sum id + corr.sum id =
            q * (B₀ * homogeneousWeightMass A B M + d * coeff) + corr.sum id :=
          by rw [hapSum]
        _ = Offset + (Step * coeff + corr.sum id) := by
          dsimp [Offset, Step, Mass]
          ring
        _ = Offset + Y := by rw [hsumEq]
        _ = target := hYeq
  have hsumLower : p.card * (a * (q * B ^ M)) ≤ c * p.sum id := by
    have hsum := Finset.sum_le_sum (s := p) (fun x hx => (hpBounds x hx).2)
    calc
      p.card * (a * (q * B ^ M)) =
          ∑ _x ∈ p, a * (a * b * c * (b ^ u * c ^ v) ^ M) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        dsimp [q, B]
      _ ≤ ∑ x ∈ p, c * x := hsum
      _ = c * p.sum id := by
        rw [Finset.mul_sum]
        simp only [id_eq]
  have hpCardT : T ≤ p.card := hcardTarget.trans hpCard
  have hoptionalEnough : (R - 1) * Lo ≤ p.sum id := by
    have hscaledLo : c * ((R - 1) * Lo) ≤ c * p.sum id := by
      calc
        c * ((R - 1) * Lo) ≤
            c * ((R - 1) * (K * B ^ (M + 1))) :=
          Nat.mul_le_mul_left c (Nat.mul_le_mul_left (R - 1) hLoBound)
        _ ≤ p.card * (a * (q * B ^ M)) := by
          have hpow : B ^ (M + 1) = B * B ^ M := by rw [pow_succ]; ring
          rw [hpow]
          have hTdef : T = c * R * K * B := rfl
          have hcoefT : c * (R - 1) * K * B ≤ p.card := by
            calc
              c * (R - 1) * K * B ≤ c * R * K * B := by
                gcongr
                omega
              _ = T := hTdef.symm
              _ ≤ p.card := hpCardT
          have haq : 1 ≤ a * q := by
            have hq : 0 < q := by dsimp [q]; positivity
            nlinarith
          calc
            c * ((R - 1) * (K * (B * B ^ M))) =
                (c * (R - 1) * K * B) * B ^ M := by ring
            _ ≤ p.card * B ^ M := Nat.mul_le_mul_right _ hcoefT
            _ ≤ p.card * (a * q * B ^ M) := by
              have hh : B ^ M ≤ a * q * B ^ M := by
                simpa only [one_mul] using Nat.mul_le_mul_right (B ^ M) haq
              exact Nat.mul_le_mul_left p.card hh
            _ = p.card * (a * (q * B ^ M)) := by ring
        _ ≤ c * p.sum id := hsumLower
    exact Nat.le_of_mul_le_mul_left hscaledLo (by omega : 0 < c)
  have hRLo : R * Lo ≤ Hi + p.sum id := by
    have hbaseWidth : Lo ≤ Hi := hLoHi
    have hRdecomp : R - 1 + 1 = R := Nat.sub_add_cancel (by omega : 1 ≤ R)
    calc
      R * Lo = (R - 1 + 1) * Lo := by rw [hRdecomp]
      _ = Lo + (R - 1) * Lo := by ring
      _ ≤ Hi + p.sum id := Nat.add_le_add hbaseWidth hoptionalEnough
  refine ⟨Lo, hNminLo, hLoPos, ?_⟩
  intro target htLo htR
  apply representable_interval_extend_by_level_finset ha hb hc hab hac hbc
    hLoHi hpFit hpSmooth hpDegree hbase target htLo
  exact htR.trans hRLo

/-- The arbitrarily wide seed discharges the flexible finite-seed gate for
strictly ordered bases `a<c<b`. -/
theorem ordered_three_base_is_dComplete
    {a b c : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hacLt : a < c) (hcb : c < b)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    IsDComplete (Smooth3 a b c) := by
  rcases flexible_finite_seed_gate ha hb hc hab hac hbc with
    ⟨N₀, C, hN₀, hC, hgate⟩
  rcases ordered_arbitrarily_wide_primitive_seed ha hb hc hacLt hcb hab hac hbc hC
      (Nmin := N₀) with ⟨N, hN₀N, _hNpos, hseed⟩
  exact hgate N hN₀N hseed

end Erdos123
