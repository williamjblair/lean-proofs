import Mathlib

namespace Erdos123

/-- Recursive bounded-coefficient sums with homogeneous two-base weights.
At stage `M`, this is exactly the set of sums
`Σ_{i=0}^M s_i A^(M-i) B^i` with `s_i<L`. -/
def HomogeneousRadixRep (A B L : ℕ) : ℕ → ℕ → Prop
  | 0, n => n < L
  | M + 1, n => ∃ x s : ℕ,
      HomogeneousRadixRep A B L M x ∧ s < L ∧
        n = A * x + B ^ (M + 1) * s

private theorem exists_interval_shift_decomposition
    {U V P K y : ℕ} (hP : 0 < P) (hK : 0 < K)
    (hUV : U ≤ V) (hwidth : P - 1 ≤ V - U)
    (hyLo : U ≤ y) (hyHi : y ≤ V + P * (K - 1)) :
    ∃ x q : ℕ, U ≤ x ∧ x ≤ V ∧ q < K ∧ y = x + P * q := by
  by_cases hq : (y - U) / P < K
  · let q := (y - U) / P
    let x := U + (y - U) % P
    refine ⟨x, q, by dsimp [x]; omega, ?_, hq, ?_⟩
    · have hmod : (y - U) % P ≤ P - 1 := by
        have := Nat.mod_lt (y - U) hP
        omega
      have hVU : U + (P - 1) ≤ V := by
        have hh := (Nat.le_sub_iff_add_le hUV).mp hwidth
        simpa [Nat.add_comm] using hh
      dsimp [x]
      exact (Nat.add_le_add_left hmod U).trans hVU
    · have hdecomp := Nat.mod_add_div (y - U) P
      have hy : U + (y - U) = y := Nat.add_sub_of_le hyLo
      dsimp [x, q]
      omega
  · have hqge : K ≤ (y - U) / P := by omega
    have hKP : K * P ≤ y - U :=
      (Nat.le_div_iff_mul_le hP).mp hqge
    have hPK : P * K ≤ y - U := by simpa [Nat.mul_comm] using hKP
    let q := K - 1
    have hqK : q < K := by dsimp [q]; omega
    have hPqPK : P * q < P * K := Nat.mul_lt_mul_of_pos_left hqK hP
    have hPq : P * q ≤ y :=
      hPqPK.le.trans (hPK.trans (Nat.sub_le y U))
    have hUPq : U + P * q ≤ y := by
      have hh : P * q ≤ y - U := hPqPK.le.trans hPK
      have hh' := (Nat.le_sub_iff_add_le hyLo).mp hh
      simpa [Nat.add_comm] using hh'
    let x := y - P * q
    refine ⟨x, q, ?_, ?_, hqK, ?_⟩
    · dsimp [x]
      exact Nat.le_sub_of_add_le hUPq
    · dsimp [x]
      exact Nat.sub_le_iff_le_add.mpr (by simpa [q, Nat.add_comm] using hyHi)
    · dsimp [x]
      exact (Nat.sub_add_cancel hPq).symm

private theorem bounded_residue_power {A B e : ℕ}
    (hA : 0 < A) (hcop : Nat.Coprime A B) (n : ℕ) :
    ∃ r : ℕ, r < A ∧ (B ^ e * r) % A = n % A := by
  let f : Fin A → Fin A := fun r =>
    ⟨(B ^ e * (r : ℕ)) % A, Nat.mod_lt _ hA⟩
  have hf : Function.Injective f := by
    intro r s hrs
    have hmod : B ^ e * (r : ℕ) ≡ B ^ e * (s : ℕ) [MOD A] :=
      congrArg Fin.val hrs
    have hpowCop : Nat.Coprime A (B ^ e) := hcop.pow_right e
    have hrsMod : (r : ℕ) ≡ (s : ℕ) [MOD A] :=
      Nat.ModEq.cancel_left_of_coprime hpowCop (by
        simpa [Nat.mul_comm] using hmod)
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hrsMod r.isLt s.isLt)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp⟩
  let target : Fin A := ⟨n % A, Nat.mod_lt _ hA⟩
  rcases hbij.2 target with ⟨r, hr⟩
  exact ⟨r, r.isLt, congrArg Fin.val hr⟩

/-- One interval-amplification step for homogeneous bounded radix sums. -/
theorem homogeneousRadixRep_interval_step
    {A B L M U V K : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hcop : Nat.Coprime A B)
    (hK : 0 < K) (hL : L = A * K)
    (hUV : U ≤ V)
    (hwidth : B ^ (M + 1) - 1 ≤ V - U)
    (hrep : ∀ n, U ≤ n → n ≤ V → HomogeneousRadixRep A B L M n) :
    ∀ n,
      A * U + B ^ (M + 1) * (A - 1) ≤ n →
      n ≤ A * (V + B ^ (M + 1) * (K - 1)) →
      HomogeneousRadixRep A B L (M + 1) n := by
  intro n hnLo hnHi
  let P := B ^ (M + 1)
  have hP : 0 < P := pow_pos hB _
  rcases bounded_residue_power (e := M + 1) hA hcop n with ⟨r, hrA, hrmod⟩
  let z := P * r
  have hzle : z ≤ P * (A - 1) := by
    dsimp [z]
    exact Nat.mul_le_mul_left P (by omega)
  have hzn : z ≤ n := by
    have hbase : P * (A - 1) ≤ n := by
      dsimp [P] at ⊢
      omega
    exact hzle.trans hbase
  have hmod : (n - z) % A = 0 := by
    have hnmod : n ≡ n % A [MOD A] := by simp [Nat.ModEq]
    have hzmod : z ≡ n % A [MOD A] := by
      show z % A = (n % A) % A
      simp [z, P, hrmod, Nat.mod_eq_of_lt (Nat.mod_lt n hA)]
    have hh := Nat.ModEq.sub hzn (le_refl (n % A)) hnmod hzmod
    simpa [Nat.ModEq] using hh
  have hdiv : A ∣ n - z := Nat.dvd_iff_mod_eq_zero.mpr hmod
  let y := (n - z) / A
  have hAy : A * y = n - z := Nat.mul_div_cancel' hdiv
  have hyLo : U ≤ y := by
    apply (Nat.le_div_iff_mul_le hA).2
    have hAUz : A * U + z ≤ n := by
      have hzbound : z ≤ P * (A - 1) := hzle
      dsimp [P] at hzbound
      omega
    have hAU : A * U ≤ n - z := Nat.le_sub_of_add_le hAUz
    simpa [Nat.mul_comm] using hAU
  have hyHi : y ≤ V + P * (K - 1) := by
    apply Nat.le_of_mul_le_mul_left (c := A) _ hA
    rw [hAy]
    dsimp [z, P] at hnHi ⊢
    omega
  rcases exists_interval_shift_decomposition hP hK hUV
      (by simpa [P] using hwidth) hyLo hyHi with
    ⟨x, q, hxLo, hxHi, hqK, hy⟩
  let s := A * q + r
  have hsL : s < L := by
    rw [hL]
    dsimp [s]
    nlinarith
  refine ⟨x, s, hrep x hxLo hxHi, hsL, ?_⟩
  have hnEq : n = A * y + z := by rw [hAy]; omega
  rw [hnEq, hy]
  dsimp [s, z, P]
  ring

/-- Choosing `L=4AB` gives a robust interval whose width grows at least like
`B^(M+1)` at every homogeneous-radix stage. -/
theorem homogeneousRadixRep_large_interval
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hcop : Nat.Coprime A B) :
    let L := 4 * A * B
    ∀ M : ℕ, ∃ U V : ℕ,
      U ≤ V ∧ 2 * A * B ^ (M + 1) ≤ V - U ∧
      ∀ n, U ≤ n → n ≤ V → HomogeneousRadixRep A B L M n := by
  dsimp only
  let L := 4 * A * B
  intro M
  induction M with
  | zero =>
      refine ⟨0, L - 1, Nat.zero_le _, ?_, ?_⟩
      · dsimp [L]
        have hAB : 1 ≤ A * B := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
          (Nat.ne_of_gt hA) (Nat.ne_of_gt hB))
        rw [pow_one]
        have hh : 2 * (A * B) ≤ 4 * (A * B) - 1 := by omega
        simpa [Nat.mul_assoc] using hh
      · intro n _hn0 hn
        simp only [HomogeneousRadixRep]
        dsimp [L] at hn ⊢
        have hLpos : 0 < 4 * A * B := by positivity
        omega
  | succ M ih =>
      rcases ih with ⟨U, V, hUV, hwidth, hrep⟩
      let K := 4 * B
      let U' := A * U + B ^ (M + 1) * (A - 1)
      let V' := A * (V + B ^ (M + 1) * (K - 1))
      have hstep := homogeneousRadixRep_interval_step hA hB hcop
        (K := K) (by dsimp [K]; positivity) (by dsimp [L, K]; ring)
        hUV (by
          have hcoef : 0 < 2 * A := by positivity
          have hle : B ^ (M + 1) ≤ (2 * A) * B ^ (M + 1) :=
            Nat.le_mul_of_pos_left _ hcoef
          exact (Nat.sub_le _ _).trans (hle.trans hwidth)) hrep
      refine ⟨U', V', ?_, ?_, ?_⟩
      · dsimp [U', V', K]
        rw [Nat.mul_add]
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left A hUV
        · have hB1 : 1 ≤ B := hB
          have hKcoef : A - 1 ≤ A * (4 * B - 1) := by
            calc
              A - 1 ≤ A := Nat.sub_le _ _
              _ ≤ A * (4 * B - 1) :=
                Nat.le_mul_of_pos_right A (by omega)
          have hh := Nat.mul_le_mul_left (B ^ (M + 1)) hKcoef
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh
      · apply Nat.le_sub_of_add_le
        dsimp [U', V', K]
        rw [Nat.mul_add]
        have hB1 : 1 ≤ B := hB
        have hcoef : (A - 1) + 2 * A * B ≤ A * (4 * B - 1) := by
          calc
            (A - 1) + 2 * A * B ≤ A + 2 * A * B :=
              Nat.add_le_add_right (Nat.sub_le A 1) _
            _ = A * (2 * B + 1) := by ring
            _ ≤ A * (4 * B - 1) := by
              exact Nat.mul_le_mul_left A (by omega)
        have hcoefP := Nat.mul_le_mul_left (B ^ (M + 1)) hcoef
        have hpow : B ^ (M + 2) = B ^ (M + 1) * B := by
          rw [show M + 2 = (M + 1) + 1 by omega, pow_succ]
        rw [hpow]
        calc
          2 * A * (B ^ (M + 1) * B) +
              (A * U + B ^ (M + 1) * (A - 1)) =
            A * U + B ^ (M + 1) * ((A - 1) + 2 * A * B) := by ring
          _ ≤ A * U + B ^ (M + 1) * (A * (4 * B - 1)) :=
            Nat.add_le_add_left hcoefP _
          _ ≤ A * V + B ^ (M + 1) * (A * (4 * B - 1)) :=
            Nat.add_le_add_right (Nat.mul_le_mul_left A hUV) _
          _ = A * V + A * (B ^ (M + 1) * (4 * B - 1)) := by ring
      · intro n hnLo hnHi
        exact hstep n hnLo hnHi

end Erdos123
