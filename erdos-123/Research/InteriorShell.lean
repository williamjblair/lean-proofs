import Research.ExactDegreeCorrections

namespace Erdos123

set_option maxHeartbeats 3000000

/-- A geometric grid between `q*a^R` and `q*c^R` has a point immediately
below any target in that interval.  The second inequality is the useful
multiplicative lower bound on that point. -/
theorem exists_geometric_grid_point {a c q R T : ℕ}
    (ha : 0 < a) (hac : a < c) (hq : 0 < q)
    (hlo : q * a ^ R ≤ T) (hhi : T ≤ q * c ^ R) :
    ∃ k : ℕ, k ≤ R ∧
      q * a ^ (R - k) * c ^ k ≤ T ∧
      a * T ≤ c * (q * a ^ (R - k) * c ^ k) := by
  let good : Finset ℕ := (Finset.range (R + 1)).filter
    (fun k => q * a ^ (R - k) * c ^ k ≤ T)
  have hgood : good.Nonempty := by
    refine ⟨0, ?_⟩
    simp [good, hlo]
  let k := good.max' hgood
  have hkmem : k ∈ good := Finset.max'_mem good hgood
  have hkR : k ≤ R := by
    have := (Finset.mem_filter.mp hkmem).1
    simp only [Finset.mem_range] at this
    omega
  have hklo : q * a ^ (R - k) * c ^ k ≤ T :=
    (Finset.mem_filter.mp hkmem).2
  refine ⟨k, hkR, hklo, ?_⟩
  by_cases hk : k = R
  · have hklo' : q * c ^ R ≤ T := by rw [hk] at hklo; simpa using hklo
    have hEq : T = q * c ^ R := by omega
    rw [hEq, hk]
    simp only [Nat.sub_self, pow_zero, mul_one]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt hac)
  · have hklt : k < R := by omega
    have hnextRange : k + 1 ∈ Finset.range (R + 1) := by simp; omega
    have hnextNot : ¬q * a ^ (R - (k + 1)) * c ^ (k + 1) ≤ T := by
      intro hle
      have hnextGood : k + 1 ∈ good := Finset.mem_filter.mpr ⟨hnextRange, hle⟩
      have hmax := Finset.le_max' good (k + 1) hnextGood
      omega
    have hnext : T < q * a ^ (R - (k + 1)) * c ^ (k + 1) := by omega
    have hsub : R - k = (R - (k + 1)) + 1 := by omega
    calc
      a * T ≤ a * (q * a ^ (R - (k + 1)) * c ^ (k + 1)) :=
        Nat.mul_le_mul_left a hnext.le
      _ = c * (q * a ^ (R - k) * c ^ k) := by
        rw [hsub, pow_succ, pow_succ]
        ring

/-- A long explicit strip of one homogeneous exponent level lies in a fixed
multiplicative window around the interior ray `(b^u c^v)^M`.  The strip is
placed beyond a prescribed `b`-exponent cutoff `H` and all its terms are strict
interior terms after one common `abc` shift. -/
theorem exists_long_interior_shell {a b c u v δ M H : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hacLt : a < c) (hcb : c < b)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (hu : 0 < u) (hv : 0 < v)
    (hHM : H + 2 ≤ M)
    (hdom : a ^ δ * (b * a ^ v) ^ M ≤ (c ^ v) ^ M) :
    let G := u + v
    let B := b ^ u * c ^ v
    let X := a * b * c * B ^ M
    ∃ p : Finset ℕ,
      M - (H + 2) + 1 ≤ p.card ∧
      (∀ z ∈ p, ∃ i j k : ℕ,
        0 < i ∧ 0 < j ∧ 0 < k ∧
        i + j + k = δ + G * M + 3 ∧
        u * M + H + 2 < j ∧
        z = eval3 a b c i j k) ∧
      (∀ z ∈ p, z ∈ Smooth3 a b c) ∧
      IsPrimitive p ∧
      (∀ z ∈ p, z ≤ X ∧ a * X ≤ c * z) := by
  dsimp only
  let G := u + v
  let B := b ^ u * c ^ v
  let X := a * b * c * B ^ M
  let J : Finset ℕ := Finset.Icc (H + 2) M
  have hR (s : ℕ) (hs : s ∈ J) : s ≤ v * M + δ := by
    have hsM : s ≤ M := (Finset.mem_Icc.mp hs).2
    have hvM : M ≤ v * M := by
      simpa only [one_mul] using Nat.mul_le_mul_right M (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hv))
    omega
  have hlow (s : ℕ) (hs : s ∈ J) :
      b ^ s * a ^ (v * M + δ - s) ≤ c ^ (v * M) := by
    have hsM : s ≤ M := (Finset.mem_Icc.mp hs).2
    have hbpow : b ^ s ≤ b ^ M := Nat.pow_le_pow_right (by omega) hsM
    have hapow : a ^ (v * M + δ - s) ≤ a ^ (v * M + δ) :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    calc
      b ^ s * a ^ (v * M + δ - s) ≤ b ^ M * a ^ (v * M + δ) :=
        Nat.mul_le_mul hbpow hapow
      _ = a ^ δ * (b * a ^ v) ^ M := by
        simp only [mul_pow, pow_mul, pow_add]
        ring
      _ ≤ (c ^ v) ^ M := hdom
      _ = c ^ (v * M) := by rw [pow_mul]
  have hhigh (s : ℕ) (hs : s ∈ J) :
      c ^ (v * M) ≤ b ^ s * c ^ (v * M + δ - s) := by
    have hsR := hR s hs
    have hcs : c ^ s ≤ b ^ s := Nat.pow_le_pow_left hcb.le _
    have hsplit : s + (v * M + δ - s) = v * M + δ := by omega
    calc
      c ^ (v * M) ≤ c ^ (v * M + δ) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ = c ^ s * c ^ (v * M + δ - s) := by rw [← pow_add, hsplit]
      _ ≤ b ^ s * c ^ (v * M + δ - s) :=
        Nat.mul_le_mul_right _ hcs
  let JS := {s : ℕ // s ∈ J}
  have hex (s : JS) : ∃ k : ℕ,
      k ≤ v * M + δ - s.1 ∧
      b ^ s.1 * a ^ (v * M + δ - s.1 - k) * c ^ k ≤ c ^ (v * M) ∧
      a * c ^ (v * M) ≤
        c * (b ^ s.1 * a ^ (v * M + δ - s.1 - k) * c ^ k) := by
    exact exists_geometric_grid_point (a := a) (c := c) (q := b ^ s.1)
      (R := v * M + δ - s.1) (T := c ^ (v * M))
      (by omega) hacLt (pow_pos (by omega) _) (hlow s.1 s.2) (hhigh s.1 s.2)
  let kval (s : JS) : ℕ := Classical.choose (hex s)
  have hkval (s : JS) := Classical.choose_spec (hex s)
  let term (s : JS) : ℕ :=
    eval3 a b c
      (v * M + δ - s.1 - kval s + 1)
      (u * M + s.1 + 1)
      (kval s + 1)
  let p : Finset ℕ := J.attach.image term
  have hterm_inj : Function.Injective term := by
    intro s t hst
    have hdvd : term s ∣ term t := by rw [hst]
    have hcoord := (eval3_dvd_iff ha hb hc hab hac hbc).mp hdvd
    have hdvd' : term t ∣ term s := by rw [hst]
    have hcoord' := (eval3_dvd_iff ha hb hc hab hac hbc).mp hdvd'
    apply Subtype.ext
    omega
  have hdegree (s : JS) :
      (v * M + δ - s.1 - kval s + 1) + (u * M + s.1 + 1) +
        (kval s + 1) = δ + G * M + 3 := by
    have hk := (hkval s).1
    have hsR := hR s.1 s.2
    have hsub1 : (v * M + δ - s.1 - kval s) + kval s =
        v * M + δ - s.1 := Nat.sub_add_cancel hk
    have hsub2 : (v * M + δ - s.1) + s.1 = v * M + δ :=
      Nat.sub_add_cancel hsR
    have hGM : G * M = u * M + v * M := by
      dsimp [G]
      rw [Nat.add_mul]
    rw [hGM]
    omega
  have hterm_value (s : JS) : term s =
      (a * b * c * b ^ (u * M)) *
        (b ^ s.1 * a ^ (v * M + δ - s.1 - kval s) * c ^ (kval s)) := by
    dsimp [term, eval3]
    rw [pow_succ, pow_succ, pow_succ, pow_add]
    ring
  have hX_value : X =
      (a * b * c * b ^ (u * M)) * c ^ (v * M) := by
    dsimp [X, B]
    simp only [mul_pow, pow_mul]
    ring
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · have hcard : p.card = J.card := by
      dsimp [p]
      rw [Finset.card_image_iff.mpr]
      · exact Finset.card_attach
      · intro s _hs t _ht hst
        exact hterm_inj hst
    rw [hcard]
    simp [J]
    omega
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, _hs, rfl⟩
    have hslo : H + 2 ≤ s.1 := (Finset.mem_Icc.mp s.2).1
    refine ⟨v * M + δ - s.1 - kval s + 1,
      u * M + s.1 + 1, kval s + 1,
      by omega, by omega, by omega, hdegree s, by omega, rfl⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, _hs, rfl⟩
    exact ⟨v * M + δ - s.1 - kval s + 1,
      u * M + s.1 + 1, kval s + 1, rfl⟩
  · intro x hx y hy hxy hdvd
    rcases Finset.mem_image.mp hx with ⟨s, _hs, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨t, _ht, rfl⟩
    apply hxy
    have he := exponents_eq_of_eval3_dvd_of_degree_eq ha hb hc hab hac hbc hdvd
      ((hdegree s).trans (hdegree t).symm)
    simp only [term]
    rw [he.1, he.2.1, he.2.2]
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, _hs, rfl⟩
    have hks := hkval s
    constructor
    · change term s ≤ X
      rw [hterm_value, hX_value]
      exact Nat.mul_le_mul_left _ hks.2.1
    · change a * X ≤ c * term s
      rw [hterm_value, hX_value]
      have hmul := Nat.mul_le_mul_left (a * b * c * b ^ (u * M)) hks.2.2
      convert hmul using 1 <;> ring

end Erdos123
