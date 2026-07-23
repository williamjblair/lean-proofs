import Research.UpperCombinatorics

namespace Erdos796

/-- If every prime factor of a sufficiently large integer is at most `W`, the
integer splits into two factors both exceeding `W`.  The proof uses the least
divisor above `W`. -/
theorem exists_large_split_of_primeFactors_le
    {W d : ℕ} (hW : 1 < W) (hd : W ^ 3 < d)
    (hall : ∀ p : ℕ, p.Prime → p ∣ d → p ≤ W) :
    ∃ a b : ℕ, W < a ∧ W < b ∧ d = a * b := by
  have hWd : W < d :=
    lt_of_le_of_lt (Nat.le_pow (a := W) (b := 3) (by norm_num)) hd
  let P : ℕ → Prop := fun a => a ∣ d ∧ W < a
  have hex : ∃ a, P a := ⟨d, dvd_rfl, hWd⟩
  let a := Nat.find hex
  have ha : P a := Nat.find_spec hex
  have ha2 : 2 ≤ a := by omega
  have hanotprime : ¬a.Prime := by
    intro hap
    exact (not_le_of_gt ha.2) (hall a hap ha.1)
  obtain ⟨m, hmdiva, hm2, hma⟩ :=
    Nat.exists_dvd_of_not_prime2 ha2 hanotprime
  have hmdivd : m ∣ d := hmdiva.trans ha.1
  have hmW : m ≤ W := by
    by_contra h
    have hWm : W < m := by omega
    exact (Nat.find_min hex hma) ⟨hmdivd, hWm⟩
  let c := a / m
  have hapos : 0 < a := by omega
  have hc_lt : c < a := by
    dsimp [c]
    exact Nat.div_lt_self hapos (by omega)
  have hac : a = m * c := by
    dsimp [c]
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel hmdiva).symm
  have hcdiva : c ∣ a := by
    exact ⟨m, by simpa [Nat.mul_comm] using hac⟩
  have hcdivd : c ∣ d := hcdiva.trans ha.1
  have hcW : c ≤ W := by
    by_contra h
    have hWc : W < c := by omega
    exact (Nat.find_min hex hc_lt) ⟨hcdivd, hWc⟩
  have haW2 : a ≤ W ^ 2 := by
    rw [hac]
    nlinarith
  let b := d / a
  have hdab : d = a * b := by
    dsimp [b]
    exact (Nat.mul_div_cancel' ha.1).symm
  have hbW : W < b := by
    by_contra h
    have hb_le : b ≤ W := by omega
    rw [hdab] at hd
    nlinarith
  exact ⟨a, b, ha.2, hbW, hdab⟩

/-- If all prime factors are at most `W` and `W²<d≤W³`, then `d`
has two factors at most `W²`. -/
theorem exists_bounded_split_of_primeFactors_le
    {W d : ℕ} (hW : 1 < W) (hdlo : W ^ 2 < d) (hdhi : d ≤ W ^ 3)
    (hall : ∀ p : ℕ, p.Prime → p ∣ d → p ≤ W) :
    ∃ a b : ℕ, d = a * b ∧ a ≤ W ^ 2 ∧ b ≤ W ^ 2 := by
  have hWd : W < d :=
    lt_of_le_of_lt (Nat.le_pow (a := W) (b := 2) (by norm_num)) hdlo
  let P : ℕ → Prop := fun a => a ∣ d ∧ W < a
  have hex : ∃ a, P a := ⟨d, dvd_rfl, hWd⟩
  let a := Nat.find hex
  have ha : P a := Nat.find_spec hex
  have ha2 : 2 ≤ a := by omega
  have hanotprime : ¬a.Prime := by
    intro hap
    exact (not_le_of_gt ha.2) (hall a hap ha.1)
  obtain ⟨m, hmdiva, hm2, hma⟩ :=
    Nat.exists_dvd_of_not_prime2 ha2 hanotprime
  have hmdivd : m ∣ d := hmdiva.trans ha.1
  have hmW : m ≤ W := by
    by_contra h
    exact (Nat.find_min hex hma) ⟨hmdivd, by omega⟩
  let c := a / m
  have hc_lt : c < a := by
    dsimp [c]
    exact Nat.div_lt_self (by omega) (by omega)
  have hac : a = m * c := by
    dsimp [c]
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel hmdiva).symm
  have hcdivd : c ∣ d := by
    apply Nat.dvd_trans (b := a) _ ha.1
    exact ⟨m, by simpa [Nat.mul_comm] using hac⟩
  have hcW : c ≤ W := by
    by_contra h
    exact (Nat.find_min hex hc_lt) ⟨hcdivd, by omega⟩
  have haW2 : a ≤ W ^ 2 := by
    rw [hac]
    nlinarith
  let b := d / a
  have hdab : d = a * b := by
    dsimp [b]
    exact (Nat.mul_div_cancel' ha.1).symm
  have hbW2 : b ≤ W ^ 2 := by
    by_contra h
    have : W ^ 2 < b := by omega
    rw [hdab] at hdhi
    have haW : W < a := ha.2
    nlinarith
  exact ⟨a, b, hdab, haW2, hbW2⟩

/-- Every integer through `N⁶` has either a prime factor above `N⁴` with
cofactor at most `N²`, or a factorization with factors bounded by `N⁴` and
`N³`.  This is the standard encoding lemma for multiplicative Sidon sets. -/
theorem sixthPower_factorization
    {N d : ℕ} (hN : 1 < N) (hdpos : 0 < d) (hd : d ≤ N ^ 6) :
    (∃ p t : ℕ, p.Prime ∧ N ^ 4 < p ∧ d = p * t ∧ t ≤ N ^ 2) ∨
    (∃ u v : ℕ, d = u * v ∧ u ≤ N ^ 4 ∧ v ≤ N ^ 3) := by
  by_cases hlarge : ∃ p : ℕ, p.Prime ∧ N ^ 4 < p ∧ p ∣ d
  · left
    rcases hlarge with ⟨p, hpprime, hpN, hpdiv⟩
    let t := d / p
    have hdpt : d = p * t := by
      dsimp [t]
      exact (Nat.mul_div_cancel' hpdiv).symm
    have ht : t ≤ N ^ 2 := by
      by_contra h
      have ht' : N ^ 2 < t := by omega
      rw [hdpt] at hd
      nlinarith
    exact ⟨p, t, hpprime, hpN, hdpt, ht⟩
  · right
    have hall4 : ∀ p : ℕ, p.Prime → p ∣ d → p ≤ N ^ 4 := by
      intro p hp hpd
      by_contra h
      exact hlarge ⟨p, hp, by omega, hpd⟩
    by_cases hdsmall : d ≤ N ^ 4
    · exact ⟨d, 1, by simp, hdsmall, by
        have : 1 ≤ N := by omega
        exact Nat.one_le_pow _ _ this⟩
    · by_cases hmedium : ∃ p : ℕ, p.Prime ∧ N ^ 2 < p ∧ p ∣ d
      · rcases hmedium with ⟨p, hpprime, hpN2, hpdiv⟩
        let t := d / p
        have hdpt : d = p * t := by
          dsimp [t]
          exact (Nat.mul_div_cancel' hpdiv).symm
        have hpN4 : p ≤ N ^ 4 := hall4 p hpprime hpdiv
        have htN4 : t ≤ N ^ 4 := by
          by_contra h
          have ht' : N ^ 4 < t := by omega
          rw [hdpt] at hd
          nlinarith
        let u := max p t
        let v := min p t
        have huv : d = u * v := by
          dsimp [u, v]
          rcases le_total p t with h | h
          · simpa [max_eq_right h, min_eq_left h, Nat.mul_comm] using hdpt
          · simpa [max_eq_left h, min_eq_right h] using hdpt
        have huN4 : u ≤ N ^ 4 := by
          dsimp [u]
          exact max_le hpN4 htN4
        have hvN3 : v ≤ N ^ 3 := by
          by_contra h
          have hmin_gt : N ^ 3 < min p t := not_le.mp h
          have hpgt : N ^ 3 < p := hmin_gt.trans_le (min_le_left p t)
          have htgt : N ^ 3 < t := hmin_gt.trans_le (min_le_right p t)
          have hN3pos : 0 < N ^ 3 := by positivity
          have hp_pos : 0 < p := hpprime.pos
          have hmul1 : N ^ 3 * N ^ 3 < p * N ^ 3 :=
            Nat.mul_lt_mul_of_pos_right hpgt hN3pos
          have hmul2 : p * N ^ 3 < p * t :=
            Nat.mul_lt_mul_of_pos_left htgt hp_pos
          have hmul : N ^ 6 < p * t := by
            rw [show N ^ 6 = N ^ 3 * N ^ 3 by ring]
            exact hmul1.trans hmul2
          rw [hdpt] at hd
          omega
        exact ⟨u, v, huv, huN4, hvN3⟩
      · have hall2 : ∀ p : ℕ, p.Prime → p ∣ d → p ≤ N ^ 2 := by
          intro p hp hpd
          by_contra h
          exact hmedium ⟨p, hp, by omega, hpd⟩
        have hsplit := exists_bounded_split_of_primeFactors_le
          (W := N ^ 2) (d := d) (by nlinarith)
          (by
            rw [show (N ^ 2) ^ 2 = N ^ 4 by ring]
            exact not_le.mp hdsmall) (by
            rw [show (N ^ 2) ^ 3 = N ^ 6 by ring]
            exact hd) hall2
        rcases hsplit with ⟨u, v, huv, hu, hv⟩
        have hmin : min u v ≤ N ^ 3 := by
          by_contra h
          have hmin_gt : N ^ 3 < min u v := not_le.mp h
          have hu' : N ^ 3 < u := hmin_gt.trans_le (min_le_left u v)
          have hv' : N ^ 3 < v := hmin_gt.trans_le (min_le_right u v)
          have hN3pos : 0 < N ^ 3 := by positivity
          have hu_pos : 0 < u := by omega
          have hmul1 : N ^ 3 * N ^ 3 < u * N ^ 3 :=
            Nat.mul_lt_mul_of_pos_right hu' hN3pos
          have hmul2 : u * N ^ 3 < u * v :=
            Nat.mul_lt_mul_of_pos_left hv' hu_pos
          have hmul : N ^ 6 < u * v := by
            rw [show N ^ 6 = N ^ 3 * N ^ 3 by ring]
            exact hmul1.trans hmul2
          rw [huv] at hd
          omega
        have hu' : u ≤ N ^ 4 := by
          simpa [show (N ^ 2) ^ 2 = N ^ 4 by ring] using hu
        have hv' : v ≤ N ^ 4 := by
          simpa [show (N ^ 2) ^ 2 = N ^ 4 by ring] using hv
        have hprod : d = max u v * min u v := by
          rcases le_total u v with h | h
          · simpa [max_eq_right h, min_eq_left h, Nat.mul_comm] using huv
          · simpa [max_eq_left h, min_eq_right h] using huv
        exact ⟨max u v, min u v, hprod, max_le hu' hv', hmin⟩

/-- Every composite core above `R`, when `W³≤R`, is either genuinely split
into two factors above `W` or lies on a unique-large-prime ray `t·p` with
`t≤W<p`.  Prime cores themselves are included in the second case with `t=1`.
This is the arithmetic classification behind the uniform fiber-tail lemma. -/
theorem core_above_cutoff_split_or_primeRay
    {W R d : ℕ} (hW : 1 < W) (hWR : W ^ 3 ≤ R) (hd : R < d) :
    (∃ a b : ℕ, W < a ∧ W < b ∧ d = a * b) ∨
    (∃ t p : ℕ, 0 < t ∧ t ≤ W ∧ W < p ∧ p.Prime ∧ d = t * p) := by
  by_cases hlarge : ∃ p : ℕ, W < p ∧ p.Prime ∧ p ∣ d
  · rcases hlarge with ⟨p, hpW, hpprime, hpdiv⟩
    rcases hpdiv with ⟨t, rfl⟩
    have htpos : 0 < t := by
      by_contra ht
      have : t = 0 := by omega
      subst t
      simp at hd
    by_cases htW : t ≤ W
    · right
      exact ⟨t, p, htpos, htW, hpW, hpprime, by simp [Nat.mul_comm]⟩
    · left
      exact ⟨p, t, hpW, by omega, rfl⟩
  · left
    apply exists_large_split_of_primeFactors_le hW (lt_of_le_of_lt hWR hd)
    intro p hpprime hpdiv
    by_contra hp
    exact hlarge ⟨p, by omega, hpprime, hpdiv⟩

end Erdos796
