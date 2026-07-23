import Research.Basic

namespace Erdos796

/-- Three distinct valid factor pairs for one product contradict the `< 3`
representation condition.  This packages the basic finite-cardinality
obstruction used throughout the problem. -/
theorem three_rep_obstruction
    (A : Finset ℕ) (m a b c d e f : ℕ)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (he : e ∈ A) (hf : f ∈ A)
    (hab : a < b) (hcd : c < d) (hef : e < f)
    (habm : a * b = m) (hcdm : c * d = m) (hefm : e * f = m)
    (hcard : ({(a, b), (c, d), (e, f)} : Finset (ℕ × ℕ)).card = 3) :
    ¬ HasRepBound 3 A := by
  intro hA
  let R := (A ×ˢ A).filter fun x => x.1 < x.2 ∧ x.1 * x.2 = m
  have hsub : ({(a, b), (c, d), (e, f)} : Finset (ℕ × ℕ)) ⊆ R := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · simp [R, ha, hb, hab, habm]
    · simp [R, hc, hd, hcd, hcdm]
    · simp [R, he, hf, hef, hefm]
  have hle := Finset.card_le_card hsub
  have hthree : 3 ≤ repCount A m := by
    simpa [R, repCount, hcard] using hle
  exact (Nat.not_lt_of_ge hthree) (hA m)

/-- If `1 < p < q < r < pq`, an admissible set cannot simultaneously contain
`p,q,r` and the three pairwise products.  Indeed `p(qr)=q(pr)=r(pq)` gives
three distinct representations. -/
theorem multiplicative_triangle_obstruction
    (A : Finset ℕ) (p q r : ℕ)
    (hp : 1 < p) (hpq : p < q) (hqr : q < r) (hrpq : r < p * q)
    (hP : p ∈ A) (hQ : q ∈ A) (hR : r ∈ A)
    (hPQ : p * q ∈ A) (hPR : p * r ∈ A) (hQR : q * r ∈ A) :
    ¬ HasRepBound 3 A := by
  have hp_qr : p < q * r := by nlinarith
  have hq_pr : q < p * r := by nlinarith
  have h12 : (p, q * r) ≠ (q, p * r) := by
    intro h
    exact hpq.ne (congrArg Prod.fst h)
  have h13 : (p, q * r) ≠ (r, p * q) := by
    intro h
    exact (hpq.trans hqr).ne (congrArg Prod.fst h)
  have h23 : (q, p * r) ≠ (r, p * q) := by
    intro h
    exact hqr.ne (congrArg Prod.fst h)
  have hcard :
      ({(p, q * r), (q, p * r), (r, p * q)} : Finset (ℕ × ℕ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13])]
    rw [Finset.card_insert_of_notMem (by simp [h23])]
    simp
  apply three_rep_obstruction A (p * q * r)
      p (q * r) q (p * r) r (p * q)
      hP hQR hQ hPR hR hPQ hp_qr hq_pr hrpq
  · simp [Nat.mul_assoc]
  · simp [Nat.mul_comm, Nat.mul_left_comm]
  · simp [Nat.mul_comm, Nat.mul_left_comm]
  · exact hcard

/-- The same triangle obstruction without choosing which of `r` and `pq` is
smaller.  Equality is the only degenerate case because diagonal products are
not counted by the problem. -/
theorem multiplicative_triangle_obstruction_of_ne
    (A : Finset ℕ) (p q r : ℕ)
    (hp : 1 < p) (hpq : p < q) (hqr : q < r) (hne : r ≠ p * q)
    (hP : p ∈ A) (hQ : q ∈ A) (hR : r ∈ A)
    (hPQ : p * q ∈ A) (hPR : p * r ∈ A) (hQR : q * r ∈ A) :
    ¬ HasRepBound 3 A := by
  rcases lt_or_gt_of_ne hne with hrpq | hpqr
  · exact multiplicative_triangle_obstruction A p q r hp hpq hqr hrpq
      hP hQ hR hPQ hPR hQR
  · have hp_qr : p < q * r := by nlinarith
    have hq_pr : q < p * r := by nlinarith
    have hp_pq : p < p * q := by nlinarith
    have hq_pq : q < p * q := by nlinarith
    have h12 : (p, q * r) ≠ (q, p * r) := by
      intro h
      exact hpq.ne (congrArg Prod.fst h)
    have h13 : (p, q * r) ≠ (p * q, r) := by
      intro h
      exact hp_pq.ne (congrArg Prod.fst h)
    have h23 : (q, p * r) ≠ (p * q, r) := by
      intro h
      exact hq_pq.ne (congrArg Prod.fst h)
    have hcard :
        ({(p, q * r), (q, p * r), (p * q, r)} : Finset (ℕ × ℕ)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13])]
      rw [Finset.card_insert_of_notMem (by simp [h23])]
      simp
    apply three_rep_obstruction A (p * q * r)
        p (q * r) q (p * r) (p * q) r
        hP hQR hQ hPR hPQ hR hp_qr hq_pr hpqr
    · simp [Nat.mul_assoc]
    · simp [Nat.mul_comm, Nat.mul_left_comm]
    · simp [Nat.mul_assoc]
    · exact hcard

/-- For three increasing primes the exceptional equality `r = pq` is
impossible, so retaining the primes and all three semiprimes violates the
representation bound. -/
theorem prime_semiprime_triangle_obstruction
    (A : Finset ℕ) (p q r : ℕ)
    (hPprime : p.Prime) (hQprime : q.Prime) (hRprime : r.Prime)
    (hpq : p < q) (hqr : q < r)
    (hP : p ∈ A) (hQ : q ∈ A) (hR : r ∈ A)
    (hPQ : p * q ∈ A) (hPR : p * r ∈ A) (hQR : q * r ∈ A) :
    ¬ HasRepBound 3 A := by
  have hne : r ≠ p * q := by
    intro heq
    have hdvd : r ∣ p * q := by rw [← heq]
    rcases hRprime.dvd_mul.mp hdvd with hrp | hrq
    · have := Nat.le_of_dvd hPprime.pos hrp
      omega
    · have := Nat.le_of_dvd hQprime.pos hrq
      omega
  exact multiplicative_triangle_obstruction_of_ne A p q r hPprime.one_lt hpq hqr hne
    hP hQ hR hPQ hPR hQR

end Erdos796
