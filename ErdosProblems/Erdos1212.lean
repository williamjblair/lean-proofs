/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
# Erdős Problem #1212 — the certified structural core

https://www.erdosproblems.com/1212

The problem: in the graph on `{(x,y) : gcd(x,y) = 1}` with edges joining points
differing by `±1` in exactly one coordinate, is there a path to infinity all of
whose vertices satisfy `min(x,y) > 1` and have at least one coordinate
composite?

This file formalizes *unconditional* structural results established in the
2026-07-30/31 campaign. **The problem itself remains open**: that campaign
reduced a YES answer to a single unproved statement (an arithmetic
staircase-exclusion lemma), and nothing here claims otherwise.

What is formalized:

* `row_odd_of_horizontal_step` — the move-parity law: horizontal steps need odd
  rows.
* `blocked_of_prime_dvd` — the exact blocking criterion for a hub step.
* `deadRow_three` — rows divisible by 3 admit no horizontal hub step.
* `elevator_shaft`, `elevator_shaft_adjacent` — a composite column of large
  least prime factor carries an admissible vertical shaft (Lemma A).
* `palette_wall`, `palette_wall_of_composite` — the composite-palette wall: for
  any finite palette of composite rows bounded by `Y`, infinitely many columns
  block *every* row of the palette simultaneously, with modulus depending only
  on `√Y`. This is the obstruction that rules out low-band architectures.
* `semiprime_block_sparsity` — the block-event cap: a row with two prime factors
  `≥ Z` has at most six blocked columns per window of `Z` columns.
* `pow_card_le_of_primes_gt` — the counting core of pointwise tameness: an
  integer has few prime factors above a given threshold.

Informal author: Claude (Anthropic), with adversarial refereeing by GPT Pro.
Formal author: Claude (Anthropic).
-/
import Mathlib

set_option linter.style.longLine false

namespace Erdos1212

/-! ## The graph -/

/-- `n` is composite. -/
def Composite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

/-- Edges of the ambient visible-lattice graph: two lattice points are adjacent
when they differ by one in exactly one coordinate. -/
def Adj (u v : ℕ × ℕ) : Prop :=
  (u.2 = v.2 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1)) ∨
  (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2))

/-- The admissible vertices: coprime coordinates, both exceeding 1, at least one
composite. -/
def Admissible (v : ℕ × ℕ) : Prop :=
  Nat.Coprime v.1 v.2 ∧ 1 < v.1 ∧ 1 < v.2 ∧ (Composite v.1 ∨ Composite v.2)

/-- A hub step `(a,b) → (a+2,b)` is open exactly when `b` is coprime to
`a(a+1)(a+2)`: the two-step move through the intermediate vertex. -/
def HubOpenRight (a b : ℕ) : Prop := Nat.Coprime b (a * (a + 1) * (a + 2))

/-! ## Move parity -/

/-- A horizontal step requires an odd row: if `(x,y)` and `(x+1,y)` are both
coprime pairs then `y` is odd. -/
theorem row_odd_of_horizontal_step {x y : ℕ}
    (h1 : Nat.Coprime x y) (h2 : Nat.Coprime (x + 1) y) : Odd y := by
  rcases Nat.even_or_odd y with he | ho
  · exfalso
    have hy2 : 2 ∣ y := he.two_dvd
    have hx2 : ¬ (2 ∣ x) := by
      intro hd
      have hg : (2 : ℕ) ∣ Nat.gcd x y := Nat.dvd_gcd hd hy2
      rw [Nat.Coprime] at h1
      rw [h1] at hg
      omega
    have hx1 : (2 : ℕ) ∣ (x + 1) := by omega
    have hg : (2 : ℕ) ∣ Nat.gcd (x + 1) y := Nat.dvd_gcd hx1 hy2
    rw [Nat.Coprime] at h2
    rw [h2] at hg
    omega
  · exact ho

/-! ## The blocking criterion -/

/-- If a prime divides the row and one of the three swept columns, the hub step
is blocked. -/
theorem blocked_of_prime_dvd {a b p : ℕ} (hp : p.Prime)
    (hpb : p ∣ b) (hpa : p ∣ a * (a + 1) * (a + 2)) : ¬ HubOpenRight a b := by
  intro h
  have hd : p ∣ Nat.gcd b (a * (a + 1) * (a + 2)) := Nat.dvd_gcd hpb hpa
  rw [HubOpenRight, Nat.Coprime] at h
  rw [h] at hd
  have h1 := Nat.le_of_dvd one_pos hd
  have h2 := hp.two_le
  omega

/-- Rows divisible by 3 admit no horizontal hub step: one of `a`, `a+1`, `a+2`
is always divisible by 3. -/
theorem deadRow_three {a b : ℕ} (hb : 3 ∣ b) : ¬ HubOpenRight a b := by
  have h3 : (3 : ℕ) ∣ a * (a + 1) * (a + 2) := by
    have h : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases h with h | h | h
    · have hd : (3 : ℕ) ∣ a := by omega
      exact (hd.mul_right (a + 1)).mul_right (a + 2)
    · have hd : (3 : ℕ) ∣ (a + 2) := by omega
      exact hd.mul_left (a * (a + 1))
    · have hd : (3 : ℕ) ∣ (a + 1) := by omega
      exact (hd.mul_left a).mul_right (a + 2)
  exact blocked_of_prime_dvd (by norm_num) hb h3

/-! ## Elevator shafts -/

/-- Everything below the least prime factor is coprime to `a`. -/
theorem coprime_of_lt_minFac {a s : ℕ} (hs : 0 < s) (hlt : s < a.minFac) :
    Nat.Coprime a s := by
  by_contra hc
  obtain ⟨p, hp, hpa, hps⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have h1 : a.minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le hpa
  have h2 : p ≤ s := Nat.le_of_dvd hs hps
  omega

/-- **Elevator shaft (Lemma A).** Every vertex `(a, s)` with `a` composite and
`2 ≤ s < p⁻(a)` is admissible. -/
theorem elevator_shaft {a s : ℕ} (ha : Composite a) (hs : 2 ≤ s)
    (hlt : s < a.minFac) : Admissible (a, s) :=
  ⟨coprime_of_lt_minFac (by omega) hlt, ha.1, by omega, Or.inl ha⟩

/-- Consecutive shaft vertices are adjacent, so the shaft is a path in the
admissible subgraph. -/
theorem elevator_shaft_adjacent {a s : ℕ} (ha : Composite a) (hs : 2 ≤ s)
    (hlt : s + 1 < a.minFac) :
    Admissible (a, s) ∧ Admissible (a, s + 1) ∧ Adj (a, s) (a, s + 1) :=
  ⟨elevator_shaft ha hs (by omega), elevator_shaft ha (by omega) hlt,
    Or.inr ⟨rfl, Or.inl rfl⟩⟩

/-! ## The composite-palette wall

A single column congruence blocks an entire palette of composite rows at once,
because every composite `r` has a prime factor at most `√r`. This is the
obstruction ruling out architectures whose rows are confined to a low band. -/

/-- Every composite number has a prime factor whose square is at most itself. -/
theorem exists_prime_factor_sq_le {r : ℕ} (hr : Composite r) :
    ∃ p, p.Prime ∧ p ∣ r ∧ p * p ≤ r := by
  have hr1 : 1 < r := hr.1
  refine ⟨r.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd r, ?_⟩
  have h := Nat.minFac_sq_le_self (by omega : 0 < r) hr.2
  rw [pow_two] at h
  exact h

/-- The wall column `2Y - 1`: it is odd, exceeds `N` whenever `N < Y`, and its
sweep `a(a+1)(a+2)` is divisible by every divisor of `Y`. -/
theorem wall_column {Y N : ℕ} (hY : N + 1 ≤ Y) :
    N < 2 * Y - 1 ∧ Odd (2 * Y - 1) ∧
      ∀ p : ℕ, p ∣ Y →
        p ∣ (2 * Y - 1) * ((2 * Y - 1) + 1) * ((2 * Y - 1) + 2) := by
  refine ⟨by omega, ⟨Y - 1, by omega⟩, ?_⟩
  intro p hp
  have hsucc : 2 * Y - 1 + 1 = 2 * Y := by omega
  have hpA : p ∣ (2 * Y - 1 + 1) := by rw [hsucc]; exact hp.mul_left 2
  exact (hpA.mul_left (2 * Y - 1)).mul_right (2 * Y - 1 + 2)

/-- **Palette wall.** If every row of a finite set `S` has a prime factor at most
`T`, then beyond every bound there is an odd column at which the horizontal hub
step is blocked on *every* row of `S` simultaneously. -/
theorem palette_wall (S : Finset ℕ) (T N : ℕ)
    (hS : ∀ r ∈ S, ∃ p, p.Prime ∧ p ∣ r ∧ p ≤ T) :
    ∃ a, N < a ∧ Odd a ∧ ∀ r ∈ S, ¬ HubOpenRight a r := by
  have hMpos : 0 < Nat.factorial T := Nat.factorial_pos T
  have hYge : N + 1 ≤ (N + 1) * Nat.factorial T :=
    Nat.le_mul_of_pos_right _ hMpos
  obtain ⟨h1, h2, h3⟩ := wall_column hYge
  refine ⟨2 * ((N + 1) * Nat.factorial T) - 1, h1, h2, ?_⟩
  intro r hr
  obtain ⟨p, hp, hpr, hpT⟩ := hS r hr
  exact blocked_of_prime_dvd hp hpr
    (h3 p ((Nat.dvd_factorial hp.pos hpT).mul_left (N + 1)))

/-- **Palette wall for bounded composite rows.** A finite palette of composite
rows bounded by `Y` is blocked simultaneously at infinitely many columns, using
only the primes up to `√Y`. -/
theorem palette_wall_of_composite (S : Finset ℕ) (Y N : ℕ)
    (hS : ∀ r ∈ S, Composite r ∧ r ≤ Y) :
    ∃ a, N < a ∧ Odd a ∧ ∀ r ∈ S, ¬ HubOpenRight a r := by
  refine palette_wall S (Nat.sqrt Y) N ?_
  intro r hr
  obtain ⟨hc, hrY⟩ := hS r hr
  obtain ⟨p, hp, hpr, hpp⟩ := exists_prime_factor_sq_le hc
  exact ⟨p, hp, hpr, Nat.le_sqrt.mpr (le_trans hpp hrY)⟩

/-! ## Block-event sparsity for rows with two large prime factors -/

/-- A window of at most `p` consecutive integers contains at most one solution of
`p ∣ a + j`. -/
theorem card_dvd_window_le_one {p A Z j : ℕ} (hZ : Z ≤ p) :
    ((Finset.Ico A (A + Z)).filter (fun a => p ∣ a + j)).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_Ico] at hx hy
  obtain ⟨⟨hx1, hx2⟩, u, hu⟩ := hx
  obtain ⟨⟨hy1, hy2⟩, v, hv⟩ := hy
  rcases Nat.lt_trichotomy u v with h | h | h
  · exfalso
    have h1 : u + 1 ≤ v := h
    have h2 : p * u + p ≤ p * v := by nlinarith
    omega
  · subst h; omega
  · exfalso
    have h1 : v + 1 ≤ u := h
    have h2 : p * v + p ≤ p * u := by nlinarith
    omega

/-- **Block-event cap.** A row `p * q` whose two prime factors are both at least
`Z` has at most six blocked columns in any window of `Z` consecutive columns. -/
theorem semiprime_block_sparsity {p q Z A : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpZ : Z ≤ p) (hqZ : Z ≤ q) :
    ((Finset.Ico A (A + Z)).filter
      (fun a => ¬ Nat.Coprime (p * q) (a * (a + 1) * (a + 2)))).card ≤ 6 := by
  classical
  set W := Finset.Ico A (A + Z) with hW
  have hcover : W.filter (fun a => ¬ Nat.Coprime (p * q) (a * (a + 1) * (a + 2))) ⊆
      (W.filter (fun a => p ∣ a + 0)) ∪ (W.filter (fun a => p ∣ a + 1)) ∪
      (W.filter (fun a => p ∣ a + 2)) ∪ (W.filter (fun a => q ∣ a + 0)) ∪
      (W.filter (fun a => q ∣ a + 1)) ∪ (W.filter (fun a => q ∣ a + 2)) := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨haW, hablk⟩ := ha
    obtain ⟨t, ht, htpq, htsweep⟩ := Nat.Prime.not_coprime_iff_dvd.mp hablk
    have hsweep : t ∣ a ∨ t ∣ a + 1 ∨ t ∣ a + 2 := by
      rcases (Nat.Prime.dvd_mul ht).mp htsweep with h | h
      · rcases (Nat.Prime.dvd_mul ht).mp h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h)
    have htcases : t = p ∨ t = q := by
      rcases (Nat.Prime.dvd_mul ht).mp htpq with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq ht hp).mp h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq ht hq).mp h)
    simp only [Finset.mem_union, Finset.mem_filter, Nat.add_zero]
    rcases htcases with rfl | rfl <;> rcases hsweep with h | h | h <;> tauto
  have key : ∀ (s t : Finset ℕ) (m n : ℕ), s.card ≤ m → t.card ≤ n →
      (s ∪ t).card ≤ m + n :=
    fun s t m n hs ht => le_trans (Finset.card_union_le s t) (Nat.add_le_add hs ht)
  have b0 := card_dvd_window_le_one (p := p) (A := A) (Z := Z) (j := 0) hpZ
  have b1 := card_dvd_window_le_one (p := p) (A := A) (Z := Z) (j := 1) hpZ
  have b2 := card_dvd_window_le_one (p := p) (A := A) (Z := Z) (j := 2) hpZ
  have b3 := card_dvd_window_le_one (p := q) (A := A) (Z := Z) (j := 0) hqZ
  have b4 := card_dvd_window_le_one (p := q) (A := A) (Z := Z) (j := 1) hqZ
  have b5 := card_dvd_window_le_one (p := q) (A := A) (Z := Z) (j := 2) hqZ
  refine le_trans (Finset.card_le_card hcover) ?_
  exact key _ _ 5 1 (key _ _ 4 1 (key _ _ 3 1 (key _ _ 2 1 (key _ _ 1 1 b0 b1) b2) b3) b4) b5

/-! ## The counting core of pointwise tameness

An integer cannot have many prime factors above a threshold, since their product
divides it. This is the elementary fact underlying the pointwise tameness bound
that made the multiscale climbing lemma unconditional. -/

/-- If `S` is a finite set of primes, each exceeding `R` and each dividing
`m > 0`, then `R ^ |S| ≤ m`. -/
theorem pow_card_le_of_primes_gt {m R : ℕ} (hm : 0 < m) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hgt : ∀ p ∈ S, R < p) (hdvd : ∀ p ∈ S, p ∣ m) :
    R ^ S.card ≤ m := by
  classical
  have hprod : (∏ p ∈ S, p) ∣ m :=
    Finset.prod_primes_dvd m (fun p hp => (hprime p hp).prime) hdvd
  have hle : R ^ S.card ≤ ∏ p ∈ S, p := by
    calc R ^ S.card = ∏ _p ∈ S, R := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' (fun p hp => le_of_lt (hgt p hp))
  exact le_trans hle (Nat.le_of_dvd hm hprod)

end Erdos1212
