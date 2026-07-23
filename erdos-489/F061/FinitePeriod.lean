import Mathlib

/-- Positive integers avoiding every modulus in a finite set. -/
def finSieved (s : Finset ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ a ∈ s, ¬a ∣ n

/-- Divisibility avoidance by a finite set is periodic away from the positivity
condition, with an explicit period equal to the product of the moduli. -/
theorem periodic_avoidDivisors (s : Finset ℕ) :
    Function.Periodic (fun n : ℕ => ∀ a ∈ s, ¬a ∣ n) (s.prod id) := by
  intro n
  apply propext
  constructor
  · intro h a ha han
    apply h a ha
    have hap : a ∣ (s.prod id : ℕ) := Finset.dvd_prod_of_mem id ha
    exact (Nat.dvd_add_iff_left hap).1 han
  · intro h a ha hans
    apply h a ha
    have hap : a ∣ (s.prod id : ℕ) := Finset.dvd_prod_of_mem id ha
    exact (Nat.dvd_add_iff_left hap).2 hans

/-- On positive inputs, the finite sifted predicate itself repeats after the
product period. -/
theorem finSieved_add_prod_iff (s : Finset ℕ) (n : ℕ) (hn : 0 < n) :
    finSieved s (n + s.prod id) ↔ finSieved s n := by
  rw [finSieved, finSieved]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hn, (periodic_avoidDivisors s n).mp h⟩
  · rintro ⟨_, h⟩
    exact ⟨Nat.add_pos_left hn _, (periodic_avoidDivisors s n).mpr h⟩
