import Mathlib

/-!
# An explicit numerical-semigroup conductor extension

This is the elementary induction step behind Brauer's gcd-chain conductor
bound.  It is stated for an arbitrary additive submonoid of `ℕ` so it can be
reused independently of the cubical geometry.
-/

namespace Erdos769

/-- If an additive submonoid contains `a` and has a representative at most
`R` for every residue modulo `a`, it contains every integer at least `R`. -/
theorem AddSubmonoid.all_ge_of_bounded_complete_residues
    (S : AddSubmonoid ℕ) {a R : ℕ} (ha0 : 0 < a) (ha : a ∈ S)
    (hres : ∀ r < a, ∃ w, w ≤ R ∧ w ∈ S ∧ w % a = r) :
    ∀ N, R ≤ N → N ∈ S := by
  intro N hRN
  obtain ⟨w, hwR, hwS, hwmod⟩ := hres (N % a) (Nat.mod_lt N ha0)
  have hwN : w ≤ N := le_trans hwR hRN
  have hwmodeq : w ≡ N % a [MOD a] := by
    change w % a = (N % a) % a
    rw [Nat.mod_eq_of_lt (Nat.mod_lt N ha0)]
    exact hwmod
  have hmodeq : w ≡ N [MOD a] := hwmodeq.trans (Nat.mod_modEq N a)
  obtain ⟨q, hq⟩ := (Nat.modEq_iff_exists_eq_add hwN).1 hmodeq
  rw [hq]
  exact S.add_mem hwS (by simpa [mul_comm] using S.nsmul_mem ha q)

/-- Suppose an additive submonoid contains `a`, and contains every sufficiently
large multiple `d*q` of `d`.  If `a` and `d` are coprime, adjoining `a`
fills every integer beyond the displayed explicit threshold. -/
theorem AddSubmonoid.all_ge_of_coprime_and_large_multiples
    (S : AddSubmonoid ℕ) {a d C : ℕ}
    (hd : 0 < d) (hcop : a.Coprime d) (ha : a ∈ S)
    (hlarge : ∀ q, C ≤ q → d * q ∈ S) :
    ∀ N, d * C + (d - 1) * a ≤ N → N ∈ S := by
  intro N hN
  obtain ⟨t, htd, htmod⟩ :=
    Nat.exists_mul_mod_eq_of_coprime N hcop (Nat.ne_of_gt hd)
  have hta_bound : a * t ≤ (d - 1) * a := by
    have ht : t ≤ d - 1 := by omega
    nlinarith [Nat.mul_le_mul_left a ht]
  have htaN : a * t ≤ N := by omega
  have hmodeq : a * t ≡ N [MOD d] := htmod
  obtain ⟨q, hqeq⟩ := (Nat.modEq_iff_exists_eq_add htaN).1 hmodeq
  have hdc_le : d * C ≤ d * q := by omega
  have hCq : C ≤ q := Nat.le_of_mul_le_mul_left hdc_le hd
  have hmul : d * q ∈ S := hlarge q hCq
  have hat : a * t ∈ S := by
    simpa [mul_comm] using S.nsmul_mem ha t
  rw [hqeq]
  exact S.add_mem hat hmul

/-- Scale every member of an additive submonoid by `r`, then adjoin a new
generator `b`. -/
def scaledExtend (S : AddSubmonoid ℕ) (r b : ℕ) : AddSubmonoid ℕ :=
  S.map (nsmulAddMonoidHom r) ⊔ AddSubmonoid.closure ({b} : Set ℕ)

lemma mul_mem_scaledExtend {S : AddSubmonoid ℕ} {r b q : ℕ}
    (hq : q ∈ S) : r * q ∈ scaledExtend S r b := by
  apply (show S.map (nsmulAddMonoidHom r) ≤ scaledExtend S r b from le_sup_left)
  refine ⟨q, hq, ?_⟩
  simp [Nat.nsmul_eq_mul]

lemma generator_mem_scaledExtend (S : AddSubmonoid ℕ) (r b : ℕ) :
    b ∈ scaledExtend S r b := by
  apply (show AddSubmonoid.closure ({b} : Set ℕ) ≤ scaledExtend S r b from le_sup_right)
  exact AddSubmonoid.subset_closure (by simp)

/-- A normalized gcd-chain is represented abstractly as successive pairs
`(r,b)`, where `r` is the gcd ratio and `b` the newly normalized generator. -/
def conductorChainMonoid : List (ℕ × ℕ) → AddSubmonoid ℕ
  | [] => ⊤
  | (r, b) :: tail => scaledExtend (conductorChainMonoid tail) r b

/-- The explicit conductor obtained by iterating the coprime extension step. -/
def conductorChainBound : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (r, b) :: tail =>
      r * conductorChainBound tail + (r - 1) * b

/-- Iterated Brauer conductor mechanism: if every ratio `r` is positive and
coprime to its normalized new generator `b`, every integer beyond the
recursive chain bound lies in the resulting additive submonoid. -/
theorem conductorChainMonoid_all_ge
    (steps : List (ℕ × ℕ))
    (hsteps : ∀ rb ∈ steps, 0 < rb.1 ∧ rb.2.Coprime rb.1) :
    ∀ N, conductorChainBound steps ≤ N → N ∈ conductorChainMonoid steps := by
  induction steps with
  | nil =>
      intro N hN
      simp [conductorChainMonoid]
  | cons rb tail ih =>
      rcases rb with ⟨r, b⟩
      have hrb : 0 < r ∧ b.Coprime r := hsteps (r, b) (by simp)
      have htail : ∀ rb ∈ tail, 0 < rb.1 ∧ rb.2.Coprime rb.1 := by
        intro rb hrbmem
        exact hsteps rb (by simp [hrbmem])
      have ih' := ih htail
      intro N hN
      refine AddSubmonoid.all_ge_of_coprime_and_large_multiples
        (scaledExtend (conductorChainMonoid tail) r b)
        (a := b) (d := r) (C := conductorChainBound tail)
        hrb.1 hrb.2 (generator_mem_scaledExtend _ _ _) ?_ N ?_
      · intro q hq
        exact mul_mem_scaledExtend (ih' q hq)
      · simpa [conductorChainBound] using hN

end Erdos769
