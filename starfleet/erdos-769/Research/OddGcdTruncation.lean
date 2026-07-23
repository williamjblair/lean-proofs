import Mathlib

/-!
# The collective regular-grid gcd is one in large odd dimensions

This develops an elementary interval-of-roots argument, independent of the
BCZ estimate for the first two generators.
-/

namespace Erdos769

/-- Four disjoint blocks of explicitly constructible smooth roots. -/
inductive SmoothRootIndex (M : ℕ)
  | one : Fin M → SmoothRootIndex M
  | two : Fin (M - M / 2) → SmoothRootIndex M
  | three : Fin (M - (2 * M) / 3) → SmoothRootIndex M
  | four : Fin ((M - 2) - (3 * M) / 4) → SmoothRootIndex M
  deriving Fintype, DecidableEq

/-- The positive integer represented by a smooth-root index. -/
def SmoothRootIndex.val {M : ℕ} : SmoothRootIndex M → ℕ
  | .one i => i + 1
  | .two i => 2 * (M / 2 + 1 + i)
  | .three i => 3 * ((2 * M) / 3 + 1 + i)
  | .four i => 4 * ((3 * M) / 4 + 1 + i)

lemma SmoothRootIndex.val_injective {M : ℕ} :
    Function.Injective (@SmoothRootIndex.val M) := by
  intro x y h
  cases x <;> cases y <;>
    simp [SmoothRootIndex.val] at h ⊢ <;> omega

def SmoothRootIndex.equivSum (M : ℕ) :
    SmoothRootIndex M ≃
      Fin M ⊕ Fin (M - M / 2) ⊕ Fin (M - (2 * M) / 3) ⊕
        Fin ((M - 2) - (3 * M) / 4) where
  toFun
    | .one i => Sum.inl i
    | .two i => Sum.inr (Sum.inl i)
    | .three i => Sum.inr (Sum.inr (Sum.inl i))
    | .four i => Sum.inr (Sum.inr (Sum.inr i))
  invFun
    | Sum.inl i => .one i
    | Sum.inr (Sum.inl i) => .two i
    | Sum.inr (Sum.inr (Sum.inl i)) => .three i
    | Sum.inr (Sum.inr (Sum.inr i)) => .four i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with x | ⟨x | ⟨x | x⟩⟩ <;> rfl

lemma SmoothRootIndex.card (M : ℕ) :
    Fintype.card (SmoothRootIndex M) =
      M + (M - M / 2) + (M - (2 * M) / 3) +
        ((M - 2) - (3 * M) / 4) := by
  rw [Fintype.card_congr (SmoothRootIndex.equivSum M)]
  simp
  omega

/-- The four blocks contain more than `n` indices when
`M=(n+3)/2`, for odd `n≥15`. -/
lemma SmoothRootIndex.card_gt {n : ℕ} (hn : 15 ≤ n) (hnodd : Odd n) :
    n < Fintype.card (SmoothRootIndex ((n + 3) / 2)) := by
  rw [SmoothRootIndex.card]
  obtain ⟨q, hq⟩ := hnodd
  omega

/-- Every represented value is positive. -/
lemma SmoothRootIndex.val_pos {M : ℕ} (hM : 1 ≤ M)
    (i : SmoothRootIndex M) : 0 < i.val := by
  cases i <;> simp [SmoothRootIndex.val] <;> omega

/-- For odd `n`, all represented values are at most `2n`, and hence are
strictly below any prime of the form `q*n+1` with `q≥2`. -/
lemma SmoothRootIndex.val_le_two_mul {n : ℕ} (hn : 15 ≤ n) (hnodd : Odd n)
    (i : SmoothRootIndex ((n + 3) / 2)) : i.val ≤ 2 * n := by
  obtain ⟨q, hq⟩ := hnodd
  cases i <;> simp [SmoothRootIndex.val] <;> omega

/-- Every represented integer is a product of two positive integers at most
`M`. -/
lemma SmoothRootIndex.exists_factors {M : ℕ} (hM : 4 ≤ M)
    (i : SmoothRootIndex M) :
    ∃ a b : ℕ, 1 ≤ a ∧ a ≤ M ∧ 1 ≤ b ∧ b ≤ M ∧ i.val = a * b := by
  cases i with
  | one i =>
      refine ⟨1, i + 1, by omega, by omega, by omega, ?_, by simp [SmoothRootIndex.val]⟩
      omega
  | two i =>
      refine ⟨2, M / 2 + 1 + i, by omega, by omega, by omega, ?_, rfl⟩
      omega
  | three i =>
      refine ⟨3, (2 * M) / 3 + 1 + i, by omega, by omega, by omega, ?_, rfl⟩
      omega
  | four i =>
      refine ⟨4, (3 * M) / 4 + 1 + i, by omega, by omega, by omega, ?_, rfl⟩
      omega

/-- If every integer in `[1,M]` is an `n`-th root modulo `p`, then so is every
integer represented by `SmoothRootIndex M`. -/
lemma SmoothRootIndex.cast_pow_eq_one {M n p : ℕ} (hM : 4 ≤ M)
    (hall : ∀ j : ℕ, 1 ≤ j → j ≤ M → (j : ZMod p) ^ n = 1)
    (i : SmoothRootIndex M) :
    (i.val : ZMod p) ^ n = 1 := by
  obtain ⟨a, b, ha1, haM, hb1, hbM, hab⟩ := i.exists_factors hM
  rw [hab, Nat.cast_mul, mul_pow, hall a ha1 haM, hall b hb1 hbM, one_mul]

/-- Turn each explicit smooth root into an element of the kernel of the power
map on `(ZMod p)ˣ`. -/
noncomputable def SmoothRootIndex.toPowerKernel {M n p : ℕ}
    (hp : p.Prime) (hval : ∀ i : SmoothRootIndex M, i.val < p)
    (hM : 4 ≤ M)
    (hall : ∀ j : ℕ, 1 ≤ j → j ≤ M → (j : ZMod p) ^ n = 1)
    (i : SmoothRootIndex M) :
    (powMonoidHom n : (ZMod p)ˣ →* (ZMod p)ˣ).ker := by
  have hi0 : i.val ≠ 0 := Nat.ne_of_gt (i.val_pos (by omega))
  have hcop : i.val.Coprime p :=
    (Nat.coprime_of_lt_prime hi0 (hval i) hp).symm
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime i.val hcop
  refine ⟨u, (MonoidHom.mem_ker).2 ?_⟩
  rw [powMonoidHom_apply]
  apply Units.ext
  simpa [u, ZMod.coe_unitOfCoprime] using i.cast_pow_eq_one hM hall

@[simp] lemma SmoothRootIndex.coe_toPowerKernel {M n p : ℕ}
    (hp : p.Prime) (hval : ∀ i : SmoothRootIndex M, i.val < p)
    (hM : 4 ≤ M)
    (hall : ∀ j : ℕ, 1 ≤ j → j ≤ M → (j : ZMod p) ^ n = 1)
    (i : SmoothRootIndex M) :
    (((i.toPowerKernel hp hval hM hall :
      (powMonoidHom n : (ZMod p)ˣ →* (ZMod p)ˣ).ker) : (ZMod p)ˣ) : ZMod p) =
      (i.val : ZMod p) := by
  simp [SmoothRootIndex.toPowerKernel, ZMod.coe_unitOfCoprime]

/-- Package any coprime natural root modulo `p` as a unit in the power
kernel. -/
noncomputable def natRootToPowerKernel {n p t : ℕ}
    (hcop : t.Coprime p) (hroot : (t : ZMod p) ^ n = 1) :
    (powMonoidHom n : (ZMod p)ˣ →* (ZMod p)ˣ).ker := by
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime t hcop
  refine ⟨u, (MonoidHom.mem_ker).2 ?_⟩
  rw [powMonoidHom_apply]
  apply Units.ext
  simpa [u, ZMod.coe_unitOfCoprime] using hroot

@[simp] lemma coe_natRootToPowerKernel {n p t : ℕ}
    (hcop : t.Coprime p) (hroot : (t : ZMod p) ^ n = 1) :
    (((natRootToPowerKernel hcop hroot :
      (powMonoidHom n : (ZMod p)ˣ →* (ZMod p)ˣ).ker) : (ZMod p)ˣ) : ZMod p) =
      (t : ZMod p) := by
  simp [natRootToPowerKernel, ZMod.coe_unitOfCoprime]

/-- More than `n` explicit smooth roots contradict the cyclic-group root
count once all represented integers are below `p`. -/
theorem not_all_small_integers_are_roots_of_large_prime
    {n p : ℕ} (hn : 15 ≤ n) (hnodd : Odd n) (hp : p.Prime)
    (hpbig : 2 * n < p)
    (hall : ∀ j : ℕ, 1 ≤ j → j ≤ (n + 3) / 2 →
      (j : ZMod p) ^ n = 1) : False := by
  let M := (n + 3) / 2
  have hM : 4 ≤ M := by dsimp [M]; omega
  have hval : ∀ i : SmoothRootIndex M, i.val < p := by
    intro i
    exact lt_of_le_of_lt (i.val_le_two_mul hn hnodd) hpbig
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  let f : SmoothRootIndex M →
      (powMonoidHom n : (ZMod p)ˣ →* (ZMod p)ˣ).ker :=
    fun i => i.toPowerKernel hp hval hM hall
  have hf : Function.Injective f := by
    intro i j hij
    have hz : (i.val : ZMod p) = (j.val : ZMod p) := by
      have := congrArg (fun z => (((z :
        (powMonoidHom n : (ZMod p)ˣ →* (ZMod p)ˣ).ker) : (ZMod p)ˣ) : ZMod p)) hij
      simpa [f] using this
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (hval i), ZMod.val_natCast_of_lt (hval j)] at hv
    exact SmoothRootIndex.val_injective hv
  have hcardle := Fintype.card_le_of_injective f hf
  have hker : Fintype.card
      (powMonoidHom n : (ZMod p)ˣ →* (ZMod p)ˣ).ker ≤ n := by
    rw [← Nat.card_eq_fintype_card]
    rw [IsCyclic.card_powMonoidHom_ker]
    exact Nat.gcd_le_right (Nat.card (ZMod p)ˣ) (by omega)
  have hgt : n < Fintype.card (SmoothRootIndex M) := by
    simpa [M] using SmoothRootIndex.card_gt hn hnodd
  omega

/-- In a sufficiently large odd dimension, no prime can make all integers up
to `(n+3)/2` into `n`-th roots. This is the key gcd-one truncation lemma. -/
theorem no_prime_divides_all_truncated_regular_increments
    {n p : ℕ} (hn : 15 ≤ n) (hnodd : Odd n) (hp : p.Prime)
    (hall : ∀ j : ℕ, 1 ≤ j → j ≤ (n + 3) / 2 →
      (j : ZMod p) ^ n = 1) : False := by
  let M := (n + 3) / 2
  letI : Fact p.Prime := ⟨hp⟩
  have hMpos : 0 < M := by dsimp [M]; omega
  have hpM : M < p := by
    by_contra h
    have hp_le : p ≤ M := by omega
    have hroot := hall p hp.pos hp_le
    have hn0 : n ≠ 0 := by omega
    have hz : (0 : ZMod p) = 1 := by simpa [hn0] using hroot
    exact zero_ne_one hz
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  let f : Fin M → (powMonoidHom n : (ZMod p)ˣ →* (ZMod p)ˣ).ker := fun i => by
    let t : ℕ := i + 1
    have ht0 : t ≠ 0 := by dsimp [t]; omega
    have htM : t ≤ M := by dsimp [t]; omega
    have htp : t < p := lt_of_le_of_lt htM hpM
    have hcop : t.Coprime p := (Nat.coprime_of_lt_prime ht0 htp hp).symm
    exact natRootToPowerKernel hcop (hall t (by dsimp [t]; omega) htM)
  have hf : Function.Injective f := by
    intro i j hij
    have hz : ((i + 1 : ℕ) : ZMod p) = ((j + 1 : ℕ) : ZMod p) := by
      have := congrArg (fun z => (((z :
        (powMonoidHom n : (ZMod p)ˣ →* (ZMod p)ˣ).ker) : (ZMod p)ˣ) : ZMod p)) hij
      simpa [f] using this
    have hv := congrArg ZMod.val hz
    have hip : i.val + 1 < p := lt_of_le_of_lt (by omega) hpM
    have hjp : j.val + 1 < p := lt_of_le_of_lt (by omega) hpM
    rw [ZMod.val_natCast_of_lt hip, ZMod.val_natCast_of_lt hjp] at hv
    apply Fin.ext
    omega
  have hMker : M ≤ Fintype.card
      (powMonoidHom n : (ZMod p)ˣ →* (ZMod p)ˣ).ker := by
    simpa using Fintype.card_le_of_injective f hf
  have hkerEq : Fintype.card
      (powMonoidHom n : (ZMod p)ˣ →* (ZMod p)ˣ).ker = (p - 1).gcd n := by
    rw [← Nat.card_eq_fintype_card, IsCyclic.card_powMonoidHom_ker]
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hMg : M ≤ (p - 1).gcd n := by
    rw [← hkerEq]
    exact hMker
  have hgpos : 0 < (p - 1).gcd n := lt_of_lt_of_le hMpos hMg
  have hgle : (p - 1).gcd n ≤ n := Nat.gcd_le_right (p - 1) (by omega)
  have hgeq : (p - 1).gcd n = n := by
    by_contra hne
    have hglt : (p - 1).gcd n < n := lt_of_le_of_ne hgle hne
    obtain ⟨q, hq⟩ := Nat.gcd_dvd_right (p - 1) n
    have hqgt : 1 < q := by
      by_contra hqnot
      have hqcases : q = 0 ∨ q = 1 := by omega
      rcases hqcases with rfl | rfl
      · simp at hq
        omega
      · simp at hq
        omega
    have hqodd : Odd q := by
      have hprod : Odd ((p - 1).gcd n * q) := hq ▸ hnodd
      exact Nat.Odd.of_mul_right hprod
    obtain ⟨r, hr⟩ := hqodd
    have hq3 : 3 ≤ q := by omega
    have h3g : 3 * (p - 1).gcd n ≤ n := by
      calc
        3 * (p - 1).gcd n = (p - 1).gcd n * 3 := by omega
        _ ≤ (p - 1).gcd n * q := Nat.mul_le_mul_left ((p - 1).gcd n) hq3
        _ = n := hq.symm
    dsimp [M] at hMg
    omega
  have hndvd : n ∣ p - 1 := by
    rw [← hgeq]
    exact Nat.gcd_dvd_left (p - 1) n
  obtain ⟨q, hq⟩ := hndvd
  have hpform : p = n * q + 1 := by omega
  have hq2 : 2 ≤ q := by
    by_contra hqnot
    have hqcases : q = 0 ∨ q = 1 := by omega
    rcases hqcases with rfl | rfl
    · simp at hpform
      omega
    · simp at hpform
      have hpeven : Even p := by
        obtain ⟨r, hr⟩ := hnodd
        refine ⟨r + 1, ?_⟩
        omega
      have hp2 : p = 2 := (hp.even_iff).1 hpeven
      omega
  have hpbig : 2 * n < p := by rw [hpform]; nlinarith
  exact not_all_small_integers_are_roots_of_large_prime hn hnodd hp hpbig hall

/-- The regular-grid increments with bases from `2` through `(n+3)/2` have
collective gcd one in every odd dimension `n≥15`. -/
theorem truncated_regular_increment_gcd_eq_one
    {n : ℕ} (hn : 15 ≤ n) (hnodd : Odd n) :
    (Finset.Icc 2 ((n + 3) / 2)).gcd (fun j => j ^ n - 1) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  apply no_prime_divides_all_truncated_regular_increments hn hnodd hp
  intro j hj1 hjM
  by_cases hjone : j = 1
  · subst j
    simp
  have hj2 : 2 ≤ j := by omega
  have hpinc : p ∣ j ^ n - 1 :=
    (Finset.dvd_gcd_iff.mp hpdvd) j (Finset.mem_Icc.mpr ⟨hj2, hjM⟩)
  obtain ⟨q, hq⟩ := hpinc
  have hjpow : 0 < j ^ n := pow_pos (by omega) n
  have heq : j ^ n = 1 + p * q := by omega
  have heqcast := congrArg (fun x : ℕ => (x : ZMod p)) heq
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_pow] at heqcast
  simpa using heqcast

end Erdos769
