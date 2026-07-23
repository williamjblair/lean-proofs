import Mathlib

namespace Erdos254.TailModularCoverage

noncomputable section

def residueFiber (A : Set ℕ) (q r : ℕ) : Set ℕ :=
  {n | n ∈ A ∧ n % q = r}

def recurringResidues (A : Set ℕ) (q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range q).filter (fun r => (residueFiber A q r).Infinite)

lemma mem_recurringResidues_iff (A : Set ℕ) (q r : ℕ) :
    r ∈ recurringResidues A q ↔ r < q ∧ (residueFiber A q r).Infinite := by
  classical
  simp [recurringResidues]

lemma nonmultiples_infinite (A : Set ℕ)
    (htail : ∀ d : ℕ, 2 ≤ d → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ n ∈ A ∧ ¬ d ∣ n)
    (d : ℕ) (hd : 2 ≤ d) :
    {n : ℕ | n ∈ A ∧ ¬ d ∣ n}.Infinite := by
  intro hfinite
  obtain ⟨M, hM⟩ := hfinite.exists_le
  obtain ⟨n, hnM, hnA, hnd⟩ := htail d hd (M + 1)
  have hnle : n ≤ M := hM n ⟨hnA, hnd⟩
  omega

/-- The residue classes occurring infinitely often in `A` generate the full
cyclic group modulo `q`, expressed as a gcd-one statement. -/
theorem gcd_recurringResidues_eq_one (A : Set ℕ)
    (htail : ∀ d : ℕ, 2 ≤ d → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ n ∈ A ∧ ¬ d ∣ n)
    (q : ℕ) (hq : 2 ≤ q) :
    Nat.gcd q ((recurringResidues A q).gcd id) = 1 := by
  let R := recurringResidues A q
  let g := Nat.gcd q (R.gcd id)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  change g = 1
  by_contra hgne
  have hg2 : 2 ≤ g := by omega
  have hE : {n : ℕ | n ∈ A ∧ ¬ g ∣ n}.Infinite :=
    nonmultiples_infinite A htail g hg2
  let E : Set ℕ := {n : ℕ | n ∈ A ∧ ¬ g ∣ n}
  let f : E → Fin q := fun n =>
    ⟨n.1 % q, Nat.mod_lt _ (lt_of_lt_of_le Nat.zero_lt_two hq)⟩
  letI : Infinite E := hE.to_subtype
  obtain ⟨r, hr⟩ := Finite.exists_infinite_fiber f
  let P : Set E := f ⁻¹' {r}
  let emb : P → residueFiber A q r.val := fun n => by
    refine ⟨n.1.1, n.1.2.1, ?_⟩
    have hmem := n.2
    change f n.1 ∈ ({r} : Set (Fin q)) at hmem
    have hfr : f n.1 = r := Set.mem_singleton_iff.mp hmem
    exact congrArg Fin.val hfr
  have hemb : Function.Injective emb := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : residueFiber A q r.val => x.1) hab
  letI : Infinite P := hr
  haveI : Infinite (residueFiber A q r.val) := Infinite.of_injective emb hemb
  have hrInf : (residueFiber A q r.val).Infinite := Set.infinite_coe_iff.mp inferInstance
  have hrR : r.val ∈ R := by
    rw [show R = recurringResidues A q by rfl, mem_recurringResidues_iff]
    exact ⟨r.isLt, hrInf⟩
  have hgq : g ∣ q := Nat.gcd_dvd_left _ _
  have hgr : g ∣ r.val :=
    (Nat.gcd_dvd_right q (R.gcd id)).trans (Finset.gcd_dvd hrR)
  let a : P := Classical.arbitrary P
  have haE : a.1.1 ∈ A ∧ ¬ g ∣ a.1.1 := a.1.2
  have hmem := a.2
  change f a.1 ∈ ({r} : Set (Fin q)) at hmem
  have hfa : f a.1 = r := Set.mem_singleton_iff.mp hmem
  have hmod : a.1.1 % q = r.val := congrArg Fin.val hfa
  have hgn : g ∣ a.1.1 := by
    rw [← Nat.dvd_mod_iff hgq, hmod]
    exact hgr
  exact haE.2 hgn

end


private theorem finset_gcd_linear_combination (s : Finset ℕ) :
    ∃ c : ℕ → ℤ, ((s.gcd (fun x => x) : ℕ) : ℤ) =
      ∑ x ∈ s, c x * (x : ℤ) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨c, hc⟩ := ih
      let sg : ℕ := s.gcd (fun x => x)
      let ca := Nat.gcdA a sg
      let cb := Nat.gcdB a sg
      refine ⟨fun x => if x = a then ca else c x * cb, ?_⟩
      rw [Finset.gcd_insert, Finset.sum_insert ha]
      have hsum :
          ∑ x ∈ s, (if x = a then ca else c x * cb) * (x : ℤ) =
            (∑ x ∈ s, c x * (x : ℤ)) * cb := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        rw [if_neg (by exact fun hxa => ha (hxa ▸ hx))]
        ring_nf
      rw [hsum, ← hc]
      simp only
      change ((Nat.gcd a sg : ℕ) : ℤ) = ca * (a : ℤ) + (sg : ℤ) * cb
      rw [Nat.gcd_eq_gcd_ab]
      simp only [ca, cb]
      ring_nf

/-- A gcd-one set of natural residues linearly generates one in `ZMod q`. -/
theorem zmod_one_linear_combination (R : Finset ℕ) (q : ℕ)
    (h : Nat.gcd q (R.gcd id) = 1) :
    ∃ z : ℕ → ℤ, (1 : ZMod q) =
      ∑ r ∈ R, (z r : ZMod q) * (r : ZMod q) := by
  classical
  obtain ⟨c, hc⟩ := finset_gcd_linear_combination R
  let rg : ℕ := R.gcd (fun r => r)
  let b : ℤ := Nat.gcdB q rg
  refine ⟨fun r => c r * b, ?_⟩
  have hab := Nat.gcd_eq_gcd_ab q rg
  have hrg : rg = R.gcd id := rfl
  rw [hrg, h] at hab
  have habz := congrArg (fun x : ℤ => (x : ZMod q)) hab
  norm_num at habz
  rw [habz]
  have hcz := congrArg (fun x : ℤ => (x : ZMod q)) hc
  norm_num at hcz
  change ((R.gcd (fun x => x) : ℕ) : ZMod q) *
    ((b : ℤ) : ZMod q) = ∑ r ∈ R, ((c r * b : ℤ) : ZMod q) * (r : ZMod q)
  rw [hcz]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [b]
  push_cast
  ring

/-- With `q` labeled copies of each gcd-one residue, ordinary subset selection
can realize every target residue. -/
theorem zmod_target_as_bounded_repetitions (R : Finset ℕ) (q : ℕ) (hq : 2 ≤ q)
    (h : Nat.gcd q (R.gcd id) = 1) (t : ZMod q) :
    ∃ T : (r : {r // r ∈ R}) → Finset (Fin q),
      t = ∑ r, ∑ _k ∈ T r, (r.1 : ZMod q) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  obtain ⟨z, hz⟩ := zmod_one_linear_combination R q h
  let coeff : {r // r ∈ R} → ℕ := fun r => (t * (z r.1 : ZMod q)).val
  let T : (r : {r // r ∈ R}) → Finset (Fin q) := fun r =>
    Finset.univ.filter (fun k => k.val < coeff r)
  refine ⟨T, ?_⟩
  have hcard : ∀ r, (T r).card = coeff r := by
    intro r
    change (Finset.univ.filter (fun k : Fin q => k.val < coeff r)).card = coeff r
    rw [Fin.card_filter_val_lt]
    exact Nat.min_eq_right (ZMod.val_lt _).le
  calc
    t = t * (1 : ZMod q) := by ring
    _ = t * (∑ r ∈ R, (z r : ZMod q) * (r : ZMod q)) := by rw [← hz]
    _ = ∑ r ∈ R, (t * (z r : ZMod q)) * (r : ZMod q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ∑ r : {r // r ∈ R}, (coeff r : ZMod q) * (r.1 : ZMod q) := by
      rw [Finset.sum_subtype (p := fun r => r ∈ R) (s := R) (by simp)]
      apply Finset.sum_congr rfl
      intro r hr
      rw [show (coeff r : ZMod q) = t * (z r.1 : ZMod q) by
        exact ZMod.natCast_zmod_val _]
    _ = ∑ r, ∑ _k ∈ T r, (r.1 : ZMod q) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.sum_const, hcard, nsmul_eq_mul]


/-- Every residue modulo `q` is a subset sum of arbitrarily far-out distinct
members of `A`. -/
theorem tail_subset_sums_cover_zmod (A : Set ℕ)
    (htail : ∀ d : ℕ, 2 ≤ d → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ n ∈ A ∧ ¬ d ∣ n)
    (q : ℕ) (hq : 2 ≤ q) (N : ℕ) (t : ZMod q) :
    ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ A ∧ N ≤ n) ∧
      (∑ n ∈ s, (n : ZMod q)) = t := by
  classical
  letI : NeZero q := ⟨by omega⟩
  let R := recurringResidues A q
  have hgen : Nat.gcd q (R.gcd id) = 1 :=
    gcd_recurringResidues_eq_one A htail q hq
  let tailFiber (r : {r // r ∈ R}) : Set ℕ :=
    {n | n ∈ residueFiber A q r.1 ∧ N ≤ n}
  have htailFiber : ∀ r : {r // r ∈ R}, (tailFiber r).Infinite := by
    intro r
    have hrInf : (residueFiber A q r.1).Infinite :=
      (mem_recurringResidues_iff A q r.1).mp r.2 |>.2
    have hd := hrInf.sdiff (Set.finite_Iio N)
    have heq : residueFiber A q r.1 \ Set.Iio N = tailFiber r := by
      ext n
      simp only [Set.mem_sdiff, Set.mem_Iio, tailFiber, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hn, hN⟩
        exact ⟨hn, Nat.le_of_not_gt hN⟩
      · rintro ⟨hn, hN⟩
        exact ⟨hn, Nat.not_lt_of_ge hN⟩
    rw [← heq]
    exact hd
  have hex : ∀ r : {r // r ∈ R}, ∃ W : Finset ℕ,
      (W : Set ℕ) ⊆ tailFiber r ∧ W.card = q := by
    intro r
    exact (htailFiber r).exists_subset_card_eq q
  choose W hWsub hWcard using hex
  let e : (r : {r // r ∈ R}) → Fin q → ℕ := fun r k =>
    ((W r).orderIsoOfFin (hWcard r) k).1
  have he_mem : ∀ r k, e r k ∈ W r := by
    intro r k
    exact ((W r).orderIsoOfFin (hWcard r) k).2
  have he_tail : ∀ r k, e r k ∈ residueFiber A q r.1 ∧ N ≤ e r k := by
    intro r k
    exact hWsub r (he_mem r k)
  have he_inj : ∀ r, Function.Injective (e r) := by
    intro r k l hkl
    apply (W r).orderIsoOfFin (hWcard r) |>.injective
    apply Subtype.ext
    exact hkl
  obtain ⟨T, hT⟩ := zmod_target_as_bounded_repetitions R q hq hgen t
  let U : {r // r ∈ R} → Finset ℕ := fun r => (T r).image (e r)
  have hU_tail : ∀ r n, n ∈ U r →
      n ∈ residueFiber A q r.1 ∧ N ≤ n := by
    intro r n hn
    change n ∈ (T r).image (e r) at hn
    rw [Finset.mem_image] at hn
    obtain ⟨k, hk, rfl⟩ := hn
    exact he_tail r k
  have hdisj : (↑(Finset.univ : Finset {r // r ∈ R}) : Set {r // r ∈ R}).PairwiseDisjoint U := by
    intro r hr r' hr' hne
    change Disjoint (U r) (U r')
    rw [Finset.disjoint_left]
    intro n hn hn'
    have hnmod := (hU_tail r n hn).1.2
    have hnmod' := (hU_tail r' n hn').1.2
    have hv : r.1 = r'.1 := hnmod.symm.trans hnmod'
    exact hne (Subtype.ext hv)
  have hsumU : ∀ r : {r // r ∈ R},
      (∑ n ∈ U r, (n : ZMod q)) =
        ∑ _k ∈ T r, (r.1 : ZMod q) := by
    intro r
    change (∑ n ∈ (T r).image (e r), (n : ZMod q)) =
      ∑ _k ∈ T r, (r.1 : ZMod q)
    rw [Finset.sum_image (he_inj r).injOn]
    apply Finset.sum_congr rfl
    intro k hk
    have hkmod := (he_tail r k).1.2
    rw [← ZMod.natCast_mod (e r k) q, hkmod]
  let s : Finset ℕ := Finset.univ.biUnion U
  refine ⟨s, ?_, ?_⟩
  · intro n hn
    change n ∈ Finset.univ.biUnion U at hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨r, hr, hnr⟩ := hn
    exact ⟨(hU_tail r n hnr).1.1, (hU_tail r n hnr).2⟩
  · change (∑ n ∈ Finset.univ.biUnion U, (n : ZMod q)) = t
    rw [Finset.sum_biUnion hdisj]
    calc
      (∑ r ∈ (Finset.univ : Finset {r // r ∈ R}),
          ∑ n ∈ U r, (n : ZMod q)) =
          ∑ r, ∑ _k ∈ T r, (r.1 : ZMod q) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hsumU r
      _ = t := hT.symm

end Erdos254.TailModularCoverage
