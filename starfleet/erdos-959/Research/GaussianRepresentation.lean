import Mathlib.NumberTheory.SumTwoSquares
import Research.BinaryFactor
import Research.RepresentationCount

open Zsqrtd
open scoped ComplexConjugate

namespace Erdos959

lemma gaussian_prime_of_norm_prime {z : GaussianInt} {p : ℕ}
    (hp : p.Prime) (hn : z.norm.natAbs = p) : Prime z := by
  rw [← irreducible_iff_prime, irreducible_iff]
  constructor
  · intro hu
    have hnorm1 : z.norm.natAbs = 1 := norm_eq_one_iff.mpr hu
    rw [hn] at hnorm1
    exact hp.ne_one hnorm1
  · intro a b hab
    have hmul : a.norm.natAbs * b.norm.natAbs = p := by
      rw [← hn, hab, Zsqrtd.norm_mul, Int.natAbs_mul]
    rcases hp.eq_one_or_self_of_dvd a.norm.natAbs ⟨b.norm.natAbs, hmul.symm⟩ with ha1 | hap
    · exact Or.inl (norm_eq_one_iff.mp ha1)
    · right
      apply norm_eq_one_iff.mp
      rw [hap] at hmul
      exact Nat.eq_of_mul_eq_mul_left hp.pos (by simpa using hmul)

lemma gaussian_norm_nat_mk (a b : ℤ) :
    (Zsqrtd.norm (⟨a, b⟩ : GaussianInt)).natAbs =
      a.natAbs ^ 2 + b.natAbs ^ 2 := by
  simpa [pow_two] using GaussianInt.natAbs_norm_eq (⟨a, b⟩ : GaussianInt)

lemma gaussian_norm_nat_dvd_of_dvd {z w : GaussianInt} (h : z ∣ w) :
    z.norm.natAbs ∣ w.norm.natAbs := by
  rcases h with ⟨q, rfl⟩
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  exact dvd_mul_right _ _

lemma gaussian_prime_norm_dvd_prime_norm_eq
    {z w : GaussianInt} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hz : z.norm.natAbs = p) (hw : w.norm.natAbs = q)
    (hd : z ∣ w) : p = q := by
  have hpq : p ∣ q := by
    rw [← hz, ← hw]
    exact gaussian_norm_nat_dvd_of_dvd hd
  rcases (Nat.dvd_prime hq).mp hpq with hp1 | hpqeq
  · exact False.elim (hp.ne_one hp1)
  · exact hpqeq

lemma gaussian_norm_nat_star (z : GaussianInt) :
    (star z).norm.natAbs = z.norm.natAbs := by
  rw [Zsqrtd.norm_conj]

lemma gaussian_mk_nat_norm {a b p : ℕ} (h : a ^ 2 + b ^ 2 = p) :
    (Zsqrtd.norm (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)).natAbs = p := by
  rw [gaussian_norm_nat_mk]
  simp only [Int.natAbs_natCast]
  exact h

lemma gaussian_mk_nat_not_dvd_conj
    {a b p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hsum : a ^ 2 + b ^ 2 = p) :
    ¬(⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∣
      star (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) := by
  let z : GaussianInt := ⟨(a : ℤ), (b : ℤ)⟩
  intro hd
  have hzsum : z ∣ z + star z := dvd_add (dvd_refl z) hd
  have hnormz : z.norm.natAbs = p := gaussian_mk_nat_norm hsum
  have hnormsum : (z + star z).norm.natAbs = 4 * a ^ 2 := by
    dsimp [z]
    simp only [Zsqrtd.norm]
    simp
    have hcast :
        ((((↑a + ↑a) * (↑a + ↑a) : ℤ).natAbs : ℕ) : ℤ) =
          ((4 * a ^ 2 : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg (by positivity)]
      push_cast
      ring
    exact_mod_cast hcast
  have hpdiv : p ∣ 4 * a ^ 2 := by
    rw [← hnormz, ← hnormsum]
    exact gaussian_norm_nat_dvd_of_dvd hzsum
  rcases (Nat.Prime.dvd_mul hp).mp hpdiv with hp4 | hpa2
  · have hpPow : p ∣ 2 ^ 2 := by simpa [pow_two] using hp4
    have hpTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpPow
    rcases (Nat.dvd_prime Nat.prime_two).mp hpTwo with hp1 | hpEq
    · exact hp.ne_one hp1
    · exact hp2 hpEq
  · have hpa : p ∣ a := hp.dvd_of_dvd_pow hpa2
    have hple : p ≤ a := Nat.le_of_dvd ha hpa
    nlinarith

abbrev gaussianCoords (z : GaussianInt) : IntPoint := (z.re, z.im)

lemma gaussianCoords_injective : Function.Injective gaussianCoords := by
  intro z w h
  exact Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

abbrev coordsGaussian (v : IntPoint) : GaussianInt := ⟨v.1, v.2⟩

lemma coordsGaussian_injective : Function.Injective coordsGaussian := by
  intro v w h
  apply Prod.ext
  · exact congrArg Zsqrtd.re h
  · exact congrArg Zsqrtd.im h

lemma coords_gaussian_roundtrip (z : GaussianInt) : coordsGaussian (gaussianCoords z) = z := by
  exact Zsqrtd.ext rfl rfl

lemma int_finset_card_le_two_of_sq_constant
    (s : Finset ℤ) (h : ∀ a ∈ s, ∀ b ∈ s, a ^ 2 = b ^ 2) :
    s.card ≤ 2 := by
  by_cases hs : s.Nonempty
  · obtain ⟨b, hb⟩ := hs
    have hsub : s ⊆ {b, -b} := by
      intro a ha
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp (h a ha b hb)) with hab | hab
      · simp [hab]
      · simp [hab]
    calc
      s.card ≤ ({b, -b} : Finset ℤ).card := Finset.card_le_card hsub
      _ ≤ 2 := by
        have hc := Finset.card_insert_le b ({-b} : Finset ℤ)
        simpa using hc
  · simp only [Finset.not_nonempty_iff_eq_empty] at hs
    simp [hs]

lemma intPoint_fiber_card_le_two
    (s : Finset IntPoint) (a t : ℤ)
    (hfirst : ∀ v ∈ s, v.1 = a)
    (hnorm : ∀ v ∈ s, intNormSq v = t) :
    s.card ≤ 2 := by
  have hinj : Set.InjOn Prod.snd (s : Set IntPoint) := by
    intro v hv w hw heq
    apply Prod.ext
    · rw [hfirst v hv, hfirst w hw]
    · exact heq
  rw [← Finset.card_image_iff.mpr hinj]
  apply int_finset_card_le_two_of_sq_constant
  intro b hb c hc
  rcases Finset.mem_image.mp hb with ⟨v, hv, rfl⟩
  rcases Finset.mem_image.mp hc with ⟨w, hw, rfl⟩
  have hvn := hnorm v hv
  have hwn := hnorm w hw
  dsimp [intNormSq] at hvn hwn
  rw [hfirst v hv] at hvn
  rw [hfirst w hw] at hwn
  nlinarith

/-- Elementary circle-point bound: fixing the absolute first coordinate has at
most four sign choices, and that coordinate ranges only up to `sqrt n`. -/
lemma representationVectors_card_le_sqrt (n : ℕ) (hn : 1 ≤ n) :
    (representationVectors n).card ≤ 4 * (n.sqrt + 1) := by
  let V := representationVectors n
  let f : IntPoint → ℕ := fun v => v.1.natAbs
  have hfiber : ∀ r ∈ V.image f, (V.filter fun v => f v = r).card ≤ 4 := by
    intro r hr
    let F := V.filter fun v => f v = r
    have hEach : ∀ a ∈ F.image Prod.fst,
        (F.filter fun v => v.1 = a).card ≤ 2 := by
      intro a ha
      apply intPoint_fiber_card_le_two _ a n
      · intro v hv
        exact (Finset.mem_filter.mp hv).2
      · intro v hv
        have hvV := (Finset.mem_filter.mp hv).1
        exact (mem_representationVectors_iff hn v).mp
          (Finset.mem_filter.mp hvV).1
    have hF : F.card ≤ 2 * (F.image Prod.fst).card :=
      Finset.card_le_mul_card_image F 2 hEach
    have hImageSq : ∀ a ∈ F.image Prod.fst, ∀ b ∈ F.image Prod.fst,
        a ^ 2 = b ^ 2 := by
      intro a ha b hb
      rcases Finset.mem_image.mp ha with ⟨v, hv, rfl⟩
      rcases Finset.mem_image.mp hb with ⟨w, hw, rfl⟩
      have hvr := (Finset.mem_filter.mp hv).2
      have hwr := (Finset.mem_filter.mp hw).2
      dsimp [f] at hvr hwr
      have hs : v.1.natAbs ^ 2 = w.1.natAbs ^ 2 := by rw [hvr, hwr]
      calc
        v.1 ^ 2 = ((v.1.natAbs : ℤ) ^ 2) := (Int.natAbs_sq v.1).symm
        _ = ((w.1.natAbs : ℤ) ^ 2) := by exact_mod_cast hs
        _ = w.1 ^ 2 := Int.natAbs_sq w.1
    have hImage : (F.image Prod.fst).card ≤ 2 :=
      int_finset_card_le_two_of_sq_constant _ hImageSq
    change F.card ≤ 4
    calc
      F.card ≤ 2 * (F.image Prod.fst).card := hF
      _ ≤ 2 * 2 := Nat.mul_le_mul_left 2 hImage
      _ = 4 := by norm_num
  have hV : V.card ≤ 4 * (V.image f).card :=
    Finset.card_le_mul_card_image V 4 hfiber
  have hmap : V.image f ⊆ Finset.range (n.sqrt + 1) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨v, hv, rfl⟩
    have hvn := (mem_representationVectors_iff hn v).mp hv
    have hxInt : v.1 ^ 2 ≤ (n : ℤ) := by
      dsimp [intNormSq] at hvn
      nlinarith [sq_nonneg v.2]
    have hxNat : v.1.natAbs ^ 2 ≤ n := by
      have hxCast : ((v.1.natAbs ^ 2 : ℕ) : ℤ) ≤ (n : ℤ) := by
        simpa [Int.natAbs_sq] using hxInt
      exact_mod_cast hxCast
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.le_sqrt'.mpr hxNat
  have hImageCard : (V.image f).card ≤ n.sqrt + 1 := by
    simpa using Finset.card_le_card hmap
  exact hV.trans (Nat.mul_le_mul_left 4 hImageCard)

lemma representationVectors_card_sq_le (n : ℕ) (hn : 1 ≤ n) :
    (representationVectors n).card ^ 2 ≤ 64 * n := by
  have hsqrt : 1 ≤ n.sqrt := Nat.le_sqrt'.mpr (by simpa using hn)
  have hcard0 := representationVectors_card_le_sqrt n hn
  have hcard : (representationVectors n).card ≤ 8 * n.sqrt := by
    apply hcard0.trans
    nlinarith
  calc
    (representationVectors n).card ^ 2 ≤ (8 * n.sqrt) ^ 2 :=
      Nat.pow_le_pow_left hcard 2
    _ = 64 * n.sqrt ^ 2 := by ring
    _ ≤ 64 * n := Nat.mul_le_mul_left 64 (Nat.sqrt_le' n)

/-- Gaussian integers of norm `n`, represented by the already finite coordinate set. -/
noncomputable def gaussianRepresentations (n : ℕ) : Finset GaussianInt :=
  (representationVectors n).image coordsGaussian

lemma card_gaussianRepresentations (n : ℕ) :
    (gaussianRepresentations n).card = (representationVectors n).card := by
  exact Finset.card_image_of_injective _ coordsGaussian_injective

lemma mem_gaussianRepresentations_iff {n : ℕ} (hn : 1 ≤ n) (z : GaussianInt) :
    z ∈ gaussianRepresentations n ↔ z.norm.natAbs = n := by
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
    have hi := (mem_representationVectors_iff hn v).mp hv
    have hnorm : (Zsqrtd.norm (coordsGaussian v)) = (n : ℤ) := by
      dsimp [intNormSq, coordsGaussian] at hi
      simpa [Zsqrtd.norm, pow_two] using hi
    rw [hnorm]
    simp
  · intro hz
    apply Finset.mem_image.mpr
    refine ⟨gaussianCoords z, ?_, coords_gaussian_roundtrip z⟩
    apply (mem_representationVectors_iff hn _).mpr
    have hzInt : z.norm = (n : ℤ) := by
      rw [← GaussianInt.abs_natCast_norm z]
      exact_mod_cast hz
    dsimp [intNormSq, gaussianCoords]
    rw [← hzInt]
    simp [Zsqrtd.norm, pow_two]

lemma gaussian_mul_conj_eq_natCast {w : GaussianInt} {n : ℕ}
    (hn : w.norm.natAbs = n) :
    w * star w = (n : GaussianInt) := by
  have hnormInt : w.norm = (n : ℤ) := by
    rw [← GaussianInt.abs_natCast_norm w]
    exact_mod_cast hn
  rw [← Zsqrtd.norm_eq_mul_conj]
  exact_mod_cast hnormInt

/-- Strip one chosen Gaussian factor above a rational prime from an element
whose norm is divisible by that prime. -/
lemma gaussian_strip_split_prime
    {z w : GaussianInt} {p n : ℕ}
    (hp : p.Prime) (hz : z.norm.natAbs = p)
    (hw : w.norm.natAbs = p * n) :
    ∃ q : GaussianInt,
      (w = z * q ∨ w = star z * q) ∧ q.norm.natAbs = n := by
  have hzPrime : Prime z := gaussian_prime_of_norm_prime hp hz
  have hzScalar : z * star z = (p : GaussianInt) :=
    gaussian_mul_conj_eq_natCast hz
  have hwScalar : w * star w = (p * n : GaussianInt) := by
    simpa using gaussian_mul_conj_eq_natCast hw
  have hzDiv : z ∣ w * star w := by
    rw [hwScalar]
    refine ⟨star z * (n : GaussianInt), ?_⟩
    rw [← mul_assoc, hzScalar]
  rcases (Prime.dvd_mul hzPrime).mp hzDiv with hzw | hzsw
  · rcases hzw with ⟨q, hq⟩
    refine ⟨q, Or.inl hq, ?_⟩
    have hmul : p * q.norm.natAbs = p * n := by
      have hw' := hw
      rw [hq, Zsqrtd.norm_mul, Int.natAbs_mul, hz] at hw'
      exact hw'
    exact Nat.eq_of_mul_eq_mul_left hp.pos hmul
  · rcases hzsw with ⟨q, hq⟩
    let q' := star q
    have hwq : w = star z * q' := by
      have hs := congrArg star hq
      simpa [q'] using hs
    refine ⟨q', Or.inr hwq, ?_⟩
    dsimp [q']
    rw [gaussian_norm_nat_star]
    have hmul : p * q.norm.natAbs = p * n := by
      have hw' := hw
      rw [← gaussian_norm_nat_star w, hq, Zsqrtd.norm_mul,
        Int.natAbs_mul, hz] at hw'
      exact hw'
    exact Nat.eq_of_mul_eq_mul_left hp.pos hmul

/-- Iteratively strip one Gaussian factor above every split rational prime. -/
lemma gaussian_strip_split_family
    {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (p : ι → ℕ) (z : ι → GaussianInt)
    (hp : ∀ i ∈ U, (p i).Prime)
    (hnorm : ∀ i ∈ U, (z i).norm.natAbs = p i)
    (A : ℕ) {w : GaussianInt}
    (hw : w.norm.natAbs = A * ∏ i ∈ U, p i) :
    ∃ q : GaussianInt, ∃ S ∈ U.powerset,
      q.norm.natAbs = A ∧
        w = q * binaryFactorProduct U S z (fun i => star (z i)) := by
  induction U using Finset.induction_on generalizing w with
  | empty =>
      refine ⟨w, ∅, by simp, ?_, ?_⟩
      · simpa using hw
      · simp [binaryFactorProduct]
  | @insert i U hi ih =>
      have hpi : (p i).Prime := hp i (Finset.mem_insert_self i U)
      have hzi : (z i).norm.natAbs = p i :=
        hnorm i (Finset.mem_insert_self i U)
      have hpU : ∀ j ∈ U, (p j).Prime := by
        intro j hj
        exact hp j (Finset.mem_insert_of_mem hj)
      have hzU : ∀ j ∈ U, (z j).norm.natAbs = p j := by
        intro j hj
        exact hnorm j (Finset.mem_insert_of_mem hj)
      have hw' : w.norm.natAbs = p i * (A * ∏ j ∈ U, p j) := by
        rw [hw, Finset.prod_insert hi]
        ring
      obtain ⟨q, hchoice, hqnorm⟩ :=
        gaussian_strip_split_prime hpi hzi hw'
      obtain ⟨u, S, hSpow, huNorm, hq⟩ := ih hpU hzU hqnorm
      have hSsub : S ⊆ U := Finset.mem_powerset.mp hSpow
      have hiS : i ∉ S := fun hiMem => hi (hSsub hiMem)
      rcases hchoice with hleft | hright
      · refine ⟨u, insert i S, ?_, huNorm, ?_⟩
        · exact Finset.mem_powerset.mpr (by
            intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hjS
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (hSsub hjS))
        · have hBin :
              binaryFactorProduct (insert i U) (insert i S) z (fun j => star (z j)) =
                z i * binaryFactorProduct U S z (fun j => star (z j)) := by
            rw [binaryFactorProduct, Finset.prod_insert hi]
            simp only [Finset.mem_insert, true_or, if_true]
            congr 1
            apply Finset.prod_congr rfl
            intro j hj
            have hji : j ≠ i := fun hji => hi (hji ▸ hj)
            simp [hji]
          rw [hleft, hq, hBin]
          ring
      · refine ⟨u, S, Finset.mem_powerset.mpr (fun _ hj =>
          Finset.mem_insert_of_mem (hSsub hj)), huNorm, ?_⟩
        rw [hright, hq]
        simp only [binaryFactorProduct, Finset.prod_insert hi, hiS, if_false]
        ring

/-- Multiplying by a squarefree family of split rational primes increases the
number of oriented two-square representations by at most `2` per factor. -/
theorem representationVectors_mul_splitProduct_upper
    {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (p : ι → ℕ) (z : ι → GaussianInt)
    (hp : ∀ i ∈ U, (p i).Prime)
    (hnorm : ∀ i ∈ U, (z i).norm.natAbs = p i)
    (A : ℕ) (hA : 1 ≤ A) :
    (representationVectors (A * ∏ i ∈ U, p i)).card ≤
      (representationVectors A).card * 2 ^ U.card := by
  classical
  let source : Finset (GaussianInt × Finset ι) :=
    (gaussianRepresentations A).product U.powerset
  let compose : GaussianInt × Finset ι → GaussianInt := fun qS =>
    qS.1 * binaryFactorProduct U qS.2 z (fun i => star (z i))
  let image : Finset GaussianInt := source.image compose
  have hprodOne : 1 ≤ ∏ i ∈ U, p i :=
    Finset.one_le_prod fun i hi => (hp i hi).one_le
  have htargetPos : 1 ≤ A * ∏ i ∈ U, p i :=
    one_le_mul hA hprodOne
  have hsub : gaussianRepresentations (A * ∏ i ∈ U, p i) ⊆ image := by
    intro w hw
    have hwNorm := (mem_gaussianRepresentations_iff htargetPos w).mp hw
    obtain ⟨q, S, hSpow, hqNorm, hwq⟩ :=
      gaussian_strip_split_family U p z hp hnorm A hwNorm
    apply Finset.mem_image.mpr
    refine ⟨(q, S), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨(mem_gaussianRepresentations_iff hA q).mpr hqNorm, hSpow⟩
    · exact hwq.symm
  calc
    (representationVectors (A * ∏ i ∈ U, p i)).card =
        (gaussianRepresentations (A * ∏ i ∈ U, p i)).card :=
          (card_gaussianRepresentations _).symm
    _ ≤ image.card := Finset.card_le_card hsub
    _ ≤ source.card := Finset.card_image_le
    _ = (gaussianRepresentations A).card * U.powerset.card :=
      Finset.card_product _ _
    _ = (representationVectors A).card * 2 ^ U.card := by
      rw [card_gaussianRepresentations, Finset.card_powerset]

lemma gaussian_binaryProduct_norm
    {ι : Type*} [DecidableEq ι]
    (U S : Finset ι) (p : ι → ℕ) (z : ι → GaussianInt)
    (hnorm : ∀ i ∈ U, (z i).norm.natAbs = p i) :
    (binaryFactorProduct U S z (fun i => star (z i))).norm.natAbs =
      ∏ i ∈ U, p i := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [binaryFactorProduct]
  | @insert i U hi ih =>
      have hiNorm := hnorm i (Finset.mem_insert_self i U)
      have hrest : ∀ j ∈ U, (z j).norm.natAbs = p j := by
        intro j hj
        exact hnorm j (Finset.mem_insert_of_mem hj)
      rw [binaryFactorProduct]
      simp only [Finset.prod_insert hi, Zsqrtd.norm_mul, Int.natAbs_mul,
        Finset.mem_insert]
      rw [show (Zsqrtd.norm (∏ j ∈ U,
          if j ∈ S then z j else star (z j))).natAbs = ∏ j ∈ U, p j by
        simpa only [binaryFactorProduct] using ih hrest]
      by_cases hiS : i ∈ S
      · simp [hiS, hiNorm]
      · simp [hiS, gaussian_norm_nat_star, hiNorm]

lemma gaussian_binaryProduct_is_representation
    {ι : Type*} [DecidableEq ι]
    (U S : Finset ι) (p : ι → ℕ) (z : ι → GaussianInt)
    (hp : ∀ i ∈ U, (p i).Prime)
    (hnorm : ∀ i ∈ U, (z i).norm.natAbs = p i) :
    gaussianCoords (binaryFactorProduct U S z (fun i => star (z i))) ∈
      representationVectors (∏ i ∈ U, p i) := by
  classical
  let g := binaryFactorProduct U S z (fun i => star (z i))
  let s := ∏ i ∈ U, p i
  have hs : 1 ≤ s := Finset.one_le_prod fun i hi => (hp i hi).one_le
  apply (mem_representationVectors_iff hs _).mpr
  have hnormNat : g.norm.natAbs = s := gaussian_binaryProduct_norm U S p z hnorm
  have hnormInt : g.norm = (s : ℤ) := by
    rw [← GaussianInt.abs_natCast_norm g]
    exact_mod_cast hnormNat
  change g.re ^ 2 + g.im ^ 2 = (s : ℤ)
  rw [← hnormInt]
  simp [Zsqrtd.norm, pow_two]

lemma exists_gaussian_factor_of_prime_mod_four_one
    {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    ∃ z : GaussianInt,
      z.norm.natAbs = p ∧ ¬z ∣ star z := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hsum⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have hp2 : p ≠ 2 := by
    intro hpEq
    have : 2 % 4 = 1 := by rw [← hpEq]; exact hmod
    norm_num at this
  have ha0 : a ≠ 0 := by
    intro ha
    subst a
    have hsquare : IsSquare p := ⟨b, by simpa [pow_two] using hsum.symm⟩
    exact hp.prime.not_isSquare hsquare
  have hb0 : b ≠ 0 := by
    intro hb
    subst b
    have hsquare : IsSquare p := ⟨a, by simpa [pow_two] using hsum.symm⟩
    exact hp.prime.not_isSquare hsquare
  let z : GaussianInt := ⟨(a : ℤ), (b : ℤ)⟩
  refine ⟨z, gaussian_mk_nat_norm hsum, ?_⟩
  exact gaussian_mk_nat_not_dvd_conj hp hp2 (Nat.pos_of_ne_zero ha0)
    (Nat.pos_of_ne_zero hb0) hsum

/-- Distinct split Gaussian factors generate at least `2^|U|` oriented
sum-of-two-squares representations of the product of their rational norms. -/
theorem splitGaussian_representation_lower
    {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (p : ι → ℕ) (z : ι → GaussianInt)
    (hp : ∀ i ∈ U, (p i).Prime)
    (hpInj : Set.InjOn p U)
    (hnorm : ∀ i ∈ U, (z i).norm.natAbs = p i)
    (hnotConj : ∀ i ∈ U, ¬z i ∣ star (z i)) :
    2 ^ U.card ≤ (representationVectors (∏ i ∈ U, p i)).card := by
  classical
  let b : ι → GaussianInt := fun i => star (z i)
  have ha : ∀ i ∈ U, Prime (z i) := by
    intro i hi
    exact gaussian_prime_of_norm_prime (hp i hi) (hnorm i hi)
  have haa : ∀ i ∈ U, ∀ j ∈ U, z i ∣ z j → i = j := by
    intro i hi j hj hd
    apply hpInj hi hj
    exact gaussian_prime_norm_dvd_prime_norm_eq (hp i hi) (hp j hj)
      (hnorm i hi) (hnorm j hj) hd
  have hab : ∀ i ∈ U, ∀ j ∈ U, ¬z i ∣ b j := by
    intro i hi j hj hd
    have hpEq : p i = p j := gaussian_prime_norm_dvd_prime_norm_eq
      (hp i hi) (hp j hj) (hnorm i hi)
      (by dsimp [b]; rw [gaussian_norm_nat_star, hnorm j hj]) hd
    have hij : i = j := hpInj hi hj hpEq
    subst j
    exact hnotConj i hi hd
  let G : Finset GaussianInt := U.powerset.image fun S =>
    binaryFactorProduct U S z b
  have hGcard : G.card = 2 ^ U.card :=
    card_binaryFactorProducts U z b ha haa hab
  let C : Finset IntPoint := G.image gaussianCoords
  have hCcard : C.card = 2 ^ U.card := by
    rw [Finset.card_image_of_injective _ gaussianCoords_injective, hGcard]
  have hCsub : C ⊆ representationVectors (∏ i ∈ U, p i) := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨g, hg, rfl⟩
    rcases Finset.mem_image.mp hg with ⟨S, hS, rfl⟩
    exact gaussian_binaryProduct_is_representation U S p z hp hnorm
  rw [← hCcard]
  exact Finset.card_le_card hCsub

/-- A finite injective family of rational primes congruent to one modulo four
has at least two oriented representations per prime factor in its product. -/
theorem splitPrimeProduct_representation_lower
    {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hmod : ∀ i, p i % 4 = 1) (hpInj : Function.Injective p) :
    2 ^ Fintype.card ι ≤
      (representationVectors (∏ i, p i)).card := by
  classical
  let z : ι → GaussianInt := fun i =>
    Classical.choose (exists_gaussian_factor_of_prime_mod_four_one (hp i) (hmod i))
  have hzspec : ∀ i, (z i).norm.natAbs = p i ∧ ¬z i ∣ star (z i) := by
    intro i
    exact Classical.choose_spec
      (exists_gaussian_factor_of_prime_mod_four_one (hp i) (hmod i))
  have h := splitGaussian_representation_lower Finset.univ p z
    (by simp [hp]) (by
      intro i _ j _ hij
      exact hpInj hij)
    (by intro i _; exact (hzspec i).1)
    (by intro i _; exact (hzspec i).2)
  simpa using h

end Erdos959
