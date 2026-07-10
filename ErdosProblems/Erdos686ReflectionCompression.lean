/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686

/-!
# Erdős Problem 686: reflection gcd compression

The reflection congruence for a hypothetical `N = 4` gap solution gives

`S ∣ c * ∏ i ∈ Icc 1 k, (n + i)`,

where `S = 2*n+d+k+1` and `c` is `3` or `5` according to the parity of `k`.
For every lower-block factor, the already verified reflection bound gives

`gcd S (n+i) ∣ d+k+1-2*i`.

This module proves the general gcd-compression principle needed to replace all
lower-block factors by their reflected differences.  It then obtains the
unconditional consequence

`S ∣ reflectionCoeff k * reflectionProduct k d`.
-/

namespace Erdos686

namespace Erdos686Variant

/-- Replace one factor in a divisibility by any multiple of its gcd with the
positive modulus. -/
lemma dvd_mul_replace_of_gcd_dvd {M A x y : ℕ} (hM : 0 < M)
    (hdiv : M ∣ A * x) (hgcd : Nat.gcd M x ∣ y) :
    M ∣ A * y := by
  let g := Nat.gcd M x
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left x hM
  have hgdvdM : g ∣ M := Nat.gcd_dvd_left M x
  have hgdvdx : g ∣ x := Nat.gcd_dvd_right M x
  have hM_eq : g * (M / g) = M := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hgdvdM
  have hx_eq : g * (x / g) = x := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hgdvdx
  have hscaled : g * (M / g) ∣ g * ((x / g) * A) := by
    rw [hM_eq, ← mul_assoc, hx_eq]
    simpa [mul_comm] using hdiv
  have hquot_dvd : M / g ∣ (x / g) * A :=
    Nat.dvd_of_mul_dvd_mul_left hgpos hscaled
  have hcop : (M / g).Coprime (x / g) := by
    simpa [g] using Nat.coprime_div_gcd_div_gcd (m := M) (n := x) hgpos
  have hMquot_dvd_A : M / g ∣ A := hcop.dvd_of_dvd_mul_left hquot_dvd
  obtain ⟨r, hr⟩ := hMquot_dvd_A
  obtain ⟨t, ht⟩ := hgcd
  refine ⟨r * t, ?_⟩
  calc
    A * y = ((M / g) * r) * (g * t) := by rw [hr, ht]
    _ = (g * (M / g)) * (r * t) := by ring
    _ = M * (r * t) := by rw [hM_eq]

/-- General gcd compression over a finite product.  If a positive modulus
divides `c * ∏ f i`, and each `gcd M (f i)` divides the corresponding
replacement `g i`, then the modulus divides `c * ∏ g i`. -/
theorem dvd_mul_finset_prod_replace_of_gcd_dvd
    {ι : Type*} (s : Finset ι) {M c : ℕ}
    (f g : ι → ℕ) (hM : 0 < M)
    (hdiv : M ∣ c * ∏ i ∈ s, f i)
    (hgcd : ∀ i ∈ s, Nat.gcd M (f i) ∣ g i) :
    M ∣ c * ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction generalizing c with
  | empty => simpa using hdiv
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha] at hdiv ⊢
      have hone : M ∣ (c * ∏ i ∈ s, f i) * g a :=
        dvd_mul_replace_of_gcd_dvd hM
          (by simpa [mul_assoc, mul_comm, mul_left_comm] using hdiv)
          (hgcd a (Finset.mem_insert_self a s))
      have hrest : M ∣ (c * g a) * ∏ i ∈ s, f i := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hone
      have hcompressed := ih (c := c * g a) hrest
        (fun i hi => hgcd i (Finset.mem_insert_of_mem hi))
      simpa [mul_assoc, mul_comm, mul_left_comm] using hcompressed

/-- Even-parity reflection compression: the entire lower block in the
reflection congruence can be replaced by the reflected difference product. -/
theorem reflection_compression_even {k n d : ℕ} (hk : Even k)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    2 * n + d + k + 1 ∣ 3 * reflectionProduct k d := by
  let S := 2 * n + d + k + 1
  have hSpos : 0 < S := by simp [S]
  have hbase : S ∣ 3 * ∏ i ∈ Finset.Icc 1 k, (n + i) := by
    simpa [S, blockProduct] using reflection_even hk heq
  have hcompressed := dvd_mul_finset_prod_replace_of_gcd_dvd
    (Finset.Icc 1 k) (M := S) (c := 3)
    (fun i => n + i) (fun i => d + k + 1 - 2 * i) hSpos hbase
    (fun i _ => by simpa [S] using reflection_gcd_bound k n d i)
  simpa [S, reflectionProduct] using hcompressed

/-- Odd-parity reflection compression: the entire lower block in the
reflection congruence can be replaced by the reflected difference product. -/
theorem reflection_compression_odd {k n d : ℕ} (hk : Odd k)
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    2 * n + d + k + 1 ∣ 5 * reflectionProduct k d := by
  let S := 2 * n + d + k + 1
  have hSpos : 0 < S := by simp [S]
  have hbase : S ∣ 5 * ∏ i ∈ Finset.Icc 1 k, (n + i) := by
    simpa [S, blockProduct] using reflection_odd hk heq
  have hcompressed := dvd_mul_finset_prod_replace_of_gcd_dvd
    (Finset.Icc 1 k) (M := S) (c := 5)
    (fun i => n + i) (fun i => d + k + 1 - 2 * i) hSpos hbase
    (fun i _ => by simpa [S] using reflection_gcd_bound k n d i)
  simpa [S, reflectionProduct] using hcompressed

/-- Uniform reflection compression for every hypothetical `N = 4` gap
solution, with coefficient `3` for even `k` and `5` for odd `k`. -/
theorem reflection_compression {k n d : ℕ}
    (heq : blockProduct k (n + d) = 4 * blockProduct k n) :
    2 * n + d + k + 1 ∣ reflectionCoeff k * reflectionProduct k d := by
  unfold reflectionCoeff
  by_cases hk : Even k
  · simpa [hk] using reflection_compression_even hk heq
  · have hkodd : Odd k := Nat.not_even_iff_odd.mp hk
    simpa [hk] using reflection_compression_odd hkodd heq

end Erdos686Variant

end Erdos686
