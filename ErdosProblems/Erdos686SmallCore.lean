/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686ConstantQuotient

/-!
# Erdős Problem 686: small-`k` finite core for `d ≤ 220`

Kernel-checked finite core of the small-`k` branch of the `N = 4` exclusion:
for every `5 ≤ k ≤ 15`, `k ≤ d ≤ 220`, and every `n` inside the exact ratio
window
`(n+d+k)^k ≤ 4·(n+k)^k` and `4·(n+1)^k ≤ (n+d+1)^k`,
some row `j ∈ [1,5]` (hence `j ∈ [1,k]`) escapes the localized divisor
skeleton: `¬ (n+j) ∣ shiftedDiffProductAt k d j`.

The window pins `n` to a band of width `≈ k` around `d/(4^{1/k}-1)`.  Both
sides are linearized with per-`k` rational brackets of `4^{1/k}` via
`ratio_window_linearize_of_pow_bracket` (lower side, from the upper window
inequality) and `ratio_window_upper_linearize_of_pow_bracket` (upper side,
from the lower window inequality).  Each `k` then needs only a
`(221-k) × W_k` grid certificate (`≈ 2-3.3k` points instead of the `≈ 500k`
points of the naive `n × d` rectangle), checked by a single kernel `decide`.

Band parameters (from `compute/erdos686_small_core_bands.py`, cross-checked
against the exact-arithmetic scan banked in
`compute/artifacts/small_core_witnesses.json`: 20779 window triples, all with
`n ≤ 2271`, every one failing some row `j ≤ 5`):

| `k` | `A/B > 4^{1/k}` | `A'/B' < 4^{1/k}` | `nLo(k,d)`          | `W`  |
|-----|-----------------|-------------------|---------------------|------|
|  5  | 223/169         | 318/241           | `169*d/54 + 1 - 5`  |  5   |
|  6  | 349/277         | 286/227           | `277*d/72 + 1 - 6`  |  6   |
|  7  | 423/347         | 295/242           | `347*d/76 + 1 - 7`  |  7   |
|  8  | 465/391         | 44/37             | `391*d/74 + 1 - 8`  |  8   |
|  9  | 7/6             | 463/397           | `6*d/1 + 1 - 9`     | 11   |
| 10  | 309/269         | 394/343           | `269*d/40 + 1 - 10` | 10   |
| 11  | 76/67           | 397/350           | `67*d/9 + 1 - 11`   | 11   |
| 12  | 449/400         | 55/49             | `400*d/49 + 1 - 12` | 12   |
| 13  | 435/391         | 89/80             | `391*d/44 + 1 - 13` | 13   |
| 14  | 350/317         | 297/269           | `317*d/33 + 1 - 14` | 14   |
| 15  | 419/382         | 34/31             | `382*d/37 + 1 - 15` | 16   |
-/

namespace Erdos686

namespace Erdos686Variant

/-- The `n`-abscissa of grid point `i` of the per-`k` window band at gap `d`:
`n = num·d/den + 1 - k + i` (with `den` the per-`k` bracket denominator
`A - B` and `num = B`). -/
def smallCoreBandN (num den k d i : ℕ) : ℕ := num * d / den + 1 - k + i

/-- The per-point certificate payload: inside the exact `N = 4` ratio window,
some row `j ≤ 5` escapes the localized divisor skeleton.  Kept as a reducible
abbreviation so kernel `decide` sees the composite `Decidable` instance. -/
abbrev SmallCoreEscape (k d n : ℕ) : Prop :=
  (n + d + k) ^ k ≤ 4 * (n + k) ^ k →
  4 * (n + 1) ^ k ≤ (n + d + 1) ^ k →
  ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt k d j

/-- Layer 1: over the whole small-`k` range, the lower window inequality with
`d ≤ 220` already forces `n < 2287`.  The window is lifted from exponent `k`
to exponent `15` and linearized with the bracket `57/52 < 4^{1/15}`
(`57^15 < 4·52^15`), giving `57(n+1) < 52(n+d+1)`, hence
`5n < 52·220 - 5 = 11435`. -/
theorem window_n_bound_small_k
    {k n d : ℕ} (hk1 : 1 ≤ k) (hk15 : k ≤ 15) (hd220 : d ≤ 220)
    (hlo : 4 * (n + 1) ^ k ≤ (n + d + 1) ^ k) :
    n < 2287 := by
  have hsplit : k + (15 - k) = 15 := by omega
  have h1 : (n + 1) ^ 15 = (n + 1) ^ k * (n + 1) ^ (15 - k) := by
    rw [← pow_add, hsplit]
  have h2 : (n + d + 1) ^ 15 = (n + d + 1) ^ k * (n + d + 1) ^ (15 - k) := by
    rw [← pow_add, hsplit]
  have h3 : (n + 1) ^ (15 - k) ≤ (n + d + 1) ^ (15 - k) :=
    Nat.pow_le_pow_left (by omega) _
  have hlift : 4 * (n + 1) ^ 15 ≤ (n + d + 1) ^ 15 := by
    calc
      4 * (n + 1) ^ 15 = 4 * (n + 1) ^ k * (n + 1) ^ (15 - k) := by
        rw [h1]; ring
      _ ≤ (n + d + 1) ^ k * (n + d + 1) ^ (15 - k) := Nat.mul_le_mul hlo h3
      _ = (n + d + 1) ^ 15 := h2.symm
  have hbr : 57 ^ 15 < 4 * 52 ^ 15 := by norm_num
  have hlin := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 57) (B := 52) (k := 15) (n := n) (d := d) (by norm_num)
    hbr hlift
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked band certificate for `k = 5`:
-- `d ∈ [5, 220]`, `n = 169*d/54 + 1 - 5 + i`, `i < 5`.
private theorem small_core_cert_k5 :
    ∀ (r : Fin 216) (i : Fin 5),
      SmallCoreEscape 5 (5 + (r : ℕ))
        (smallCoreBandN 169 54 5 (5 + (r : ℕ)) (i : ℕ)) := by
  decide

/-- Banded escape for `k = 5`: the window brackets
`223/169 > 4^(1/5) > 318/241` confine `n` to the certified band. -/
private theorem small_core_escape_k5 {n d : ℕ} (hd : 5 ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + 5) ^ 5 ≤ 4 * (n + 5) ^ 5)
    (hlo : 4 * (n + 1) ^ 5 ≤ (n + d + 1) ^ 5) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt 5 d j := by
  have hbrL : 4 * 169 ^ 5 < 223 ^ 5 := by norm_num
  have hL := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 223) (B := 169) (k := 5) (n := n) (d := d) (by norm_num)
    hbrL hup
  have hbrU : 318 ^ 5 < 4 * 241 ^ 5 := by norm_num
  have hU := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 318) (B := 241) (k := 5) (n := n) (d := d) (by norm_num)
    hbrU hlo
  have hr : d - 5 < 216 := by omega
  have hi : n - (169 * d / 54 + 1 - 5) < 5 := by omega
  have hd_eq : 5 + (d - 5) = d := by omega
  have hn_eq : smallCoreBandN 169 54 5 (5 + (d - 5))
      (n - (169 * d / 54 + 1 - 5)) = n := by
    simp only [smallCoreBandN]
    omega
  have hcert : SmallCoreEscape 5 (5 + (d - 5))
      (smallCoreBandN 169 54 5 (5 + (d - 5))
        (n - (169 * d / 54 + 1 - 5))) :=
    small_core_cert_k5 ⟨d - 5, hr⟩ ⟨n - (169 * d / 54 + 1 - 5), hi⟩
  rw [hn_eq, hd_eq] at hcert
  exact hcert hup hlo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked band certificate for `k = 6`:
-- `d ∈ [6, 220]`, `n = 277*d/72 + 1 - 6 + i`, `i < 6`.
private theorem small_core_cert_k6 :
    ∀ (r : Fin 215) (i : Fin 6),
      SmallCoreEscape 6 (6 + (r : ℕ))
        (smallCoreBandN 277 72 6 (6 + (r : ℕ)) (i : ℕ)) := by
  decide

/-- Banded escape for `k = 6`: the window brackets
`349/277 > 4^(1/6) > 286/227` confine `n` to the certified band. -/
private theorem small_core_escape_k6 {n d : ℕ} (hd : 6 ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + 6) ^ 6 ≤ 4 * (n + 6) ^ 6)
    (hlo : 4 * (n + 1) ^ 6 ≤ (n + d + 1) ^ 6) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt 6 d j := by
  have hbrL : 4 * 277 ^ 6 < 349 ^ 6 := by norm_num
  have hL := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 349) (B := 277) (k := 6) (n := n) (d := d) (by norm_num)
    hbrL hup
  have hbrU : 286 ^ 6 < 4 * 227 ^ 6 := by norm_num
  have hU := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 286) (B := 227) (k := 6) (n := n) (d := d) (by norm_num)
    hbrU hlo
  have hr : d - 6 < 215 := by omega
  have hi : n - (277 * d / 72 + 1 - 6) < 6 := by omega
  have hd_eq : 6 + (d - 6) = d := by omega
  have hn_eq : smallCoreBandN 277 72 6 (6 + (d - 6))
      (n - (277 * d / 72 + 1 - 6)) = n := by
    simp only [smallCoreBandN]
    omega
  have hcert : SmallCoreEscape 6 (6 + (d - 6))
      (smallCoreBandN 277 72 6 (6 + (d - 6))
        (n - (277 * d / 72 + 1 - 6))) :=
    small_core_cert_k6 ⟨d - 6, hr⟩ ⟨n - (277 * d / 72 + 1 - 6), hi⟩
  rw [hn_eq, hd_eq] at hcert
  exact hcert hup hlo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked band certificate for `k = 7`:
-- `d ∈ [7, 220]`, `n = 347*d/76 + 1 - 7 + i`, `i < 7`.
private theorem small_core_cert_k7 :
    ∀ (r : Fin 214) (i : Fin 7),
      SmallCoreEscape 7 (7 + (r : ℕ))
        (smallCoreBandN 347 76 7 (7 + (r : ℕ)) (i : ℕ)) := by
  decide

/-- Banded escape for `k = 7`: the window brackets
`423/347 > 4^(1/7) > 295/242` confine `n` to the certified band. -/
private theorem small_core_escape_k7 {n d : ℕ} (hd : 7 ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + 7) ^ 7 ≤ 4 * (n + 7) ^ 7)
    (hlo : 4 * (n + 1) ^ 7 ≤ (n + d + 1) ^ 7) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt 7 d j := by
  have hbrL : 4 * 347 ^ 7 < 423 ^ 7 := by norm_num
  have hL := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 423) (B := 347) (k := 7) (n := n) (d := d) (by norm_num)
    hbrL hup
  have hbrU : 295 ^ 7 < 4 * 242 ^ 7 := by norm_num
  have hU := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 295) (B := 242) (k := 7) (n := n) (d := d) (by norm_num)
    hbrU hlo
  have hr : d - 7 < 214 := by omega
  have hi : n - (347 * d / 76 + 1 - 7) < 7 := by omega
  have hd_eq : 7 + (d - 7) = d := by omega
  have hn_eq : smallCoreBandN 347 76 7 (7 + (d - 7))
      (n - (347 * d / 76 + 1 - 7)) = n := by
    simp only [smallCoreBandN]
    omega
  have hcert : SmallCoreEscape 7 (7 + (d - 7))
      (smallCoreBandN 347 76 7 (7 + (d - 7))
        (n - (347 * d / 76 + 1 - 7))) :=
    small_core_cert_k7 ⟨d - 7, hr⟩ ⟨n - (347 * d / 76 + 1 - 7), hi⟩
  rw [hn_eq, hd_eq] at hcert
  exact hcert hup hlo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked band certificate for `k = 8`:
-- `d ∈ [8, 220]`, `n = 391*d/74 + 1 - 8 + i`, `i < 8`.
private theorem small_core_cert_k8 :
    ∀ (r : Fin 213) (i : Fin 8),
      SmallCoreEscape 8 (8 + (r : ℕ))
        (smallCoreBandN 391 74 8 (8 + (r : ℕ)) (i : ℕ)) := by
  decide

/-- Banded escape for `k = 8`: the window brackets
`465/391 > 4^(1/8) > 44/37` confine `n` to the certified band. -/
private theorem small_core_escape_k8 {n d : ℕ} (hd : 8 ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + 8) ^ 8 ≤ 4 * (n + 8) ^ 8)
    (hlo : 4 * (n + 1) ^ 8 ≤ (n + d + 1) ^ 8) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt 8 d j := by
  have hbrL : 4 * 391 ^ 8 < 465 ^ 8 := by norm_num
  have hL := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 465) (B := 391) (k := 8) (n := n) (d := d) (by norm_num)
    hbrL hup
  have hbrU : 44 ^ 8 < 4 * 37 ^ 8 := by norm_num
  have hU := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 44) (B := 37) (k := 8) (n := n) (d := d) (by norm_num)
    hbrU hlo
  have hr : d - 8 < 213 := by omega
  have hi : n - (391 * d / 74 + 1 - 8) < 8 := by omega
  have hd_eq : 8 + (d - 8) = d := by omega
  have hn_eq : smallCoreBandN 391 74 8 (8 + (d - 8))
      (n - (391 * d / 74 + 1 - 8)) = n := by
    simp only [smallCoreBandN]
    omega
  have hcert : SmallCoreEscape 8 (8 + (d - 8))
      (smallCoreBandN 391 74 8 (8 + (d - 8))
        (n - (391 * d / 74 + 1 - 8))) :=
    small_core_cert_k8 ⟨d - 8, hr⟩ ⟨n - (391 * d / 74 + 1 - 8), hi⟩
  rw [hn_eq, hd_eq] at hcert
  exact hcert hup hlo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked band certificate for `k = 9`:
-- `d ∈ [9, 220]`, `n = 6*d/1 + 1 - 9 + i`, `i < 11`.
private theorem small_core_cert_k9 :
    ∀ (r : Fin 212) (i : Fin 11),
      SmallCoreEscape 9 (9 + (r : ℕ))
        (smallCoreBandN 6 1 9 (9 + (r : ℕ)) (i : ℕ)) := by
  decide

/-- Banded escape for `k = 9`: the window brackets
`7/6 > 4^(1/9) > 463/397` confine `n` to the certified band. -/
private theorem small_core_escape_k9 {n d : ℕ} (hd : 9 ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + 9) ^ 9 ≤ 4 * (n + 9) ^ 9)
    (hlo : 4 * (n + 1) ^ 9 ≤ (n + d + 1) ^ 9) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt 9 d j := by
  have hbrL : 4 * 6 ^ 9 < 7 ^ 9 := by norm_num
  have hL := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 7) (B := 6) (k := 9) (n := n) (d := d) (by norm_num)
    hbrL hup
  have hbrU : 463 ^ 9 < 4 * 397 ^ 9 := by norm_num
  have hU := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 463) (B := 397) (k := 9) (n := n) (d := d) (by norm_num)
    hbrU hlo
  have hr : d - 9 < 212 := by omega
  have hi : n - (6 * d / 1 + 1 - 9) < 11 := by omega
  have hd_eq : 9 + (d - 9) = d := by omega
  have hn_eq : smallCoreBandN 6 1 9 (9 + (d - 9))
      (n - (6 * d / 1 + 1 - 9)) = n := by
    simp only [smallCoreBandN]
    omega
  have hcert : SmallCoreEscape 9 (9 + (d - 9))
      (smallCoreBandN 6 1 9 (9 + (d - 9))
        (n - (6 * d / 1 + 1 - 9))) :=
    small_core_cert_k9 ⟨d - 9, hr⟩ ⟨n - (6 * d / 1 + 1 - 9), hi⟩
  rw [hn_eq, hd_eq] at hcert
  exact hcert hup hlo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked band certificate for `k = 10`:
-- `d ∈ [10, 220]`, `n = 269*d/40 + 1 - 10 + i`, `i < 10`.
private theorem small_core_cert_k10 :
    ∀ (r : Fin 211) (i : Fin 10),
      SmallCoreEscape 10 (10 + (r : ℕ))
        (smallCoreBandN 269 40 10 (10 + (r : ℕ)) (i : ℕ)) := by
  decide

/-- Banded escape for `k = 10`: the window brackets
`309/269 > 4^(1/10) > 394/343` confine `n` to the certified band. -/
private theorem small_core_escape_k10 {n d : ℕ} (hd : 10 ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + 10) ^ 10 ≤ 4 * (n + 10) ^ 10)
    (hlo : 4 * (n + 1) ^ 10 ≤ (n + d + 1) ^ 10) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt 10 d j := by
  have hbrL : 4 * 269 ^ 10 < 309 ^ 10 := by norm_num
  have hL := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 309) (B := 269) (k := 10) (n := n) (d := d) (by norm_num)
    hbrL hup
  have hbrU : 394 ^ 10 < 4 * 343 ^ 10 := by norm_num
  have hU := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 394) (B := 343) (k := 10) (n := n) (d := d) (by norm_num)
    hbrU hlo
  have hr : d - 10 < 211 := by omega
  have hi : n - (269 * d / 40 + 1 - 10) < 10 := by omega
  have hd_eq : 10 + (d - 10) = d := by omega
  have hn_eq : smallCoreBandN 269 40 10 (10 + (d - 10))
      (n - (269 * d / 40 + 1 - 10)) = n := by
    simp only [smallCoreBandN]
    omega
  have hcert : SmallCoreEscape 10 (10 + (d - 10))
      (smallCoreBandN 269 40 10 (10 + (d - 10))
        (n - (269 * d / 40 + 1 - 10))) :=
    small_core_cert_k10 ⟨d - 10, hr⟩ ⟨n - (269 * d / 40 + 1 - 10), hi⟩
  rw [hn_eq, hd_eq] at hcert
  exact hcert hup hlo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked band certificate for `k = 11`:
-- `d ∈ [11, 220]`, `n = 67*d/9 + 1 - 11 + i`, `i < 11`.
private theorem small_core_cert_k11 :
    ∀ (r : Fin 210) (i : Fin 11),
      SmallCoreEscape 11 (11 + (r : ℕ))
        (smallCoreBandN 67 9 11 (11 + (r : ℕ)) (i : ℕ)) := by
  decide

/-- Banded escape for `k = 11`: the window brackets
`76/67 > 4^(1/11) > 397/350` confine `n` to the certified band. -/
private theorem small_core_escape_k11 {n d : ℕ} (hd : 11 ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + 11) ^ 11 ≤ 4 * (n + 11) ^ 11)
    (hlo : 4 * (n + 1) ^ 11 ≤ (n + d + 1) ^ 11) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt 11 d j := by
  have hbrL : 4 * 67 ^ 11 < 76 ^ 11 := by norm_num
  have hL := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 76) (B := 67) (k := 11) (n := n) (d := d) (by norm_num)
    hbrL hup
  have hbrU : 397 ^ 11 < 4 * 350 ^ 11 := by norm_num
  have hU := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 397) (B := 350) (k := 11) (n := n) (d := d) (by norm_num)
    hbrU hlo
  have hr : d - 11 < 210 := by omega
  have hi : n - (67 * d / 9 + 1 - 11) < 11 := by omega
  have hd_eq : 11 + (d - 11) = d := by omega
  have hn_eq : smallCoreBandN 67 9 11 (11 + (d - 11))
      (n - (67 * d / 9 + 1 - 11)) = n := by
    simp only [smallCoreBandN]
    omega
  have hcert : SmallCoreEscape 11 (11 + (d - 11))
      (smallCoreBandN 67 9 11 (11 + (d - 11))
        (n - (67 * d / 9 + 1 - 11))) :=
    small_core_cert_k11 ⟨d - 11, hr⟩ ⟨n - (67 * d / 9 + 1 - 11), hi⟩
  rw [hn_eq, hd_eq] at hcert
  exact hcert hup hlo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked band certificate for `k = 12`:
-- `d ∈ [12, 220]`, `n = 400*d/49 + 1 - 12 + i`, `i < 12`.
private theorem small_core_cert_k12 :
    ∀ (r : Fin 209) (i : Fin 12),
      SmallCoreEscape 12 (12 + (r : ℕ))
        (smallCoreBandN 400 49 12 (12 + (r : ℕ)) (i : ℕ)) := by
  decide

/-- Banded escape for `k = 12`: the window brackets
`449/400 > 4^(1/12) > 55/49` confine `n` to the certified band. -/
private theorem small_core_escape_k12 {n d : ℕ} (hd : 12 ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + 12) ^ 12 ≤ 4 * (n + 12) ^ 12)
    (hlo : 4 * (n + 1) ^ 12 ≤ (n + d + 1) ^ 12) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt 12 d j := by
  have hbrL : 4 * 400 ^ 12 < 449 ^ 12 := by norm_num
  have hL := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 449) (B := 400) (k := 12) (n := n) (d := d) (by norm_num)
    hbrL hup
  have hbrU : 55 ^ 12 < 4 * 49 ^ 12 := by norm_num
  have hU := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 55) (B := 49) (k := 12) (n := n) (d := d) (by norm_num)
    hbrU hlo
  have hr : d - 12 < 209 := by omega
  have hi : n - (400 * d / 49 + 1 - 12) < 12 := by omega
  have hd_eq : 12 + (d - 12) = d := by omega
  have hn_eq : smallCoreBandN 400 49 12 (12 + (d - 12))
      (n - (400 * d / 49 + 1 - 12)) = n := by
    simp only [smallCoreBandN]
    omega
  have hcert : SmallCoreEscape 12 (12 + (d - 12))
      (smallCoreBandN 400 49 12 (12 + (d - 12))
        (n - (400 * d / 49 + 1 - 12))) :=
    small_core_cert_k12 ⟨d - 12, hr⟩ ⟨n - (400 * d / 49 + 1 - 12), hi⟩
  rw [hn_eq, hd_eq] at hcert
  exact hcert hup hlo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked band certificate for `k = 13`:
-- `d ∈ [13, 220]`, `n = 391*d/44 + 1 - 13 + i`, `i < 13`.
private theorem small_core_cert_k13 :
    ∀ (r : Fin 208) (i : Fin 13),
      SmallCoreEscape 13 (13 + (r : ℕ))
        (smallCoreBandN 391 44 13 (13 + (r : ℕ)) (i : ℕ)) := by
  decide

/-- Banded escape for `k = 13`: the window brackets
`435/391 > 4^(1/13) > 89/80` confine `n` to the certified band. -/
private theorem small_core_escape_k13 {n d : ℕ} (hd : 13 ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + 13) ^ 13 ≤ 4 * (n + 13) ^ 13)
    (hlo : 4 * (n + 1) ^ 13 ≤ (n + d + 1) ^ 13) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt 13 d j := by
  have hbrL : 4 * 391 ^ 13 < 435 ^ 13 := by norm_num
  have hL := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 435) (B := 391) (k := 13) (n := n) (d := d) (by norm_num)
    hbrL hup
  have hbrU : 89 ^ 13 < 4 * 80 ^ 13 := by norm_num
  have hU := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 89) (B := 80) (k := 13) (n := n) (d := d) (by norm_num)
    hbrU hlo
  have hr : d - 13 < 208 := by omega
  have hi : n - (391 * d / 44 + 1 - 13) < 13 := by omega
  have hd_eq : 13 + (d - 13) = d := by omega
  have hn_eq : smallCoreBandN 391 44 13 (13 + (d - 13))
      (n - (391 * d / 44 + 1 - 13)) = n := by
    simp only [smallCoreBandN]
    omega
  have hcert : SmallCoreEscape 13 (13 + (d - 13))
      (smallCoreBandN 391 44 13 (13 + (d - 13))
        (n - (391 * d / 44 + 1 - 13))) :=
    small_core_cert_k13 ⟨d - 13, hr⟩ ⟨n - (391 * d / 44 + 1 - 13), hi⟩
  rw [hn_eq, hd_eq] at hcert
  exact hcert hup hlo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked band certificate for `k = 14`:
-- `d ∈ [14, 220]`, `n = 317*d/33 + 1 - 14 + i`, `i < 14`.
private theorem small_core_cert_k14 :
    ∀ (r : Fin 207) (i : Fin 14),
      SmallCoreEscape 14 (14 + (r : ℕ))
        (smallCoreBandN 317 33 14 (14 + (r : ℕ)) (i : ℕ)) := by
  decide

/-- Banded escape for `k = 14`: the window brackets
`350/317 > 4^(1/14) > 297/269` confine `n` to the certified band. -/
private theorem small_core_escape_k14 {n d : ℕ} (hd : 14 ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + 14) ^ 14 ≤ 4 * (n + 14) ^ 14)
    (hlo : 4 * (n + 1) ^ 14 ≤ (n + d + 1) ^ 14) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt 14 d j := by
  have hbrL : 4 * 317 ^ 14 < 350 ^ 14 := by norm_num
  have hL := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 350) (B := 317) (k := 14) (n := n) (d := d) (by norm_num)
    hbrL hup
  have hbrU : 297 ^ 14 < 4 * 269 ^ 14 := by norm_num
  have hU := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 297) (B := 269) (k := 14) (n := n) (d := d) (by norm_num)
    hbrU hlo
  have hr : d - 14 < 207 := by omega
  have hi : n - (317 * d / 33 + 1 - 14) < 14 := by omega
  have hd_eq : 14 + (d - 14) = d := by omega
  have hn_eq : smallCoreBandN 317 33 14 (14 + (d - 14))
      (n - (317 * d / 33 + 1 - 14)) = n := by
    simp only [smallCoreBandN]
    omega
  have hcert : SmallCoreEscape 14 (14 + (d - 14))
      (smallCoreBandN 317 33 14 (14 + (d - 14))
        (n - (317 * d / 33 + 1 - 14))) :=
    small_core_cert_k14 ⟨d - 14, hr⟩ ⟨n - (317 * d / 33 + 1 - 14), hi⟩
  rw [hn_eq, hd_eq] at hcert
  exact hcert hup hlo

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Exhaustive kernel-checked band certificate for `k = 15`:
-- `d ∈ [15, 220]`, `n = 382*d/37 + 1 - 15 + i`, `i < 16`.
private theorem small_core_cert_k15 :
    ∀ (r : Fin 206) (i : Fin 16),
      SmallCoreEscape 15 (15 + (r : ℕ))
        (smallCoreBandN 382 37 15 (15 + (r : ℕ)) (i : ℕ)) := by
  decide

/-- Banded escape for `k = 15`: the window brackets
`419/382 > 4^(1/15) > 34/31` confine `n` to the certified band. -/
private theorem small_core_escape_k15 {n d : ℕ} (hd : 15 ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + 15) ^ 15 ≤ 4 * (n + 15) ^ 15)
    (hlo : 4 * (n + 1) ^ 15 ≤ (n + d + 1) ^ 15) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt 15 d j := by
  have hbrL : 4 * 382 ^ 15 < 419 ^ 15 := by norm_num
  have hL := ratio_window_linearize_of_pow_bracket
    (N := 4) (A := 419) (B := 382) (k := 15) (n := n) (d := d) (by norm_num)
    hbrL hup
  have hbrU : 34 ^ 15 < 4 * 31 ^ 15 := by norm_num
  have hU := ratio_window_upper_linearize_of_pow_bracket
    (N := 4) (A := 34) (B := 31) (k := 15) (n := n) (d := d) (by norm_num)
    hbrU hlo
  have hr : d - 15 < 206 := by omega
  have hi : n - (382 * d / 37 + 1 - 15) < 16 := by omega
  have hd_eq : 15 + (d - 15) = d := by omega
  have hn_eq : smallCoreBandN 382 37 15 (15 + (d - 15))
      (n - (382 * d / 37 + 1 - 15)) = n := by
    simp only [smallCoreBandN]
    omega
  have hcert : SmallCoreEscape 15 (15 + (d - 15))
      (smallCoreBandN 382 37 15 (15 + (d - 15))
        (n - (382 * d / 37 + 1 - 15))) :=
    small_core_cert_k15 ⟨d - 15, hr⟩ ⟨n - (382 * d / 37 + 1 - 15), hi⟩
  rw [hn_eq, hd_eq] at hcert
  exact hcert hup hlo

/-- Prefix form of the `d ≤ 220` finite core of the small-`k` branch: inside
the exact ratio window, some row `j ≤ 5` already escapes the localized
divisor skeleton. -/
theorem row_prefix_escape_small_k_d_le_220
    {k n d : ℕ} (hk5 : 5 ≤ k) (hk15 : k ≤ 15) (hd : k ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1) ^ k ≤ (n + d + 1) ^ k) :
    ∃ j, j ∈ Finset.Icc 1 5 ∧ ¬ n + j ∣ shiftedDiffProductAt k d j := by
  interval_cases k
  · exact small_core_escape_k5 hd hd220 hup hlo
  · exact small_core_escape_k6 hd hd220 hup hlo
  · exact small_core_escape_k7 hd hd220 hup hlo
  · exact small_core_escape_k8 hd hd220 hup hlo
  · exact small_core_escape_k9 hd hd220 hup hlo
  · exact small_core_escape_k10 hd hd220 hup hlo
  · exact small_core_escape_k11 hd hd220 hup hlo
  · exact small_core_escape_k12 hd hd220 hup hlo
  · exact small_core_escape_k13 hd hd220 hup hlo
  · exact small_core_escape_k14 hd hd220 hup hlo
  · exact small_core_escape_k15 hd hd220 hup hlo

/-- The `d ≤ 220` finite core of the small-`k` branch: for `5 ≤ k ≤ 15` and
`k ≤ d ≤ 220`, no ratio-window candidate satisfies all localized row
divisibilities — some row `j ∈ [1,k]` escapes.  (The escaping row found by
the certificates always satisfies `j ≤ 5 ≤ k`.) -/
theorem row_full_escape_small_k_d_le_220
    {k n d : ℕ} (hk5 : 5 ≤ k) (hk15 : k ≤ 15) (hd : k ≤ d) (hd220 : d ≤ 220)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1) ^ k ≤ (n + d + 1) ^ k) :
    ∃ j, j ∈ Finset.Icc 1 k ∧ ¬ n + j ∣ shiftedDiffProductAt k d j := by
  obtain ⟨j, hj, hnot⟩ :=
    row_prefix_escape_small_k_d_le_220 hk5 hk15 hd hd220 hup hlo
  refine ⟨j, ?_, hnot⟩
  simp only [Finset.mem_Icc] at hj ⊢
  omega

end Erdos686Variant

end Erdos686
