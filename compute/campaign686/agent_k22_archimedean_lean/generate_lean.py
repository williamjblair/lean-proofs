#!/usr/bin/env python3
"""Generate the isolated ordinary-kernel k=22 Archimedean modules."""

from __future__ import annotations

from pathlib import Path

import verify


ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "ErdosProblems"
PREFIX = "Erdos686EvenK22"
NS_OPEN = "namespace Erdos686.Erdos686Variant\n"
NS_CLOSE = "\nend Erdos686.Erdos686Variant\n"


def write(module: str, body: str) -> None:
    (OUT / f"{module}.lean").write_text(body)


def polynomial(name: str, terms: dict[int, int], variable: str = "W") -> str:
    pieces: list[str] = []
    for index, (degree, coefficient) in enumerate(
        sorted(terms.items(), reverse=True)
    ):
        absolute = abs(coefficient)
        if degree == 0:
            atom = str(absolute)
        elif degree == 1:
            atom = variable if absolute == 1 else f"{absolute} * {variable}"
        else:
            atom = (
                f"{variable} ^ {degree}"
                if absolute == 1
                else f"{absolute} * {variable} ^ {degree}"
            )
        if index == 0:
            pieces.append(("- " if coefficient < 0 else "") + atom)
        else:
            pieces.append((" - " if coefficient < 0 else " + ") + atom)
    return f"def {name} ({variable} : ℤ) : ℤ :=\n  " + "\n    ".join(pieces)


def generic_polynomial(name: str, terms: dict[int, int], variable: str = "W") -> str:
    return polynomial(name, terms, variable).replace(
        f"def {name} ({variable} : ℤ) : ℤ :=",
        f"def {name} {{R : Type}} [CommRing R] ({variable} : R) : R :=",
    )


def generate_defs() -> None:
    roots = [(2 * j - 1) ** 2 for j in range(1, verify.R + 1)]
    factors = [f"(W ^ 2 - {root})" for root in roots]
    factor_lines = [" * ".join(factors[i : i + 4]) for i in range(0, len(factors), 4)]
    s_def = (
        "def evenTable22S {R : Type} [CommRing R] (W : R) : R :=\n  "
        + " *\n    ".join(factor_lines)
    )
    t_def = generic_polynomial("evenTable22T", verify.T_POLY)
    write(
        f"{PREFIX}Defs",
        "import ErdosProblems.Erdos686EvenK16\n\n"
        + NS_OPEN
        + "\n"
        + s_def
        + "\n\n"
        + t_def
        + NS_CLOSE,
    )


def generate_finite_strip() -> None:
    shard_count = 28
    for shard in range(shard_count):
        lo = 27 + 8 * shard
        hi = min(lo + 8, verify.SPLIT_GAP)
        dependency = (
            f"{PREFIX}Defs" if shard == 0 else f"{PREFIX}FiniteStripS{shard - 1}"
        )
        body = (
            f"import ErdosProblems.{dependency}\n\n"
            + NS_OPEN
            + "\nset_option maxHeartbeats 100000000 in\n"
            + "set_option maxRecDepth 1000000 in\n"
            + f"theorem even22_finite_strip_shard_{shard} :\n"
            + f"    ∀ d : Fin 250, {lo} ≤ d.val → d.val < {hi} → ∀ a : Fin 120,\n"
            + "      5 * (15 * d.val - 21 + a.val + 1) < 77 * d.val →\n"
            + "      evenTable22S\n"
            + "          (2 * (((15 * d.val - 21 + a.val) + d.val : ℕ) : ℤ) + 23) ≠\n"
            + "        4 * evenTable22S (2 * ((15 * d.val - 21 + a.val : ℕ) : ℤ) + 23) := by decide\n"
            + NS_CLOSE
        )
        write(f"{PREFIX}FiniteStripS{shard}", body)

    proof = [
        "theorem even22_finite_strip :",
        "    ∀ d : Fin 250, 27 ≤ d.val → ∀ n : Fin 3834,",
        "      15 * d.val < n.val + 22 → 5 * (n.val + 1) < 77 * d.val →",
        "        evenTable22S (2 * ((n.val + d.val : ℕ) : ℤ) + 23) ≠",
        "          4 * evenTable22S (2 * (n.val : ℤ) + 23) := by",
        "  intro d hd n hlo hhi",
        "  let base := 15 * d.val - 21",
        "  let a := n.val - base",
        "  have hbase : base ≤ n.val := by dsimp [base]; omega",
        "  have hna : base + a = n.val := by dsimp [a]; omega",
        "  have halt : a < 120 := by dsimp [a, base] at *; omega",
        "  let fa : Fin 120 := ⟨a, halt⟩",
        "  have hainequality : 5 * (base + a + 1) < 77 * d.val := by",
        "    rw [hna]",
        "    exact hhi",
    ]
    for shard in range(shard_count - 1):
        hi = 35 + 8 * shard
        proof += [
            f"  by_cases h{shard} : d.val < {hi}",
            f"  · have h := even22_finite_strip_shard_{shard} d (by omega) h{shard} fa",
            "      (by dsimp [fa, base] at *; omega)",
            "    dsimp [fa, base] at h",
            "    rw [← hna]",
            "    exact h",
        ]
    proof += [
        f"  · have h := even22_finite_strip_shard_{shard_count - 1} d (by omega) "
        "d.isLt fa (by dsimp [fa, base] at *; omega)",
        "    dsimp [fa, base] at h",
        "    rw [← hna]",
        "    exact h",
    ]
    write(
        f"{PREFIX}FiniteStrip",
        f"import ErdosProblems.{PREFIX}FiniteStripS{shard_count - 1}\n\n"
        + NS_OPEN
        + "\n"
        + "\n".join(proof)
        + NS_CLOSE,
    )


def generate_core() -> None:
    d_def = polynomial("evenTable22D", verify.D_POLY)
    upper_expression = polynomial("unused", verify.NEGATIVE_UPPER, "v").split(
        ":=\n  ", 1
    )[1]
    core = f'''/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.{PREFIX}FiniteStrip
import ErdosProblems.Erdos686CenterComponentLogStrip

/-!
# Erdős 686: Archimedean and finite-strip core for the even row `k=22`

Gaps `22 ≤ d ≤ 26` use the quadratic strip.  Gaps `27 ≤ d ≤ 249`
are certified by exact ordinary-kernel tables.  For `d ≥ 250`, the centered
square-root polynomial reduces a solution to an odd candidate
`1 ≤ t ≤ {verify.CANDIDATE_BOUND}` with error `-33t`.
-/

namespace Erdos686
namespace Erdos686Variant

{d_def}

theorem even22_square_identity (W : ℤ) :
    evenTable22T W ^ 2 = {verify.SCALE ** 2} * evenTable22S W + evenTable22D W := by
  simp only [evenTable22T, evenTable22S, evenTable22D]
  ring

set_option maxHeartbeats 5000000 in
private lemma even22_centered_poly (W : ℤ) :
    evenTable22S W = centeredBlockProduct 22 W := by
  norm_num [centeredBlockProduct, evenTable22S,
    Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  ring

set_option maxHeartbeats 1000000 in
theorem even22_centered_bridge (x : ℕ) :
    evenTable22S (2 * (x : ℤ) + 23) =
      4194304 * (blockProduct 22 x : ℤ) := by
  rw [even22_centered_poly]
  convert centeredBlockProduct_center 22 x using 1 <;> norm_num

theorem even22_T_fixed_divisor (a : ℤ) :
    (33 : ℤ) ∣ evenTable22T (2 * a + 1) := by
  have hx : ((evenTable22T (2 * a + 1) : ℤ) : ZMod 33) = 0 := by
    have hall : ∀ y : ZMod 33, evenTable22T (2 * y + 1) = 0 := by decide
    simp only [evenTable22T] at hall ⊢
    push_cast
    exact hall (a : ZMod 33)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 33).mp hx

theorem even22_T_fixed_divisor_maximal (c : ℤ)
    (hc : ∀ a : ℤ, c ∣ evenTable22T (2 * a + 1)) : c ∣ 33 := by
  have h1 := hc 0
  have h3 := hc 1
  have hcomb := dvd_add (h1.mul_left (-72113493154))
    (h3.mul_left 39309729457)
  norm_num [evenTable22T] at hcomb
  exact hcomb

theorem even22_T_odd_at_odd (a : ℤ) :
    Odd (evenTable22T (2 * a + 1)) := by
  refine ⟨128 * (2 * a + 1) ^ 11 - 113344 * (2 * a + 1) ^ 9 +
      33804848 * (2 * a + 1) ^ 7 - 4055681080 * (2 * a + 1) ^ 5 +
      176248689155 * (2 * a + 1) ^ 3 -
      3027835453227 * (2 * a + 1) + a, ?_⟩
  simp only [evenTable22T]
  ring

private lemma even22_T_pos {{W : ℤ}} (hW : {verify.V_FLOOR} ≤ W) :
    0 < evenTable22T W := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ W = {verify.V_FLOOR} + a :=
    ⟨W - {verify.V_FLOOR}, by omega, by omega⟩
  simp only [evenTable22T]
  ring_nf
  positivity

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
private lemma even22_delta_lower {{v w : ℤ}} (hv : {verify.V_FLOOR} ≤ v)
    (hvw : v + 500 ≤ w) :
    0 < evenTable22D w + {verify.RUNGE_BOUND} * evenTable22T w +
      {2 * verify.RUNGE_BOUND} * evenTable22T v - 4 * evenTable22D v := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = {verify.V_FLOOR} + a :=
    ⟨v - {verify.V_FLOOR}, by omega, by omega⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℤ, 0 ≤ b ∧ w = {verify.V_FLOOR} + a + 500 + b :=
    ⟨w - ({verify.V_FLOOR} + a + 500), by omega, by omega⟩
  simp only [evenTable22D, evenTable22T]
  ring_nf
  positivity

set_option maxHeartbeats 10000000 in
private lemma even22_negative_upper {{v : ℤ}} (hv : {verify.V_FLOOR} ≤ v) :
    {upper_expression} < 0 := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℤ, 0 ≤ a ∧ v = {verify.V_FLOOR} + a :=
    ⟨v - {verify.V_FLOOR}, by omega, by omega⟩
  nlinarith [ha, pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
    pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7,
    pow_nonneg ha 8, pow_nonneg ha 9, pow_nonneg ha 10]

private lemma even22_delta_negative {{v w : ℤ}} (hv : {verify.V_FLOOR} ≤ v)
    (hw : 0 ≤ w) (hupper : 14 * w ≤ 15 * v) :
    evenTable22D w - 4 * evenTable22D v < 0 := by
  have h10 : (14 * w) ^ 10 ≤ (15 * v) ^ 10 :=
    pow_le_pow_left₀ (by omega) hupper 10
  have h6 : (14 * w) ^ 6 ≤ (15 * v) ^ 6 :=
    pow_le_pow_left₀ (by omega) hupper 6
  have h2 : (14 * w) ^ 2 ≤ (15 * v) ^ 2 :=
    pow_le_pow_left₀ (by omega) hupper 2
  have hw8 : 0 ≤ w ^ 8 := pow_nonneg hw 8
  have hw4 : 0 ≤ w ^ 4 := pow_nonneg hw 4
  have hneg := even22_negative_upper hv
  simp only [evenTable22D]
  ring_nf at h10 h6 h2
  nlinarith

private lemma lower_ratio_linearize_22
    {{N A B k n d : ℕ}}
    (hbracket : A ^ k < N * B ^ k)
    (hlo : N * (n + 1) ^ k ≤ (n + d + 1) ^ k) :
    A * (n + 1) < B * (n + d + 1) := by
  by_contra hnot
  have hle : B * (n + d + 1) ≤ A * (n + 1) := by omega
  have hpow := Nat.pow_le_pow_left hle k
  have hpow' : B ^ k * (n + d + 1) ^ k ≤
      A ^ k * (n + 1) ^ k := by
    simpa [Nat.mul_pow, mul_comm, mul_left_comm, mul_assoc] using hpow
  have hlomul : (N * B ^ k) * (n + 1) ^ k ≤
      B ^ k * (n + d + 1) ^ k := by
    calc
      (N * B ^ k) * (n + 1) ^ k =
          B ^ k * (N * (n + 1) ^ k) := by ring
      _ ≤ B ^ k * (n + d + 1) ^ k := Nat.mul_le_mul_left _ hlo
  have hbase : 0 < (n + 1) ^ k := Nat.pow_pos (by omega)
  have hstrict : A ^ k * (n + 1) ^ k <
      (N * B ^ k) * (n + 1) ^ k :=
    (Nat.mul_lt_mul_right hbase).2 hbracket
  omega

theorem even22_small_gap_impossible {{n d : ℕ}} (hd : 22 ≤ d)
    (hd249 : d ≤ 249)
    (heq : blockProduct 22 (n + d) = 4 * blockProduct 22 n) : False := by
  by_cases hd26 : d ≤ 26
  · exact (no_four_solution_of_quadratic_strip
      (k := 22) (n := n) (d := d) (by norm_num) hd (by omega)) heq
  · obtain ⟨hup, hlo⟩ := ratio_window_four_nat heq
    have hlin :=
      ratio_window_linearize_of_pow_bracket (N := 4) (A := 16) (B := 15)
        (k := 22) (n := n) (d := d) (by norm_num) (by norm_num) hup
    have hlow := lower_ratio_linearize_22 (N := 4) (A := 82) (B := 77)
      (k := 22) (n := n) (d := d) (by norm_num) hlo
    have hn3834 : n < 3834 := by omega
    let fd : Fin 250 := ⟨d, by omega⟩
    let fn : Fin 3834 := ⟨n, hn3834⟩
    have hstrip := even22_finite_strip fd (by dsimp [fd]; omega) fn
      (by dsimp [fd, fn]; omega) (by dsimp [fd, fn]; omega)
    have hZ : ((blockProduct 22 (n + d) : ℕ) : ℤ) =
        4 * ((blockProduct 22 n : ℕ) : ℤ) := by exact_mod_cast heq
    have hs1 := even22_centered_bridge (n + d)
    have hs2 := even22_centered_bridge n
    dsimp [fd, fn] at hstrip
    push_cast at hs1 hs2
    apply hstrip
    change evenTable22S (2 * ((n : ℤ) + (d : ℤ)) + 23) =
      4 * evenTable22S (2 * (n : ℤ) + 23)
    rw [hs1, hs2, hZ]
    ring

private lemma even22_quotient_candidate {{m q : ℤ}}
    (hmgt : -{verify.RUNGE_BOUND} < m) (hmneg : m < 0)
    (hq : m = 33 * q) :
    ∃ t : ℕ, m = -(33 * (t : ℤ)) ∧ 1 ≤ t ∧
      t ≤ {verify.CANDIDATE_BOUND} := by
  have hqlo : -{verify.CANDIDATE_BOUND + 1} < q := by
    rw [hq] at hmgt
    omega
  have hqhi : q < 0 := by
    rw [hq] at hmneg
    omega
  let t : ℕ := (-q).toNat
  have hqnonneg : 0 ≤ -q := by omega
  have htcast : (t : ℤ) = -q := by
    simp [t, Int.toNat_of_nonneg hqnonneg]
  have htpos : 1 ≤ t := by omega
  have htbound : t ≤ {verify.CANDIDATE_BOUND} := by omega
  have hmt : m = -(33 * (t : ℤ)) := by rw [hq, htcast]; ring
  exact ⟨t, hmt, htpos, htbound⟩

/-- The exact large-gap k=22 Archimedean reduction consumed by the packed cover. -/
theorem even22_large_gap_reduction {{n d : ℕ}} (hd250 : 250 ≤ d)
    (heq : blockProduct 22 (n + d) = 4 * blockProduct 22 n) :
    ∃ w v : ℤ, ∃ t : ℕ,
      evenTable22S w = 4 * evenTable22S v ∧
      -(33 * (t : ℤ)) = evenTable22T w - 2 * evenTable22T v ∧
      1 ≤ t ∧ t ≤ {verify.CANDIDATE_BOUND} ∧ Odd t := by
  obtain ⟨hup, _hlo⟩ := ratio_window_four_nat heq
  have hlin :=
    ratio_window_linearize_of_pow_bracket (N := 4) (A := 16) (B := 15)
      (k := 22) (n := n) (d := d) (by norm_num) (by norm_num) hup
  have hn3729 : 3729 ≤ n := by omega
  have hZ : ((blockProduct 22 (n + d) : ℕ) : ℤ) =
      4 * ((blockProduct 22 n : ℕ) : ℤ) := by exact_mod_cast heq
  let w : ℤ := 2 * ((n : ℤ) + (d : ℤ)) + 23
  let v : ℤ := 2 * (n : ℤ) + 23
  have hv : {verify.V_FLOOR} ≤ v := by dsimp [v]; omega
  have hw : {verify.V_FLOOR} ≤ w := by dsimp [w]; omega
  have hvw : v + 500 ≤ w := by dsimp [v, w]; omega
  have hupper : 14 * w ≤ 15 * v := by dsimp [v, w]; omega
  have hs1 := even22_centered_bridge (n + d)
  have hs2 := even22_centered_bridge n
  have hcw : 2 * ((n + d : ℕ) : ℤ) + 23 = w := by dsimp [w]
  have hcv : 2 * (n : ℤ) + 23 = v := by rfl
  rw [hcw] at hs1
  rw [hcv] at hs2
  have hS : evenTable22S w = 4 * evenTable22S v := by
    rw [hs1, hs2, hZ]
    ring
  let m : ℤ := evenTable22T w - 2 * evenTable22T v
  let X : ℤ := evenTable22T w + 2 * evenTable22T v
  have hTw : 0 < evenTable22T w := even22_T_pos hw
  have hTv : 0 < evenTable22T v := even22_T_pos hv
  have hXpos : 0 < X := by dsimp [X]; linarith
  have hmdef : m = evenTable22T w - 2 * evenTable22T v := rfl
  have hmX : m * X = evenTable22D w - 4 * evenTable22D v := by
    dsimp [m, X]
    calc
      (evenTable22T w - 2 * evenTable22T v) *
          (evenTable22T w + 2 * evenTable22T v) =
          evenTable22T w ^ 2 - 4 * evenTable22T v ^ 2 := by ring
      _ = ({verify.SCALE ** 2} * evenTable22S w + evenTable22D w) -
          4 * ({verify.SCALE ** 2} * evenTable22S v + evenTable22D v) := by
        rw [even22_square_identity, even22_square_identity]
      _ = evenTable22D w - 4 * evenTable22D v := by rw [hS]; ring
  have hdeltaNeg := even22_delta_negative hv (by omega) hupper
  have hdeltaLower :
      -{verify.RUNGE_BOUND} * X < evenTable22D w - 4 * evenTable22D v := by
    have h := even22_delta_lower hv hvw
    dsimp [X]
    linarith
  have hmneg : m < 0 := by
    by_contra hnot
    have hnonneg := mul_nonneg (not_lt.mp hnot) hXpos.le
    rw [hmX] at hnonneg
    linarith
  have hmgt : -{verify.RUNGE_BOUND} < m := by
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_right (not_lt.mp hnot) hXpos.le
    rw [hmX] at hmul
    linarith
  have hmw := even22_T_fixed_divisor ((n : ℤ) + (d : ℤ) + 11)
  have hmv := even22_T_fixed_divisor ((n : ℤ) + 11)
  have hwodd : 2 * ((n : ℤ) + (d : ℤ) + 11) + 1 = w := by
    dsimp [w]
    ring
  have hvodd : 2 * ((n : ℤ) + 11) + 1 = v := by
    dsimp [v]
    ring
  rw [hwodd] at hmw
  rw [hvodd] at hmv
  have hmdiv : (33 : ℤ) ∣ m := by
    dsimp [m]
    exact dvd_sub hmw (hmv.mul_left 2)
  obtain ⟨q, hq⟩ := hmdiv
  obtain ⟨t, hmt, htpos, htbound⟩ :=
    even22_quotient_candidate hmgt hmneg hq
  have htarget : -(33 * (t : ℤ)) = evenTable22T w - 2 * evenTable22T v := by
    rw [← hmdef, hmt]
  have hmwOdd : Odd (evenTable22T w) := by
    rw [← hwodd]
    exact even22_T_odd_at_odd ((n : ℤ) + (d : ℤ) + 11)
  have hmOdd : Odd m := by
    dsimp [m]
    exact hmwOdd.sub_even (even_two_mul (evenTable22T v))
  have hprodOdd : Odd ((33 : ℤ) * (t : ℤ)) := by
    simpa [hmt] using hmOdd.neg
  have htOdd : Odd t := by
    rcases Nat.even_or_odd t with htEven | htOdd
    · obtain ⟨u, hu⟩ := htEven
      have hucast : (t : ℤ) = 2 * (u : ℤ) := by
        push_cast
        omega
      obtain ⟨z, hz⟩ := hprodOdd
      rw [hucast] at hz
      omega
    · exact htOdd
  exact ⟨w, v, t, hS, htarget, htpos, htbound, htOdd⟩

/-- Conditional row closure from any contradiction for the exact odd candidate surface. -/
theorem no_gap_solution_four_even_twentytwo_of_large_obstruction
    (hobstruct : ∀ {{w v : ℤ}} {{t : ℕ}},
      evenTable22S w = 4 * evenTable22S v →
      -(33 * (t : ℤ)) = evenTable22T w - 2 * evenTable22T v →
      1 ≤ t → t ≤ {verify.CANDIDATE_BOUND} → Odd t → False)
    {{n d : ℕ}} (hd : 22 ≤ d) :
    blockProduct 22 (n + d) ≠ 4 * blockProduct 22 n := by
  intro heq
  by_cases hd250 : 250 ≤ d
  · obtain ⟨w, v, t, hS, htarget, htpos, htbound, htOdd⟩ :=
      even22_large_gap_reduction hd250 heq
    exact hobstruct hS htarget htpos htbound htOdd
  · exact even22_small_gap_impossible hd (by omega) heq

end Erdos686Variant
end Erdos686
'''
    write(f"{PREFIX}Core", core)


def main() -> None:
    verify.audit()
    for module in (f"{PREFIX}Defs", f"{PREFIX}FiniteStrip", f"{PREFIX}Core"):
        path = OUT / f"{module}.lean"
        if path.exists():
            path.unlink()
    for path in OUT.glob(f"{PREFIX}FiniteStripS*.lean"):
        path.unlink()
    generate_defs()
    generate_finite_strip()
    generate_core()
    print("generated isolated k=22 Archimedean modules")


if __name__ == "__main__":
    main()
