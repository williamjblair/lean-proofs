/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686QuotientConfinement

/-!
# Erdős 686: convergent (Farey/Stern–Brocot) descent machinery

Shared, `k`-generic infrastructure for the centered-Thue/convergent pipeline
that closes `N = 4` gap solutions `blockProduct k (n+d) = 4 * blockProduct k n`
for odd `k` up to an explicit astronomical gap bound
(`compute/theory/k5_third_row_note.md` §6, `compute/theory/oddk_7/note.md`,
`compute/theory/odd_k_thue_synthesis.md`).

Per-`k` input (provided by the instance modules, e.g. `Erdos686FiveThue`):
an exact *Thue window*

  `cden * |X^(e+2) - N * Y^(e+2)| ≤ cnum * Y^e`     (`e = k - 2`),

valid for every solution in centered coordinates `X, Y` with `Ylo ≤ Y`
(derived from the equation together with the banked ratio window of
`Erdos686QuotientConfinement`), plus a Boolean refuter `f` for the exact
centered equation.

The machinery confines `X/Y` by a pure-integer Stern–Brocot descent; there
are **no real numbers, no Mathlib continued fractions, and no
Legendre/Fatou black box** anywhere.  The classical confinement statements
(Legendre `C < 1/2`, Fatou `C < 1`, Worley/quasi-convergents `C ≥ 1`;
compare `compute/theory/oddk_9/note.md` §3) are all subsumed: the Thue
constant `cnum/cden` enters only through the Boolean side conditions of the
certificate, so the same machinery serves every odd `k ∈ {5, …, 15}`.

* `farey_mediant_lower` — the mediant lemma: if `X/Y` lies strictly inside
  a Farey pair `a/b < c/d` (`c*b = a*d + 1`) then `Y ≥ b + d`.  The proof
  is the identity `Y = d*(X*b - Y*a) + b*(Y*c - X*d)` in additive form.
* `farey_side_below` / `farey_side_above` — side repulsion: a fraction
  `u/v` with exact side certificate `u^K ⋚ N*v^K` (`K = e + 2`) repels
  `X/Y` once `cnum * v^K < cden * |u^K - N*v^K| * Y^2`, by comparing
  `(Y*u)^K` with `(X*v)^K` through the Thue window.
* `farey_eq_mediant` / `farey_multiple_bound` — if `X/Y` *equals* a
  mediant `A/B` then `(X, Y) = g*(A, B)` with
  `cden * g^2 * |A^K - N*B^K| ≤ cnum * B^e`; each such candidate pair is
  refuted by the exact centered equation via `f`.

`FareyTree` is the shape of a finite descent certificate, `fareyCheck` its
Boolean kernel checker, and `fareyCheck_sound` the soundness theorem: a
passing certificate rooted at a Farey pair strictly enclosing `X/Y` refutes
every solution with `Ylo ≤ Y ≤ Ymax`.  Certificates are generated and
pre-verified (including a cross-check against the campaign convergent data
`compute/artifacts/thue_convergents_k*.json`) by
`compute/erdos686_thue_gen_lean.py`.
-/

namespace Erdos686

namespace Erdos686Variant

/--
Tail proposition for the `N = 4` gap problem at width `k`: no gap solution
with `d ≥ B`.  The convergent pipeline reduces the unbounded-`d` statement
to this tail for an astronomically large `B`.
-/
def NoLargeGapSolutionFour (k B : ℕ) : Prop :=
  ∀ n d : ℕ, B ≤ d → blockProduct k (n + d) ≠ 4 * blockProduct k n

/--
Certificate tree for the Stern–Brocot descent.  Each node refers to a Farey
pair `a/b < c/d` (`c*b = a*d + 1`) maintained by the checker:

* `high` — `Ymax < b + d`: the mediant lemma pushes `Y` above `Ymax`;
* `kill` — one endpoint's exact side certificate repels `X/Y` out of the
  (strict) interval once `Y ≥ max (b+d) Ylo`;
* `node gmax l r` — split at the mediant `(a+c)/(b+d)`: the equality case
  `X/Y = (a+c)/(b+d)` is confined to multiples `g ≤ gmax`, each refuted by
  the exact equation; `l`, `r` continue on the two subintervals.
-/
inductive FareyTree : Type
  | high : FareyTree
  | kill : FareyTree
  | node (gmax : ℕ) (l r : FareyTree) : FareyTree

/--
Boolean checker for a `FareyTree` certificate against the Farey pair
`a/b < c/d`.  All arithmetic is on ℕ literals, so the kernel evaluates it
with GMP; `decide` on a generated certificate is the only computational
step of the whole pipeline.
-/
def fareyCheck (N cnum cden e Ylo Ymax : ℕ) (f : ℕ → ℕ → Bool) :
    ℕ → ℕ → ℕ → ℕ → FareyTree → Bool
  | _, b, _, d, .high => decide (Ymax < b + d)
  | a, b, c, d, .kill =>
      (decide (c ^ (e + 2) < N * d ^ (e + 2)) &&
        decide (cnum * d ^ (e + 2) <
          cden * (N * d ^ (e + 2) - c ^ (e + 2)) * max (b + d) Ylo ^ 2)) ||
      (decide (N * b ^ (e + 2) < a ^ (e + 2)) &&
        decide (cnum * b ^ (e + 2) <
          cden * (a ^ (e + 2) - N * b ^ (e + 2)) * max (b + d) Ylo ^ 2))
  | a, b, c, d, .node gmax l r =>
      decide (cnum * (b + d) ^ e <
        cden * (gmax + 1) ^ 2 *
          ((a + c) ^ (e + 2) - N * (b + d) ^ (e + 2) +
            (N * (b + d) ^ (e + 2) - (a + c) ^ (e + 2)))) &&
      ((List.range gmax).all fun i =>
        decide ((i + 1) * (b + d) < Ylo) || decide (Ymax < (i + 1) * (b + d)) ||
          f ((i + 1) * (a + c)) ((i + 1) * (b + d))) &&
      fareyCheck N cnum cden e Ylo Ymax f a b (a + c) (b + d) l &&
      fareyCheck N cnum cden e Ylo Ymax f (a + c) (b + d) c d r

/--
**Mediant lemma.**  If `X/Y` lies strictly inside the Farey pair
`a/b < c/d` (`c*b = a*d + 1`), then `Y ≥ b + d`.  Proof: multiply the two
strict inequalities by `d` resp. `b` and use
`b*(Y*c) = d*(Y*a) + Y` (the determinant identity).
-/
lemma farey_mediant_lower {a b c d X Y : ℕ}
    (hdet : c * b = a * d + 1)
    (hlow : Y * a + 1 ≤ X * b) (hhigh : X * d + 1 ≤ Y * c) :
    b + d ≤ Y := by
  have h1 : d * (Y * a + 1) ≤ d * (X * b) := mul_le_mul_right hlow d
  have h2 : b * (X * d + 1) ≤ b * (Y * c) := mul_le_mul_right hhigh b
  have h3 : b * (Y * c) = d * (Y * a) + Y := by
    calc b * (Y * c) = Y * (c * b) := by ring
      _ = Y * (a * d + 1) := by rw [hdet]
      _ = d * (Y * a) + Y := by ring
  have h4 : b * (X * d + 1) = d * (X * b) + b := by ring
  have h5 : d * (Y * a + 1) = d * (Y * a) + d := by ring
  linarith

/--
**Side repulsion, from below.**  If `u/v` lies strictly below the `K`-th
root of `N` (`u^K + D = N*v^K`, `K = e + 2`), the lower Thue window holds
at `(X, Y)`, and the gap certificate `cnum * v^K < cden * D * Y^2` holds,
then `X/Y > u/v` strictly.  Entirely in ℕ: compare `(Y*u)^K` with
`(X*v)^K`.
-/
lemma farey_side_below {N cnum cden e u v D X Y : ℕ} (hY1 : 1 ≤ Y)
    (hD : u ^ (e + 2) + D = N * v ^ (e + 2))
    (hthue : cden * (N * Y ^ (e + 2)) ≤ cden * X ^ (e + 2) + cnum * Y ^ e)
    (hgap : cnum * v ^ (e + 2) < cden * D * Y ^ 2) :
    Y * u < X * v := by
  have hYe : 0 < Y ^ e := pow_pos (by omega) e
  have h1 : v ^ (e + 2) * (cden * (N * Y ^ (e + 2))) ≤
      v ^ (e + 2) * (cden * X ^ (e + 2) + cnum * Y ^ e) :=
    mul_le_mul_right hthue _
  have h2 : cden * (Y * u) ^ (e + 2) + cden * D * Y ^ (e + 2) =
      v ^ (e + 2) * (cden * (N * Y ^ (e + 2))) := by
    calc cden * (Y * u) ^ (e + 2) + cden * D * Y ^ (e + 2)
        = cden * Y ^ (e + 2) * (u ^ (e + 2) + D) := by rw [mul_pow]; ring
      _ = cden * Y ^ (e + 2) * (N * v ^ (e + 2)) := by rw [hD]
      _ = v ^ (e + 2) * (cden * (N * Y ^ (e + 2))) := by ring
  have h3 : v ^ (e + 2) * (cden * X ^ (e + 2) + cnum * Y ^ e) =
      cden * (X * v) ^ (e + 2) + cnum * v ^ (e + 2) * Y ^ e := by
    rw [mul_pow]; ring
  have h4 : cnum * v ^ (e + 2) * Y ^ e < cden * D * Y ^ (e + 2) := by
    calc cnum * v ^ (e + 2) * Y ^ e
        < cden * D * Y ^ 2 * Y ^ e := mul_lt_mul_of_pos_right hgap hYe
      _ = cden * D * Y ^ (e + 2) := by rw [pow_add]; ring
  have h5 : cden * (Y * u) ^ (e + 2) < cden * (X * v) ^ (e + 2) := by
    have hle : cden * (Y * u) ^ (e + 2) + cden * D * Y ^ (e + 2) ≤
        cden * (X * v) ^ (e + 2) + cnum * v ^ (e + 2) * Y ^ e := by
      calc cden * (Y * u) ^ (e + 2) + cden * D * Y ^ (e + 2)
          = v ^ (e + 2) * (cden * (N * Y ^ (e + 2))) := h2
        _ ≤ v ^ (e + 2) * (cden * X ^ (e + 2) + cnum * Y ^ e) := h1
        _ = cden * (X * v) ^ (e + 2) + cnum * v ^ (e + 2) * Y ^ e := h3
    linarith
  have h6 : (Y * u) ^ (e + 2) < (X * v) ^ (e + 2) :=
    Nat.lt_of_mul_lt_mul_left h5
  by_contra hnot
  exact absurd h6 (Nat.not_lt.mpr (Nat.pow_le_pow_left (Nat.le_of_not_lt hnot) _))

/--
**Side repulsion, from above.**  If `u/v` lies strictly above the `K`-th
root of `N` (`N*v^K + D = u^K`), the upper Thue window holds at `(X, Y)`,
and the gap certificate holds, then `X/Y < u/v` strictly.
-/
lemma farey_side_above {N cnum cden e u v D X Y : ℕ} (hY1 : 1 ≤ Y)
    (hD : N * v ^ (e + 2) + D = u ^ (e + 2))
    (hthue : cden * X ^ (e + 2) ≤ cden * (N * Y ^ (e + 2)) + cnum * Y ^ e)
    (hgap : cnum * v ^ (e + 2) < cden * D * Y ^ 2) :
    X * v < Y * u := by
  have hYe : 0 < Y ^ e := pow_pos (by omega) e
  have h1 : v ^ (e + 2) * (cden * X ^ (e + 2)) ≤
      v ^ (e + 2) * (cden * (N * Y ^ (e + 2)) + cnum * Y ^ e) :=
    mul_le_mul_right hthue _
  have h2 : v ^ (e + 2) * (cden * X ^ (e + 2)) = cden * (X * v) ^ (e + 2) := by
    rw [mul_pow]; ring
  have h3 : v ^ (e + 2) * (cden * (N * Y ^ (e + 2)) + cnum * Y ^ e) +
      cden * D * Y ^ (e + 2) =
      cden * (Y * u) ^ (e + 2) + cnum * v ^ (e + 2) * Y ^ e := by
    calc v ^ (e + 2) * (cden * (N * Y ^ (e + 2)) + cnum * Y ^ e) +
        cden * D * Y ^ (e + 2)
        = cden * Y ^ (e + 2) * (N * v ^ (e + 2) + D) +
            cnum * v ^ (e + 2) * Y ^ e := by ring
      _ = cden * Y ^ (e + 2) * u ^ (e + 2) + cnum * v ^ (e + 2) * Y ^ e := by
          rw [hD]
      _ = cden * (Y * u) ^ (e + 2) + cnum * v ^ (e + 2) * Y ^ e := by
          rw [mul_pow]; ring
  have h4 : cnum * v ^ (e + 2) * Y ^ e < cden * D * Y ^ (e + 2) := by
    calc cnum * v ^ (e + 2) * Y ^ e
        < cden * D * Y ^ 2 * Y ^ e := mul_lt_mul_of_pos_right hgap hYe
      _ = cden * D * Y ^ (e + 2) := by rw [pow_add]; ring
  have h5 : cden * (X * v) ^ (e + 2) < cden * (Y * u) ^ (e + 2) := by
    linarith [h1, h2, h3, h4]
  have h6 : (X * v) ^ (e + 2) < (Y * u) ^ (e + 2) :=
    Nat.lt_of_mul_lt_mul_left h5
  by_contra hnot
  exact absurd h6 (Nat.not_lt.mpr (Nat.pow_le_pow_left (Nat.le_of_not_lt hnot) _))

/--
**Equality case at the mediant.**  If `X/Y` equals the mediant of the Farey
pair `a/b < c/d` and lies strictly above `a/b`, then `(X, Y)` is a positive
multiple of `(a+c, b+d)` (the mediant of a Farey pair is in lowest terms).
-/
lemma farey_eq_mediant {a b c d X Y : ℕ}
    (hdet : c * b = a * d + 1) (hbd : 1 ≤ b + d)
    (heq : X * (b + d) = Y * (a + c))
    (hlow : Y * a + 1 ≤ X * b) :
    ∃ g : ℕ, 1 ≤ g ∧ X = g * (a + c) ∧ Y = g * (b + d) := by
  obtain ⟨g, hg⟩ := Nat.le.dest (Nat.le_of_succ_le hlow)
  have hg1 : 1 ≤ g := by linarith [hg, hlow]
  have hkey : (b + d) * (X * b) = (b + d) * (Y * a) + Y := by
    calc (b + d) * (X * b) = b * (X * (b + d)) := by ring
      _ = b * (Y * (a + c)) := by rw [heq]
      _ = Y * (a * b) + Y * (c * b) := by ring
      _ = Y * (a * b) + Y * (a * d + 1) := by rw [hdet]
      _ = (b + d) * (Y * a) + Y := by ring
  have hYg : Y = g * (b + d) := by
    have h1 : (b + d) * (Y * a) + (b + d) * g = (b + d) * (Y * a) + Y := by
      calc (b + d) * (Y * a) + (b + d) * g = (b + d) * (Y * a + g) := by ring
        _ = (b + d) * (X * b) := by rw [hg]
        _ = (b + d) * (Y * a) + Y := hkey
    have h2 : (b + d) * g = Y := Nat.add_left_cancel h1
    rw [Nat.mul_comm g (b + d)]
    exact h2.symm
  have hXg : X = g * (a + c) := by
    have h2 : (b + d) * X = (b + d) * (g * (a + c)) := by
      calc (b + d) * X = X * (b + d) := by ring
        _ = Y * (a + c) := heq
        _ = g * (b + d) * (a + c) := by rw [hYg]
        _ = (b + d) * (g * (a + c)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hbd h2
  exact ⟨g, hg1, hXg, hYg⟩

/--
**Multiple bound at the mediant.**  If `(X, Y) = g*(A, B)` satisfies the
two-sided Thue window and `D = |A^K - N*B^K|` (given by a signed
decomposition), then `cden * g^2 * D ≤ cnum * B^e`; combined with the
certificate inequality `cnum * B^e < cden * (gmax+1)^2 * D` this pins
`g ≤ gmax`.
-/
lemma farey_multiple_bound {N cnum cden e A B D g gmax : ℕ} (hg : 1 ≤ g)
    (hDdef : A ^ (e + 2) + D = N * B ^ (e + 2) ∨
      N * B ^ (e + 2) + D = A ^ (e + 2))
    (hlo : cden * (N * (g * B) ^ (e + 2)) ≤
      cden * (g * A) ^ (e + 2) + cnum * (g * B) ^ e)
    (hhi : cden * (g * A) ^ (e + 2) ≤
      cden * (N * (g * B) ^ (e + 2)) + cnum * (g * B) ^ e)
    (hcert : cnum * B ^ e < cden * (gmax + 1) ^ 2 * D) :
    g ≤ gmax := by
  have hge : 0 < g ^ e := pow_pos hg e
  have e2 : cnum * (g * B) ^ e = g ^ e * (cnum * B ^ e) := by
    rw [mul_pow]; ring
  have hkey : g ^ e * (cden * (g ^ 2 * D)) ≤ g ^ e * (cnum * B ^ e) := by
    rcases hDdef with hD | hD
    · have e1 : cden * (N * (g * B) ^ (e + 2)) =
          cden * (g * A) ^ (e + 2) + g ^ e * (cden * (g ^ 2 * D)) := by
        calc cden * (N * (g * B) ^ (e + 2))
            = cden * g ^ (e + 2) * (N * B ^ (e + 2)) := by rw [mul_pow]; ring
          _ = cden * g ^ (e + 2) * (A ^ (e + 2) + D) := by rw [hD]
          _ = cden * (g * A) ^ (e + 2) + g ^ e * (cden * (g ^ 2 * D)) := by
              rw [mul_pow, pow_add]; ring
      rw [e1, e2] at hlo
      exact le_of_add_le_add_left hlo
    · have e1 : cden * (g * A) ^ (e + 2) =
          cden * (N * (g * B) ^ (e + 2)) + g ^ e * (cden * (g ^ 2 * D)) := by
        calc cden * (g * A) ^ (e + 2)
            = cden * g ^ (e + 2) * A ^ (e + 2) := by rw [mul_pow]; ring
          _ = cden * g ^ (e + 2) * (N * B ^ (e + 2) + D) := by rw [← hD]
          _ = cden * (N * (g * B) ^ (e + 2)) + g ^ e * (cden * (g ^ 2 * D)) := by
              rw [mul_pow, pow_add]; ring
      rw [e1, e2] at hhi
      exact le_of_add_le_add_left hhi
  have hkey2 : cden * (g ^ 2 * D) ≤ cnum * B ^ e :=
    Nat.le_of_mul_le_mul_left hkey hge
  have hlt : g ^ 2 * (cden * D) < (gmax + 1) ^ 2 * (cden * D) := by
    calc g ^ 2 * (cden * D) = cden * (g ^ 2 * D) := by ring
      _ ≤ cnum * B ^ e := hkey2
      _ < cden * (gmax + 1) ^ 2 * D := hcert
      _ = (gmax + 1) ^ 2 * (cden * D) := by ring
  have hg2 : g ^ 2 < (gmax + 1) ^ 2 :=
    lt_of_mul_lt_mul_right hlt (Nat.zero_le _)
  by_contra hnot
  exact absurd hg2
    (Nat.not_lt.mpr (Nat.pow_le_pow_left (Nat.succ_le_of_lt (Nat.lt_of_not_le hnot)) 2))

/--
**Soundness of the certificate checker.**  Given a solution predicate `Sol`
with a Boolean refuter `f` and a two-sided Thue window valid on
`Ylo ≤ Y ≤ Ymax`, a passing `fareyCheck` certificate rooted at a Farey pair
`a/b < c/d` refutes every `(X, Y)` with `Sol X Y`, `Ylo ≤ Y ≤ Ymax`, and
`X/Y` strictly inside the pair.
-/
theorem fareyCheck_sound
    {N cnum cden e Ylo Ymax : ℕ} {f : ℕ → ℕ → Bool} {Sol : ℕ → ℕ → Prop}
    (hf : ∀ X Y : ℕ, f X Y = true → ¬ Sol X Y)
    (hthue : ∀ X Y : ℕ, Sol X Y → Ylo ≤ Y → Y ≤ Ymax →
      cden * (N * Y ^ (e + 2)) ≤ cden * X ^ (e + 2) + cnum * Y ^ e ∧
        cden * X ^ (e + 2) ≤ cden * (N * Y ^ (e + 2)) + cnum * Y ^ e)
    {X Y : ℕ} (hSol : Sol X Y) (hYlo : Ylo ≤ Y) (hYmax : Y ≤ Ymax)
    (hY1 : 1 ≤ Y) :
    ∀ (t : FareyTree) (a b c d : ℕ),
      c * b = a * d + 1 →
      fareyCheck N cnum cden e Ylo Ymax f a b c d t = true →
      Y * a + 1 ≤ X * b → X * d + 1 ≤ Y * c → False := by
  intro t
  induction t with
  | high =>
      intro a b c d hdet hcheck hlow hhigh
      have hbd := farey_mediant_lower hdet hlow hhigh
      simp only [fareyCheck, decide_eq_true_eq] at hcheck
      omega
  | kill =>
      intro a b c d hdet hcheck hlow hhigh
      have hbd := farey_mediant_lower hdet hlow hhigh
      have hLY : max (b + d) Ylo ≤ Y := max_le hbd hYlo
      have hL2 : max (b + d) Ylo ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hLY 2
      simp only [fareyCheck, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      obtain ⟨hthue_lo, hthue_hi⟩ := hthue X Y hSol hYlo hYmax
      rcases hcheck with ⟨hside, hgap⟩ | ⟨hside, hgap⟩
      · -- upper endpoint `c/d` lies below the root: it repels `X/Y` upwards
        have hD : c ^ (e + 2) + (N * d ^ (e + 2) - c ^ (e + 2)) =
            N * d ^ (e + 2) := Nat.add_sub_cancel' (Nat.le_of_lt hside)
        have hgapY : cnum * d ^ (e + 2) <
            cden * (N * d ^ (e + 2) - c ^ (e + 2)) * Y ^ 2 :=
          lt_of_lt_of_le hgap (mul_le_mul_right hL2 _)
        have hrep := farey_side_below hY1 hD hthue_lo hgapY
        exact absurd hrep (Nat.lt_asymm (Nat.lt_of_succ_le hhigh))
      · -- lower endpoint `a/b` lies above the root: it repels `X/Y` downwards
        have hD : N * b ^ (e + 2) + (a ^ (e + 2) - N * b ^ (e + 2)) =
            a ^ (e + 2) := Nat.add_sub_cancel' (Nat.le_of_lt hside)
        have hgapY : cnum * b ^ (e + 2) <
            cden * (a ^ (e + 2) - N * b ^ (e + 2)) * Y ^ 2 :=
          lt_of_lt_of_le hgap (mul_le_mul_right hL2 _)
        have hrep := farey_side_above hY1 hD hthue_hi hgapY
        exact absurd hrep (Nat.lt_asymm (Nat.lt_of_succ_le hlow))
  | node gmax l r ihl ihr =>
      intro a b c d hdet hcheck hlow hhigh
      have hdetL : (a + c) * b = a * (b + d) + 1 := by
        calc (a + c) * b = a * b + c * b := by ring
          _ = a * b + (a * d + 1) := by rw [hdet]
          _ = a * (b + d) + 1 := by ring
      have hdetR : c * (b + d) = (a + c) * d + 1 := by
        calc c * (b + d) = c * b + c * d := by ring
          _ = a * d + 1 + c * d := by rw [hdet]
          _ = (a + c) * d + 1 := by ring
      have hbd1 : 1 ≤ b + d := by
        rcases Nat.eq_zero_or_pos (b + d) with h0 | h
        · exfalso
          have hb0 : b = 0 := by omega
          have hd0 : d = 0 := by omega
          rw [hb0, hd0] at hdet
          simp at hdet
        · exact h
      simp only [fareyCheck, Bool.and_eq_true, Bool.or_eq_true,
        List.all_eq_true, List.mem_range, decide_eq_true_eq] at hcheck
      obtain ⟨⟨⟨hgcert, hcand⟩, hcl⟩, hcr⟩ := hcheck
      rcases Nat.lt_trichotomy (X * (b + d)) (Y * (a + c)) with hlt | heqm | hgt
      · -- strictly left of the mediant: recurse on the left subinterval
        exact ihl a b (a + c) (b + d) hdetL hcl hlow (Nat.succ_le_of_lt hlt)
      · -- equality at the mediant: multiple of `(a+c, b+d)`, refuted by `f`
        obtain ⟨g, hg1, hX, hY'⟩ := farey_eq_mediant hdet hbd1 heqm hlow
        obtain ⟨hthue_lo, hthue_hi⟩ := hthue X Y hSol hYlo hYmax
        rw [hX, hY'] at hthue_lo hthue_hi
        have hgle : g ≤ gmax := by
          rcases Nat.lt_trichotomy ((a + c) ^ (e + 2))
              (N * (b + d) ^ (e + 2)) with hs | hs | hs
          · have hz : (a + c) ^ (e + 2) - N * (b + d) ^ (e + 2) = 0 :=
              Nat.sub_eq_zero_of_le (Nat.le_of_lt hs)
            rw [hz, Nat.zero_add] at hgcert
            exact farey_multiple_bound hg1
              (Or.inl (Nat.add_sub_cancel' (Nat.le_of_lt hs)))
              hthue_lo hthue_hi hgcert
          · have hz1 : (a + c) ^ (e + 2) - N * (b + d) ^ (e + 2) = 0 :=
              Nat.sub_eq_zero_of_le (Nat.le_of_eq hs)
            have hz2 : N * (b + d) ^ (e + 2) - (a + c) ^ (e + 2) = 0 :=
              Nat.sub_eq_zero_of_le (Nat.le_of_eq hs.symm)
            rw [hz1, hz2] at hgcert
            simp at hgcert
          · have hz : N * (b + d) ^ (e + 2) - (a + c) ^ (e + 2) = 0 :=
              Nat.sub_eq_zero_of_le (Nat.le_of_lt hs)
            rw [hz, Nat.add_zero] at hgcert
            exact farey_multiple_bound hg1
              (Or.inr (Nat.add_sub_cancel' (Nat.le_of_lt hs)))
              hthue_lo hthue_hi hgcert
        have hc := hcand (g - 1) (by omega)
        rw [show g - 1 + 1 = g by omega] at hc
        rcases hc with (hskip | hskip) | hfx
        · rw [← hY'] at hskip; omega
        · rw [← hY'] at hskip; omega
        · rw [← hX, ← hY'] at hfx
          exact hf X Y hfx hSol
      · -- strictly right of the mediant: recurse on the right subinterval
        exact ihr (a + c) (b + d) c d hdetR hcr (Nat.succ_le_of_lt hgt) hhigh

end Erdos686Variant

end Erdos686
