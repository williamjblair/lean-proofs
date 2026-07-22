import ErdosProblems.Erdos686.EvenK.K22.Table.Tables

namespace Erdos686.Erdos686Variant

/-- Repeat a low-bit-first residue mask by balanced doubling. -/
def even22PeriodicPowMask (w p pattern : ℕ) : ℕ → BitVec w
  | 0 => BitVec.ofNat w pattern
  | e + 1 =>
      let previous := even22PeriodicPowMask w p pattern e
      previous ||| (previous <<< (p * 2 ^ e))

theorem even22PeriodicPowMask_getLsbD_true
    {w p pattern e i : ℕ} (hiw : i < w) (hi : i < p * 2 ^ e)
    (hbit : pattern.testBit (i % p) = true) :
    (even22PeriodicPowMask w p pattern e).getLsbD i = true := by
  induction e generalizing i with
  | zero =>
      have hip : i < p := by simpa using hi
      have himod : i % p = i := Nat.mod_eq_of_lt hip
      rw [himod] at hbit
      rw [even22PeriodicPowMask, BitVec.getLsbD_ofNat]
      simp [hiw, hbit]
  | succ e ih =>
      let shift := p * 2 ^ e
      have htotal : p * 2 ^ (e + 1) = 2 * shift := by
        dsimp [shift]
        rw [pow_succ]
        ring
      rw [even22PeriodicPowMask, BitVec.getLsbD_or]
      by_cases hfirst : i < shift
      · have hprev := ih hiw hfirst hbit
        simp [hprev]
      · have hle : shift ≤ i := Nat.le_of_not_gt hfirst
        have hj : i - shift < p * 2 ^ e := by
          rw [htotal] at hi
          dsimp [shift] at hle ⊢
          omega
        have hmod : (i - shift) % p = i % p := by
          conv_rhs => rw [← Nat.add_sub_of_le hle]
          simp [shift, Nat.add_mod]
        have hjw : i - shift < w := by omega
        have hprev := ih hjw hj (by simpa [hmod] using hbit)
        rw [BitVec.getLsbD_shiftLeft]
        simp [hiw, hfirst, hprev, shift]

/-- Retained sequential semantics for backward-compatible source auditing.
The production certificates below use the balanced tree evaluator. -/
def even22IntersectPeriodicItems (w e : ℕ) :
    BitVec w → List (ℕ × ℕ) → BitVec w
  | acc, [] => acc
  | acc, (p, pattern) :: rest =>
      if acc = BitVec.zero w then BitVec.zero w
      else even22IntersectPeriodicItems w e
        (acc.and (even22PeriodicPowMask w p pattern e)) rest

theorem even22IntersectPeriodicItems_getLsbD_true
    {w e i : ℕ} {acc : BitVec w} {items : List (ℕ × ℕ)}
    (hiw : i < w) (hacc : acc.getLsbD i = true)
    (hitem : ∀ item ∈ items,
      i < item.1 * 2 ^ e ∧ item.2.testBit (i % item.1) = true) :
    (even22IntersectPeriodicItems w e acc items).getLsbD i = true := by
  induction items generalizing acc with
  | nil => simpa [even22IntersectPeriodicItems] using hacc
  | cons item rest ih =>
      have hhead := hitem item (by simp)
      have hmask := even22PeriodicPowMask_getLsbD_true hiw hhead.1 hhead.2
      have hacc_ne : acc ≠ BitVec.zero w := by
        intro hzero
        subst acc
        simp at hacc
      rw [even22IntersectPeriodicItems, if_neg hacc_ne]
      apply ih
      · simp [hacc, hmask]
      · intro next hnext
        exact hitem next (by simp [hnext])

theorem even22No_index_of_intersection_zero
    {w e i : ℕ} {items : List (ℕ × ℕ)}
    (hiw : i < w)
    (hzero : even22IntersectPeriodicItems w e (BitVec.allOnes w) items =
      BitVec.zero w)
    (hitem : ∀ item ∈ items,
      i < item.1 * 2 ^ e ∧ item.2.testBit (i % item.1) = true) : False := by
  have htrue := even22IntersectPeriodicItems_getLsbD_true hiw
    (acc := BitVec.allOnes w) (items := items) (by simp [hiw]) hitem
  rw [hzero] at htrue
  simp at htrue

inductive Even22PeriodicTree where
  | leaf (prime pattern : ℕ)
  | node (left right : Even22PeriodicTree)

namespace Even22PeriodicTree

def eval : Even22PeriodicTree → (w e : ℕ) → BitVec w
  | .leaf prime pattern, w, e => even22PeriodicPowMask w prime pattern e
  | .node left right, w, e => (left.eval w e).and (right.eval w e)

def Supports (tree : Even22PeriodicTree) (i e : ℕ) : Prop :=
  match tree with
  | .leaf prime pattern =>
      i < prime * 2 ^ e ∧ pattern.testBit (i % prime) = true
  | .node left right => left.Supports i e ∧ right.Supports i e

end Even22PeriodicTree

theorem Even22PeriodicTree.eval_getLsbD_true
    {tree : Even22PeriodicTree} {w e i : ℕ}
    (hiw : i < w) (hsupports : tree.Supports i e) :
    (tree.eval w e).getLsbD i = true := by
  induction tree with
  | leaf prime pattern =>
      exact even22PeriodicPowMask_getLsbD_true hiw
        hsupports.1 hsupports.2
  | node left right ihLeft ihRight =>
      have hleft := ihLeft hsupports.1
      have hright := ihRight hsupports.2
      simpa [eval, hleft, hright]

theorem even22No_index_of_tree_zero
    {tree : Even22PeriodicTree} {w e i : ℕ}
    (hiw : i < w) (hzero : tree.eval w e = BitVec.zero w)
    (hsupports : tree.Supports i e) : False := by
  have htrue := tree.eval_getLsbD_true hiw hsupports
  rw [hzero] at htrue
  simpa using htrue

theorem even22_allowed_int
    {p : ℕ} [NeZero p] (A : ZMod p → Bool)
    (hallow : ∀ w v : ZMod p,
      evenTable22S w = 4 * evenTable22S v →
        A (evenTable22T w - 2 * evenTable22T v) = true)
    {w v m : ℤ} (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : m = evenTable22T w - 2 * evenTable22T v) :
    A (m : ZMod p) = true := by
  have hSp : evenTable22S (w : ZMod p) = 4 * evenTable22S (v : ZMod p) := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) hS
    simpa [evenTable22S] using h
  subst m
  simpa [evenTable22T] using hallow (w : ZMod p) (v : ZMod p) hSp

end Erdos686.Erdos686Variant
