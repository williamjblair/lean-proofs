#!/usr/bin/env python3
"""Generate axiom-free local-table sources for the row-22 packed cover.

This is a clean-room recovery of the table phase of dangling producer blob
``d84836e8a5f8b979cf1813dd25d63a9b54b9ce3a``.  It deliberately has no
stub-generation mode: every emitted theorem is proved by ``decide +kernel``.
The packed-tree phase is added only after this local-table chain passes an
independent axiom audit.
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OUT = ROOT / "ErdosProblems"
VERIFIER_PATH = (
    ROOT / "compute/campaign686/agent_k22_sieve_probe/k22_sieve_probe_verify.py"
)
PREFIX = "Erdos686EvenK22"
NS_OPEN = "namespace Erdos686.Erdos686Variant\n"
NS_CLOSE = "\nend Erdos686.Erdos686Variant\n"
BRANCHES = (17, 21, 25, 29)
CHUNK = 16_000_000
EXPONENT = 18
MAPS_PER_MODULE = 8
BOUND = 3_795_146_531


def load_verifier():
    spec = importlib.util.spec_from_file_location(
        "k22_sieve_probe_verify", VERIFIER_PATH
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def write(name: str, body: str) -> None:
    path = OUT / f"{name}.lean"
    path.write_text(body)


def active_primes(verifier) -> list[int]:
    primes: list[int] = []
    for prime in verifier.primes_through(953):
        if prime in (2, 3, 11, 23):
            continue
        if len(verifier.local_allowed_t_residues(prime)) != prime:
            primes.append(prime)
    assert len(primes) == 132
    assert primes[0] == 83 and primes[-1] == 953
    return primes


def table_primes(verifier) -> list[int]:
    return [23, *active_primes(verifier)]


def allowed_m_mask(verifier, prime: int) -> int:
    allowed_t = verifier.local_allowed_t_residues(prime)
    row = verifier.make_row_data()
    s_values = [
        verifier.eval_poly(row.s_poly, value) % prime for value in range(prime)
    ]
    t_values = [
        verifier.eval_poly(row.t_poly, value) % prime for value in range(prime)
    ]
    buckets: dict[int, list[int]] = {}
    for w, value in enumerate(s_values):
        buckets.setdefault(value, []).append(w)
    direct_m = frozenset(
        (t_values[w] - 2 * t_values[v]) % prime
        for v in range(prime)
        for w in buckets.get(4 * s_values[v] % prime, ())
    )
    transformed_m = frozenset((-33 * residue) % prime for residue in allowed_t)
    assert direct_m == transformed_m
    return sum(1 << residue for residue in direct_m)


def generate_table_defs(verifier, primes: list[int]) -> None:
    masks = [
        (
            f"def even22A{prime} (x : ZMod {prime}) : Bool :=\n"
            f"  ({allowed_m_mask(verifier, prime)}).testBit x.val"
        )
        for prime in primes
    ]
    write(
        f"{PREFIX}TableDefs",
        f"import ErdosProblems.{PREFIX}Defs\n\n"
        + NS_OPEN
        + "\n"
        + "\n\n".join(masks)
        + NS_CLOSE,
    )


def shard_ranges(prime: int) -> list[tuple[int, int]]:
    return [(lo, min(lo + 128, prime)) for lo in range(0, prime, 128)]


def generate_prime_table(prime: int) -> int:
    ranges = shard_ranges(prime)
    for shard, (lo, hi) in enumerate(ranges):
        write(
            f"{PREFIX}TableP{prime}S{shard}",
            f"import ErdosProblems.{PREFIX}TableDefs\n\n"
            + NS_OPEN
            + "\nset_option maxHeartbeats 100000000 in\n"
            + "set_option maxRecDepth 1000000 in\n"
            + f"theorem even22_allowed_{prime}_shard_{shard} :\n"
            + f"    ∀ w : ZMod {prime}, {lo} ≤ w.val → w.val < {hi} → "
            + f"∀ v : ZMod {prime},\n"
            + "      evenTable22S w = 4 * evenTable22S v →\n"
            + f"        even22A{prime} (evenTable22T w - 2 * evenTable22T v) = true := by\n"
            + "  decide +kernel\n"
            + NS_CLOSE,
        )

    proof = [
        f"theorem even22_allowed_{prime} : ∀ w v : ZMod {prime},",
        "    evenTable22S w = 4 * evenTable22S v →",
        f"      even22A{prime} (evenTable22T w - 2 * evenTable22T v) = true := by",
        "  intro w v hS",
    ]
    for shard, (_lo, hi) in enumerate(ranges[:-1]):
        proof.extend(
            [
                f"  by_cases h{shard} : w.val < {hi}",
                f"  · exact even22_allowed_{prime}_shard_{shard} w "
                f"(by omega) h{shard} v hS",
            ]
        )
    last = len(ranges) - 1
    if last == 0:
        proof.append(
            f"  exact even22_allowed_{prime}_shard_0 w "
            "(by omega) (ZMod.val_lt w) v hS"
        )
    else:
        proof.append(
            f"  · exact even22_allowed_{prime}_shard_{last} w "
            "(by omega) (ZMod.val_lt w) v hS"
        )

    imports = "\n".join(
        f"import ErdosProblems.{PREFIX}TableP{prime}S{shard}"
        for shard in range(len(ranges))
    )
    write(
        f"{PREFIX}TableP{prime}",
        imports + "\n\n" + NS_OPEN + "\n" + "\n".join(proof) + NS_CLOSE,
    )
    return len(ranges)


def generate_tables_aggregate(primes: list[int]) -> None:
    imports = "\n".join(
        f"import ErdosProblems.{PREFIX}TableP{prime}" for prime in primes
    )
    write(f"{PREFIX}Tables", imports + "\n")


def q_pattern(verifier, prime: int, branch: int, lo: int) -> int:
    allowed = verifier.local_allowed_t_residues(prime)
    inverse = pow(46, -1, prime)
    global_residues = {
        ((allowed_residue - branch) * inverse) % prime
        for allowed_residue in allowed
    }
    local_residues = {(residue - lo) % prime for residue in global_residues}
    return sum(1 << residue for residue in local_residues)


def branch_length(branch: int) -> int:
    return (BOUND - branch) // 46 + 1


def chunks(branch: int) -> list[tuple[int, int]]:
    length = branch_length(branch)
    return [
        (lo, min(CHUNK, length - lo)) for lo in range(0, length, CHUNK)
    ]


def verify_chunk_cover(verifier, primes: list[int]) -> None:
    for branch in BRANCHES:
        for lo, width in chunks(branch):
            bits = (1 << width) - 1
            for prime in primes:
                pattern = q_pattern(verifier, prime, branch, lo)
                bits &= verifier.periodic_mask(pattern, prime, width)
                if bits == 0:
                    break
            assert bits == 0, (branch, lo, width)
            assert width <= primes[0] * 2**EXPONENT


PACKED_SEMANTICS = r'''
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
'''


def generate_packed_defs() -> None:
    write(
        f"{PREFIX}PackedDefs",
        f"import ErdosProblems.{PREFIX}Tables\n\n"
        + NS_OPEN
        + PACKED_SEMANTICS
        + NS_CLOSE,
    )


PackedTree = tuple[str, int, int] | tuple[str, "PackedTree", "PackedTree"]


def balanced_tree(items: list[tuple[int, int]]) -> PackedTree:
    assert items
    if len(items) == 1:
        return ("leaf", items[0][0], items[0][1])
    middle = len(items) // 2
    return ("node", balanced_tree(items[:middle]), balanced_tree(items[middle:]))


def tree_expression(tree: PackedTree) -> str:
    if tree[0] == "leaf":
        return f"(.leaf {tree[1]} {tree[2]})"
    return f"(.node {tree_expression(tree[1])} {tree_expression(tree[2])})"


def balanced_reference_expression(names: list[str]) -> str:
    assert names
    if len(names) == 1:
        return names[0]
    middle = len(names) // 2
    return (
        "(.node "
        + balanced_reference_expression(names[:middle])
        + " "
        + balanced_reference_expression(names[middle:])
        + ")"
    )


def mapping_lemmas(prime: int, branch: int, shard: int, lo: int, pattern: int) -> str:
    stem = f"even22_b{branch}_s{shard}_map_{prime}"
    return f'''
theorem {stem}_fin : ∀ r : Fin {prime},
    even22A{prime} (-(33 * (46 * ({lo} + (r.val : ZMod {prime})) + {branch}))) = true →
      ({pattern}).testBit r.val = true := by decide

theorem {stem} (i : ℕ)
    (h : even22A{prime} (-(33 * (46 * ({lo} + (i : ZMod {prime})) + {branch}))) = true) :
    ({pattern}).testBit (i % {prime}) = true := by
  let r : Fin {prime} := ⟨i % {prime}, Nat.mod_lt _ (by norm_num)⟩
  apply {stem}_fin r
  change even22A{prime}
    (-(33 * (46 * ({lo} + ((i % {prime} : ℕ) : ZMod {prime})) + {branch}))) = true
  have hcast : (i : ZMod {prime}) = ((i % {prime} : ℕ) : ZMod {prime}) :=
    (ZMod.natCast_mod i {prime}).symm
  rw [← hcast]
  exact h
'''


def leaf_support_proof(prime: int, branch: int, shard: int) -> list[str]:
    stem = f"even22_b{branch}_s{shard}_map_{prime}"
    return [
        "constructor",
        "· norm_num at hi ⊢",
        "  omega",
        f"· apply {stem} i",
        f"  have hA := even22_allowed_int even22A{prime} "
        f"even22_allowed_{prime} hS hm",
        "  simpa using hA",
    ]


def support_proof(tree: PackedTree, branch: int, shard: int) -> list[str]:
    if tree[0] == "leaf":
        return leaf_support_proof(tree[1], branch, shard)
    result = ["constructor"]
    for marker, child in (("·", tree[1]), ("·", tree[2])):
        child_lines = support_proof(child, branch, shard)
        result.append(f"{marker} {child_lines[0]}")
        result.extend(f"  {line}" for line in child_lines[1:])
    return result


def reference_support_proof(names: list[str]) -> list[str]:
    assert names
    if len(names) == 1:
        return [f"exact {names[0]}Supports hi hS hm"]
    middle = len(names) // 2
    result = ["constructor"]
    for marker, child in (
        ("·", names[:middle]),
        ("·", names[middle:]),
    ):
        child_lines = reference_support_proof(child)
        result.append(f"{marker} {child_lines[0]}")
        result.extend(f"  {line}" for line in child_lines[1:])
    return result


def generate_packed_shards(verifier, primes: list[int]) -> list[str]:
    generated: list[str] = []
    for branch in BRANCHES:
        for shard, (lo, width) in enumerate(chunks(branch)):
            name = f"{PREFIX}PackedB{branch}S{shard}"
            items = [(p, q_pattern(verifier, p, branch, lo)) for p in primes]
            tree = balanced_tree(items)
            map_modules: list[str] = []
            group_trees: list[str] = []
            for group, start in enumerate(range(0, len(items), MAPS_PER_MODULE)):
                map_name = f"{name}Maps{group}"
                group_items = items[start : start + MAPS_PER_MODULE]
                group_tree = balanced_tree(group_items)
                group_tree_name = f"even22PackedB{branch}S{shard}Group{group}Tree"
                group_proof = "\n".join(
                    f"  {line}" for line in support_proof(group_tree, branch, shard)
                )
                map_body = (
                    f"import ErdosProblems.{PREFIX}PackedDefs\n\n"
                    + NS_OPEN
                    + "\n-- Keep finite decisions below the process-stack danger zone.\n"
                    + "set_option maxRecDepth 10000\n"
                    + "\n".join(
                        mapping_lemmas(p, branch, shard, lo, pattern)
                        for p, pattern in group_items
                    )
                    + f"\ndef {group_tree_name} : Even22PeriodicTree :=\n"
                    + f"  {tree_expression(group_tree)}\n\n"
                    + "set_option maxRecDepth 10000 in\n"
                    + f"theorem {group_tree_name}Supports\n"
                    + "    {w v : ℤ} {i : ℕ}\n"
                    + f"    (hi : i < {width})\n"
                    + "    (hS : evenTable22S w = 4 * evenTable22S v)\n"
                    + f"    (hm : -(33 * (46 * ({lo} + (i : ℤ)) + {branch})) =\n"
                    + "      evenTable22T w - 2 * evenTable22T v) :\n"
                    + f"    {group_tree_name}.Supports i {EXPONENT} := by\n"
                    + group_proof
                    + NS_CLOSE
                )
                write(map_name, map_body)
                map_modules.append(map_name)
                group_trees.append(group_tree_name)
            proof = "\n".join(
                f"  {line}" for line in reference_support_proof(group_trees)
            )
            body = (
                "\n".join(f"import ErdosProblems.{module}" for module in map_modules)
                + "\n\n"
                + NS_OPEN
                + "\nset_option maxRecDepth 10000\n\n"
                + f"def even22PackedB{branch}S{shard}Tree : Even22PeriodicTree :=\n"
                + f"  {balanced_reference_expression(group_trees)}\n\n"
                + f"def even22PackedB{branch}S{shard}Intersection : BitVec {width} :=\n"
                + f"  even22PackedB{branch}S{shard}Tree.eval {width} {EXPONENT}\n\n"
                + "set_option maxHeartbeats 1000000000 in\n"
                + "set_option maxRecDepth 1000000 in\n"
                + f"theorem even22PackedB{branch}S{shard}Intersection_zero :\n"
                + f"    even22PackedB{branch}S{shard}Intersection = BitVec.zero {width} := by\n"
                + "  decide +kernel\n"
                + "\nset_option maxRecDepth 1000000 in\n"
                + f"theorem even22_packed_b{branch}_s{shard}_no_centers\n"
                + "    {w v : ℤ} {q : ℕ}\n"
                + f"    (hlo : {lo} ≤ q) (hhi : q < {lo + width})\n"
                + "    (hS : evenTable22S w = 4 * evenTable22S v)\n"
                + f"    (hm : -(33 * (46 * (q : ℤ) + {branch})) =\n"
                + "      evenTable22T w - 2 * evenTable22T v) : False := by\n"
                + f"  let i := q - {lo}\n"
                + f"  have hi : i < {width} := by dsimp [i]; omega\n"
                + f"  have hqi : {lo} + i = q := by dsimp [i]; omega\n"
                + "  rw [← hqi] at hm\n"
                + f"  apply even22No_index_of_tree_zero hi "
                + f"even22PackedB{branch}S{shard}Intersection_zero\n"
                + f"  change even22PackedB{branch}S{shard}Tree.Supports i {EXPONENT}\n"
                + proof
                + NS_CLOSE
            )
            write(name, body)
            generated.append(name)
    imports = "\n".join(f"import ErdosProblems.{name}" for name in generated)
    write(f"{PREFIX}PackedShards", imports + "\n")
    return generated


def branch_dispatch(branch: int) -> str:
    lines: list[str] = []
    branch_chunks = chunks(branch)
    for shard, (lo, width) in enumerate(branch_chunks[:-1]):
        hi = lo + width
        lines.extend(
            [
                f"    by_cases h{shard} : q < {hi}",
                f"    · exact even22_packed_b{branch}_s{shard}_no_centers "
                f"(by omega) h{shard} hS hm",
            ]
        )
    shard = len(branch_chunks) - 1
    lines.append(
        f"    · exact even22_packed_b{branch}_s{shard}_no_centers "
        f"(by omega) (by omega) hS hm"
    )
    return "\n".join(lines)


def generate_packed_cover() -> None:
    class_disjunction = " ∨ ".join(f"r.val = {branch}" for branch in BRANCHES)
    branch_cases = []
    for branch in BRANCHES:
        branch_cases.append(
            f"  · have ht : t = 46 * q + {branch} := by "
            "dsimp [q, r, fr] at *; omega\n"
            + "    rw [ht] at hm htbound\n"
            + branch_dispatch(branch)
        )
    body = (
        f"import ErdosProblems.{PREFIX}PackedShards\n\n"
        + "import ErdosProblems.Erdos686EvenK22Core\n\n"
        + NS_OPEN
        + "\nprivate theorem even22_mod46_classes : ∀ r : Fin 46,\n"
        + "    even22A23 (-(33 * (r.val : ZMod 23))) = true → Odd r.val →\n"
        + f"      {class_disjunction} := by decide\n\n"
        + "/-- The packed prime-field certificate excludes every positive odd\n"
        + "candidate in the exact d>=250 Runge window. -/\n"
        + "theorem even22_packed_candidate_impossible\n"
        + "    {w v : ℤ} {t : ℕ}\n"
        + "    (hS : evenTable22S w = 4 * evenTable22S v)\n"
        + "    (hm : -(33 * (t : ℤ)) = evenTable22T w - 2 * evenTable22T v)\n"
        + f"    (htodd : Odd t) (htpos : 1 ≤ t) (htbound : t ≤ {BOUND}) : False := by\n"
        + "  have hA23z := even22_allowed_int even22A23 even22_allowed_23 hS hm\n"
        + "  have hA23 : even22A23 (-(33 * (t : ZMod 23))) = true := by\n"
        + "    simpa using hA23z\n"
        + "  let q := t / 46\n"
        + "  let r := t % 46\n"
        + "  have hrlt : r < 46 := by dsimp [r]; exact Nat.mod_lt _ (by norm_num)\n"
        + "  let fr : Fin 46 := ⟨r, hrlt⟩\n"
        + "  have hdecomp : 46 * q + r = t := by\n"
        + "    dsimp [q, r]\n"
        + "    omega\n"
        + "  have hcast : (t : ZMod 23) = (r : ZMod 23) := by\n"
        + "    rw [← hdecomp]\n"
        + "    push_cast\n"
        + "    have h46 : (46 : ZMod 23) = 0 := by decide\n"
        + "    simp [h46]\n"
        + "  have hAr : even22A23 (-(33 * (fr.val : ZMod 23))) = true := by\n"
        + "    dsimp [fr]\n"
        + "    rw [← hcast]\n"
        + "    exact hA23\n"
        + "  have hrodd : Odd fr.val := by\n"
        + "    rw [Nat.odd_iff] at htodd ⊢\n"
        + "    dsimp [fr, r]\n"
        + "    have hdiv : 2 ∣ 46 := by norm_num\n"
        + "    rw [Nat.mod_mod_of_dvd _ hdiv]\n"
        + "    exact htodd\n"
        + "  rcases even22_mod46_classes fr hAr hrodd with h17 | h21 | h25 | h29\n"
        + "\n".join(branch_cases)
        + "\n\n/-- The fully discharged k=22 row: the small-gap computation and the\n"
        + "packed large-gap certificate leave no solutions. -/\n"
        + "theorem no_gap_solution_four_even_twentytwo\n"
        + "    {n d : ℕ} (hd : 22 ≤ d) :\n"
        + "    blockProduct 22 (n + d) ≠ 4 * blockProduct 22 n := by\n"
        + "  apply no_gap_solution_four_even_twentytwo_of_large_obstruction ?_ hd\n"
        + "  intro w v t hS hm htpos htbound htodd\n"
        + "  exact even22_packed_candidate_impossible hS hm htodd htpos htbound\n"
        + NS_CLOSE
    )
    write(f"{PREFIX}PackedCover", body)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--prime",
        type=int,
        help="generate definitions and only this table prime",
    )
    parser.add_argument(
        "--packed",
        action="store_true",
        help="generate the balanced packed-tree phase after all tables exist",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    verifier = load_verifier()
    primes = table_primes(verifier)
    if args.packed:
        assert args.prime is None
        active = active_primes(verifier)
        verify_chunk_cover(verifier, active)
        generate_packed_defs()
        shards = generate_packed_shards(verifier, active)
        assert len(shards) == 24
        generate_packed_cover()
        print(f"generated {len(shards)} balanced packed shards, no stubs")
        return
    generate_table_defs(verifier, primes)
    selected = primes if args.prime is None else [args.prime]
    assert all(prime in primes for prime in selected)
    shard_count = sum(generate_prime_table(prime) for prime in selected)
    if args.prime is None:
        generate_tables_aggregate(primes)
    print(
        f"generated {len(selected)} real local table(s), "
        f"{shard_count} shard(s), no stubs"
    )


if __name__ == "__main__":
    main()
