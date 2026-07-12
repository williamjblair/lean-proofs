#!/usr/bin/env python3
"""Generate isolated ordinary-kernel Lean certificates for the k=28 row."""

from __future__ import annotations

from pathlib import Path

import even_k28_verify as verify


ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "ErdosProblems"
PREFIX = "Erdos686EvenK28"
NS_OPEN = "namespace Erdos686.Erdos686Variant\n"
NS_CLOSE = "\nend Erdos686.Erdos686Variant\n"


def write(name: str, body: str) -> None:
    (OUT / f"{name}.lean").write_text(body)


def polynomial(name: str, terms: dict[int, int], variable: str = "W") -> str:
    pieces = []
    for index, (degree, coefficient) in enumerate(sorted(terms.items(), reverse=True)):
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
    return (
        f"def {name} {{R : Type}} [CommRing R] ({variable} : R) : R :=\n  "
        + "\n    ".join(pieces)
    )


def generate_defs(report: dict) -> None:
    roots = [(2 * j - 1) ** 2 for j in range(1, verify.R + 1)]
    factors = [f"({{W}} ^ 2 - {root})" for root in roots]
    factor_lines = []
    for i in range(0, len(factors), 4):
        factor_lines.append(" * ".join(factors[i : i + 4]).format(W="W"))
    s_def = (
        "def evenTable28S {R : Type} [CommRing R] (W : R) : R :=\n  "
        + " *\n    ".join(factor_lines)
    )
    t_def = polynomial("evenTable28T", verify.T_POLY)
    masks = []
    for row in report["cover"]["rows"]:
        p = row["p"]
        masks.append(
            f"def even28A{p} (x : ZMod {p}) : Bool :=\n"
            f"  ({row['allowed_m_mask']}).testBit x.val"
        )
    write(
        f"{PREFIX}Defs",
        "import ErdosProblems.Erdos686EvenK16\n"
        + NS_OPEN
        + "\n"
        + s_def
        + "\n\n"
        + t_def
        + "\n\n"
        + "\n\n".join(masks)
        + NS_CLOSE,
    )


def generate_prime_tables(report: dict) -> None:
    previous_table = None
    for row in report["cover"]["rows"]:
        p = row["p"]
        chunks = [(lo, min(lo + 128, p)) for lo in range(0, p, 128)]
        for shard, (lo, hi) in enumerate(chunks):
            theorem = f"even28_allowed_{p}_shard_{shard}"
            if shard == 0:
                dependency = previous_table or f"{PREFIX}Core"
            else:
                dependency = f"{PREFIX}TableP{p}S{shard - 1}"
            body = (
                f"import ErdosProblems.{dependency}\n"
                + NS_OPEN
                + "\nset_option maxHeartbeats 100000000 in\n"
                + "set_option maxRecDepth 1000000 in\n"
                + f"theorem {theorem} :\n"
                + f"    ∀ w : ZMod {p}, {lo} ≤ w.val → w.val < {hi} → ∀ v : ZMod {p},\n"
                + "      evenTable28S w = 4 * evenTable28S v →\n"
                + f"        even28A{p} (evenTable28T w - 2 * evenTable28T v) = true := by decide\n"
                + NS_CLOSE
            )
            write(f"{PREFIX}TableP{p}S{shard}", body)

        proof = [
            f"theorem even28_allowed_{p} : ∀ w v : ZMod {p},",
            "    evenTable28S w = 4 * evenTable28S v →",
            f"      even28A{p} (evenTable28T w - 2 * evenTable28T v) = true := by",
            "  intro w v hS",
        ]
        for shard, (_lo, hi) in enumerate(chunks[:-1]):
            proof += [
                f"  by_cases h{shard} : w.val < {hi}",
                f"  · exact even28_allowed_{p}_shard_{shard} w (by omega) h{shard} v hS",
            ]
        last = len(chunks) - 1
        if len(chunks) == 1:
            proof += [
                "  exact even28_allowed_{}_shard_0 w (by omega) "
                "(ZMod.val_lt w) v hS".format(p)
            ]
        else:
            proof += [
                f"  · exact even28_allowed_{p}_shard_{last} w (by omega) "
                "(ZMod.val_lt w) v hS"
            ]
        write(
            f"{PREFIX}TableP{p}",
            f"import ErdosProblems.{PREFIX}TableP{p}S{last}\n"
            + NS_OPEN
            + "\n"
            + "\n".join(proof)
            + NS_CLOSE,
        )
        previous_table = f"{PREFIX}TableP{p}"
    write(f"{PREFIX}Tables", f"import ErdosProblems.{previous_table}\n")


def candidate_rest_expression(t: str) -> str:
    expressions = [
        f"even28A{p} ((-({verify.FIXED} * ({t} : ℤ)) : ℤ) : ZMod {p})"
        for p in verify.COVER
        if p != 29
    ]
    return " &&\n    ".join(expressions)


def generate_candidate_defs(report: dict) -> None:
    classes = report["cover"]["p29_classes"]
    q_terms = [
        f"(({verify.CANDIDATE_COUNT} < 29 * q + {r}) || "
        f"!(even28CandidateAllowedRest (29 * q + {r})))"
        for r in classes
    ]
    body = (
        f"import ErdosProblems.{PREFIX}FiniteStrip\n"
        + NS_OPEN
        + "\n/-- Residue conditions after the four-class modulus-29 prefilter. -/\n"
        + "def even28CandidateAllowedRest (t : ℕ) : Bool :=\n  "
        + candidate_rest_expression("t")
        + "\n\n/-- All prime-field conditions in the k=28 large-gap cover. -/\n"
        + "def even28CandidateAllowed (t : ℕ) : Bool :=\n"
        + f"  even28A29 ((-({verify.FIXED} * (t : ℤ)) : ℤ) : ZMod 29) &&\n"
        + "    even28CandidateAllowedRest t\n\n"
        + "def even28QCoveredBool (q : ℕ) : Bool :=\n  "
        + " &&\n  ".join(q_terms)
        + "\n\nabbrev even28QCovered (q : ℕ) : Prop := even28QCoveredBool q = true\n\n"
        + "def even28ScanPow (f : ℕ → Bool) (lo : ℕ) : ℕ → Bool\n"
        + "  | 0 => f lo\n"
        + "  | e + 1 => even28ScanPow f lo e && even28ScanPow f (lo + 2 ^ e) e\n\n"
        + "theorem even28ScanPow_get {f : ℕ → Bool} {lo e q : ℕ}\n"
        + "    (hscan : even28ScanPow f lo e = true)\n"
        + "    (hlo : lo ≤ q) (hhi : q < lo + 2 ^ e) : f q = true := by\n"
        + "  induction e generalizing lo with\n"
        + "  | zero =>\n"
        + "      simp only [pow_zero, Nat.add_one] at hhi\n"
        + "      have : q = lo := by omega\n"
        + "      simpa [even28ScanPow, this] using hscan\n"
        + "  | succ e ih =>\n"
        + "      simp only [even28ScanPow, Bool.and_eq_true] at hscan\n"
        + "      rw [pow_succ] at hhi\n"
        + "      by_cases hmid : q < lo + 2 ^ e\n"
        + "      · exact ih hscan.1 hlo hmid\n"
        + "      · exact ih hscan.2 (by omega) (by omega)\n"
        + NS_CLOSE
    )
    write(f"{PREFIX}CandidateDefs", body)


def generate_cover_scans() -> None:
    shard_count = 18
    for shard in range(shard_count):
        lo = shard * 2048
        dependency = (
            f"{PREFIX}Tables" if shard == 0 else f"{PREFIX}CandidateCoverS{shard - 1}"
        )
        body = (
            f"import ErdosProblems.{dependency}\n"
            + NS_OPEN
            + "\nset_option maxHeartbeats 200000000 in\n"
            + "set_option maxRecDepth 1000000 in\n"
            + f"theorem even28_candidate_cover_scan_{shard} :\n"
            + f"    even28ScanPow even28QCoveredBool {lo} 11 = true := by decide\n"
            + NS_CLOSE
        )
        write(f"{PREFIX}CandidateCoverS{shard}", body)
    lines = [
        f"theorem even28_q_cover (q : ℕ) (hq : q < {verify.CANDIDATE_COUNT // 29 + 1}) : even28QCovered q := by"
    ]
    for shard in range(shard_count - 1):
        hi = (shard + 1) * 2048
        lines += [
            f"  by_cases h{shard} : q < {hi}",
            f"  · exact even28ScanPow_get even28_candidate_cover_scan_{shard} (by omega) h{shard}",
        ]
    lines += [
        f"  · exact even28ScanPow_get even28_candidate_cover_scan_{shard_count - 1} (by omega) (by omega)"
    ]
    write(
        f"{PREFIX}CandidateCoverScans",
        f"import ErdosProblems.{PREFIX}CandidateCoverS{shard_count - 1}\n"
        + NS_OPEN
        + "\n"
        + "\n".join(lines)
        + NS_CLOSE,
    )


def generate_candidate_logic(report: dict) -> None:
    classes = report["cover"]["p29_classes"]
    disjunction = " ∨ ".join(f"r.val = {r}" for r in classes)
    class_lemmas = []
    for r in classes:
        class_lemmas.append(
            f"private lemma even28_qcover_rest_{r} {{q : ℕ}} (h : even28QCovered q)\n"
            f"    (hb : 29 * q + {r} ≤ {verify.CANDIDATE_COUNT}) :\n"
            f"    even28CandidateAllowedRest (29 * q + {r}) = false := by\n"
            "  change even28QCoveredBool q = true at h\n"
            f"  cases hr : even28CandidateAllowedRest (29 * q + {r})\n"
            "  · rfl\n"
            f"  · have hlt : ¬{verify.CANDIDATE_COUNT} < 29 * q + {r} := by omega\n"
            "    simp [even28QCoveredBool, hlt, hr] at h"
        )
    cases_pattern = " | ".join(f"h{r}" for r in classes)
    branches = []
    for r in classes:
        branches.append(
            f"  · have ht : t = 29 * q + {r} := by dsimp [fr, q, r] at *; omega\n"
            f"    have hrfalse := even28_qcover_rest_{r} hqcover (by omega)\n"
            "    simp [even28CandidateAllowed, ht, hrfalse]"
        )
    q_bound = verify.CANDIDATE_COUNT // 29 + 1
    body = (
        f"import ErdosProblems.{PREFIX}CandidateCoverScans\n"
        + NS_OPEN
        + "\nprivate theorem even28_mod29_classes : ∀ r : Fin 29,\n"
        + f"    even28A29 ((-({verify.FIXED} * (r.val : ℤ)) : ℤ) : ZMod 29) = true →\n"
        + f"      {disjunction} := by decide\n\n"
        + "\n\n".join(class_lemmas)
        + "\n\ntheorem even28_candidate_cover_of_qcover\n"
        + f"    (qcover : ∀ q : ℕ, q < {q_bound} → even28QCovered q)\n"
        + f"    (t : ℕ) (htpos : 1 ≤ t) (htbound : t ≤ {verify.CANDIDATE_COUNT}) :\n"
        + "    even28CandidateAllowed t = false := by\n"
        + f"  by_cases h29 : even28A29 ((-({verify.FIXED} * (t : ℤ)) : ℤ) : ZMod 29) = false\n"
        + "  · change (even28A29 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 29) &&\n"
        + "        even28CandidateAllowedRest t) = false\n"
        + "    rw [h29]\n    rfl\n"
        + f"  have h29' : even28A29 ((-({verify.FIXED} * (t : ℤ)) : ℤ) : ZMod 29) = true := by\n"
        + f"    cases hA : even28A29 ((-({verify.FIXED} * (t : ℤ)) : ℤ) : ZMod 29) <;> simp_all\n"
        + "  let q := t / 29\n  let r := t % 29\n"
        + "  have hrlt : r < 29 := by dsimp [r]; exact Nat.mod_lt t (by norm_num)\n"
        + "  let fr : Fin 29 := ⟨r, hrlt⟩\n"
        + f"  have hcast : ((-({verify.FIXED} * (t : ℤ)) : ℤ) : ZMod 29) =\n"
        + f"      ((-({verify.FIXED} * (r : ℤ)) : ℤ) : ZMod 29) := by\n"
        + "    push_cast\n    rw [ZMod.natCast_mod]\n"
        + f"  have hfr : even28A29 ((-({verify.FIXED} * (fr.val : ℤ)) : ℤ) : ZMod 29) = true := by\n"
        + "    dsimp [fr]\n    rw [← hcast]\n    exact h29'\n"
        + "  have hdecomp := Nat.mod_add_div t 29\n"
        + f"  have hqbound : q < {q_bound} := by dsimp [q, r] at *; omega\n"
        + "  have hqcover := qcover q hqbound\n"
        + f"  rcases even28_mod29_classes fr hfr with {cases_pattern}\n"
        + "\n".join(branches)
        + NS_CLOSE
    )
    write(f"{PREFIX}CandidateLogic", body)
    write(
        f"{PREFIX}CandidateCover",
        f"import ErdosProblems.{PREFIX}CandidateLogic\n"
        + NS_OPEN
        + "\ntheorem even28_candidate_cover (t : ℕ) (htpos : 1 ≤ t)\n"
        + f"    (htbound : t ≤ {verify.CANDIDATE_COUNT}) : even28CandidateAllowed t = false :=\n"
        + "  even28_candidate_cover_of_qcover even28_q_cover t htpos htbound\n"
        + NS_CLOSE,
    )


def generate_finite_strip() -> None:
    shard_count = 45
    for shard in range(shard_count):
        lo = 28 + 8 * shard
        hi = min(lo + 8, verify.SPLIT_GAP)
        dependency = (
            f"{PREFIX}Defs" if shard == 0 else f"{PREFIX}FiniteStripS{shard - 1}"
        )
        body = (
            f"import ErdosProblems.{dependency}\n"
            + NS_OPEN
            + "\nset_option maxHeartbeats 100000000 in\n"
            + "set_option maxRecDepth 1000000 in\n"
            + f"theorem even28_finite_strip_shard_{shard} :\n"
            + f"    ∀ d : Fin 384, {lo} ≤ d.val → d.val < {hi} → ∀ a : Fin 314,\n"
            + "      4 * (19 * d.val - 27 + a.val + 1) < 79 * d.val →\n"
            + "      evenTable28S\n"
            + "          (2 * (((19 * d.val - 27 + a.val) + d.val : ℕ) : ℤ) + 29) ≠\n"
            + "        4 * evenTable28S (2 * ((19 * d.val - 27 + a.val : ℕ) : ℤ) + 29) := by decide\n"
            + NS_CLOSE
        )
        write(f"{PREFIX}FiniteStripS{shard}", body)
    proof = [
        "theorem even28_finite_strip :",
        "    ∀ d : Fin 384, 28 ≤ d.val → ∀ n : Fin 7564,",
        "      19 * d.val < n.val + 28 → 4 * (n.val + 1) < 79 * d.val →",
        "        evenTable28S (2 * ((n.val + d.val : ℕ) : ℤ) + 29) ≠",
        "          4 * evenTable28S (2 * (n.val : ℤ) + 29) := by",
        "  intro d hd n hlo hhi",
        "  let base := 19 * d.val - 27",
        "  let a := n.val - base",
        "  have hbase : base ≤ n.val := by dsimp [base]; omega",
        "  have hna : base + a = n.val := by dsimp [a]; omega",
        "  have halt : a < 314 := by dsimp [a, base] at *; omega",
        "  let fa : Fin 314 := ⟨a, halt⟩",
        "  have hainequality : 4 * (base + a + 1) < 79 * d.val := by rw [hna]; exact hhi",
    ]
    for shard in range(shard_count - 1):
        hi = 36 + 8 * shard
        proof += [
            f"  by_cases h{shard} : d.val < {hi}",
            f"  · have h := even28_finite_strip_shard_{shard} d (by omega) h{shard} fa",
            "      (by dsimp [fa, base] at *; omega)",
            "    dsimp [fa, base] at h",
            "    rw [← hna]",
            "    exact h",
        ]
    proof += [
        f"  · have h := even28_finite_strip_shard_{shard_count - 1} d (by omega) "
        "d.isLt fa (by dsimp [fa, base] at *; omega)",
        "    dsimp [fa, base] at h",
        "    rw [← hna]",
        "    exact h",
    ]
    write(
        f"{PREFIX}FiniteStrip",
        f"import ErdosProblems.{PREFIX}FiniteStripS{shard_count - 1}\n"
        + NS_OPEN
        + "\n"
        + "\n".join(proof)
        + NS_CLOSE,
    )


def main() -> None:
    report = verify.audit()
    for path in OUT.glob(f"{PREFIX}*.lean"):
        if path.name not in {f"{PREFIX}Core.lean", f"{PREFIX}.lean"}:
            path.unlink()
    generate_defs(report)
    generate_candidate_defs(report)
    generate_finite_strip()
    generate_prime_tables(report)
    generate_cover_scans()
    generate_candidate_logic(report)
    print("generated isolated k=28 Lean modules")


if __name__ == "__main__":
    main()
