#!/usr/bin/env python3
"""Generate isolated ordinary-kernel Lean tables for the k=32 closure."""

from __future__ import annotations

from pathlib import Path

import even_k32_verify as verify


ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "ErdosProblems"
PREFIX = "Erdos686EvenK32"
NS_OPEN = "namespace Erdos686.Erdos686Variant\n"
NS_CLOSE = "\nend Erdos686.Erdos686Variant\n"


def write(name: str, body: str) -> None:
    (OUT / f"{name}.lean").write_text(body)


def polynomial(name: str, terms: dict[int, int], variable: str = "W") -> str:
    ordered = sorted(terms.items(), reverse=True)
    pieces = []
    for index, (degree, coefficient) in enumerate(ordered):
        absolute = abs(coefficient)
        atom = str(absolute) if degree == 0 else (
            variable if degree == 1 and absolute == 1 else
            f"{variable} ^ {degree}" if absolute == 1 else
            f"{absolute} * {variable} ^ {degree}"
        )
        if index == 0:
            pieces.append(("- " if coefficient < 0 else "") + atom)
        else:
            pieces.append((" - " if coefficient < 0 else " + ") + atom)
    return f"def {name} {{R : Type}} [CommRing R] ({variable} : R) : R :=\n  " + "\n    ".join(pieces)


def generate_defs(report: dict) -> None:
    roots = [(2 * j - 1) ** 2 for j in range(1, 17)]
    factors = [f"({{W}} ^ 2 - {root})" for root in roots]
    factor_lines = []
    for i in range(0, len(factors), 4):
        factor_lines.append(" * ".join(factors[i:i + 4]).format(W="W"))
    s_def = "def evenTable32S {R : Type} [CommRing R] (W : R) : R :=\n  " + \
        " *\n    ".join(factor_lines)
    t_def = polynomial("evenTable32T", verify.T_POLY)
    masks = []
    for row in report["cover"]["rows"]:
        p = row["p"]
        masks.append(
            f"def even32A{p} (x : ZMod {p}) : Bool :=\n"
            f"  ({row['allowed_m_mask']}).testBit x.val"
        )
    write(
        f"{PREFIX}Defs",
        "import ErdosProblems.Erdos686EvenK16\n" + NS_OPEN + "\n" +
        s_def + "\n\n" + t_def + "\n\n" + "\n\n".join(masks) + NS_CLOSE,
    )


def generate_prime_tables(report: dict) -> None:
    previous_table = None
    for row in report["cover"]["rows"]:
        p = row["p"]
        chunks = [(lo, min(lo + 128, p)) for lo in range(0, p, 128)]
        for shard, (lo, hi) in enumerate(chunks):
            theorem = f"even32_allowed_{p}_shard_{shard}"
            if shard == 0:
                dependency = previous_table or f"{PREFIX}Core"
            else:
                dependency = f"{PREFIX}TableP{p}S{shard - 1}"
            body = (
                f"import ErdosProblems.{dependency}\n" + NS_OPEN +
                "\nset_option maxHeartbeats 100000000 in\n"
                "set_option maxRecDepth 1000000 in\n"
                f"theorem {theorem} :\n"
                f"    ∀ w : ZMod {p}, {lo} ≤ w.val → w.val < {hi} → ∀ v : ZMod {p},\n"
                "      evenTable32S w = 4 * evenTable32S v →\n"
                f"        even32A{p} (evenTable32T w - 2 * evenTable32T v) = true := by decide\n" +
                NS_CLOSE
            )
            write(f"{PREFIX}TableP{p}S{shard}", body)

        imports = f"import ErdosProblems.{PREFIX}TableP{p}S{len(chunks) - 1}"
        proof = [f"theorem even32_allowed_{p} : ∀ w v : ZMod {p},",
                 "    evenTable32S w = 4 * evenTable32S v →",
                 f"      even32A{p} (evenTable32T w - 2 * evenTable32T v) = true := by",
                 "  intro w v hS"]
        for shard, (lo, hi) in enumerate(chunks[:-1]):
            proof += [f"  by_cases h{shard} : w.val < {hi}",
                      f"  · exact even32_allowed_{p}_shard_{shard} w (by omega) h{shard} v hS"]
        last = len(chunks) - 1
        lo, hi = chunks[-1]
        if len(chunks) == 1:
            proof += [f"  exact even32_allowed_{p}_shard_0 w (by omega) (ZMod.val_lt w) v hS"]
        else:
            proof += [f"  · exact even32_allowed_{p}_shard_{last} w (by omega) (ZMod.val_lt w) v hS"]
        write(f"{PREFIX}TableP{p}", imports + "\n" + NS_OPEN + "\n" + "\n".join(proof) + NS_CLOSE)
        previous_table = f"{PREFIX}TableP{p}"

    imports = f"import ErdosProblems.{previous_table}"
    write(f"{PREFIX}Tables", imports + "\n")


def candidate_rest_expression(t: str) -> str:
    expressions = [
        f"even32A{p} ((-({verify.FIXED} * ({t} : ℤ)) : ℤ) : ZMod {p})"
        for p in verify.COVER if p != 17
    ]
    return " &&\n    ".join(expressions)


def generate_candidate_defs() -> None:
    classes = verify.P17_CLASSES
    q_terms = [
        f"(({verify.CANDIDATE_COUNT} < {'17 * q' if r == 0 else f'17 * q + {r}'}) || "
        f"!(even32CandidateAllowedRest ({'17 * q' if r == 0 else f'17 * q + {r}'})))"
        for r in classes
    ]
    body = (
        f"import ErdosProblems.{PREFIX}Defs\n" + NS_OPEN + "\n"
        "/-- Residue conditions after the seven-class modulus-17 prefilter. -/\n"
        "def even32CandidateAllowedRest (t : ℕ) : Bool :=\n  " +
        candidate_rest_expression("t") + "\n\n"
        "/-- All prime-field conditions in the k=32 large-gap cover. -/\n"
        "def even32CandidateAllowed (t : ℕ) : Bool :=\n"
        f"  even32A17 ((-({verify.FIXED} * (t : ℤ)) : ℤ) : ZMod 17) &&\n"
        "    even32CandidateAllowedRest t\n\n"
        "def even32QCoveredBool (q : ℕ) : Bool :=\n  " +
        " &&\n  ".join(q_terms) + "\n\n"
        "abbrev even32QCovered (q : ℕ) : Prop := even32QCoveredBool q = true\n\n"
        "def even32ScanPow (f : ℕ → Bool) (lo : ℕ) : ℕ → Bool\n"
        "  | 0 => f lo\n"
        "  | e + 1 => even32ScanPow f lo e && even32ScanPow f (lo + 2 ^ e) e\n\n"
        "theorem even32ScanPow_get {f : ℕ → Bool} {lo e q : ℕ}\n"
        "    (hscan : even32ScanPow f lo e = true)\n"
        "    (hlo : lo ≤ q) (hhi : q < lo + 2 ^ e) : f q = true := by\n"
        "  induction e generalizing lo with\n"
        "  | zero =>\n"
        "      simp only [pow_zero, Nat.add_one] at hhi\n"
        "      have : q = lo := by omega\n"
        "      simpa [even32ScanPow, this] using hscan\n"
        "  | succ e ih =>\n"
        "      simp only [even32ScanPow, Bool.and_eq_true] at hscan\n"
        "      rw [pow_succ] at hhi\n"
        "      by_cases hmid : q < lo + 2 ^ e\n"
        "      · exact ih hscan.1 hlo hmid\n"
        "      · exact ih hscan.2 (by omega) (by omega)\n" + NS_CLOSE
    )
    write(f"{PREFIX}CandidateDefs", body)


def generate_cover_scans() -> None:
    shard_count = 13
    for shard in range(shard_count):
        lo = shard * 2048
        dependency = (f"{PREFIX}Tables" if shard == 0 else
                      f"{PREFIX}CandidateCoverS{shard - 1}")
        body = (
            f"import ErdosProblems.{dependency}\n" + NS_OPEN +
            "\nset_option maxHeartbeats 200000000 in\n"
            "set_option maxRecDepth 1000000 in\n"
            f"theorem even32_candidate_cover_scan_{shard} :\n"
            f"    even32ScanPow even32QCoveredBool {lo} 11 = true := by decide\n" + NS_CLOSE
        )
        write(f"{PREFIX}CandidateCoverS{shard}", body)

    imports = f"import ErdosProblems.{PREFIX}CandidateCoverS{shard_count - 1}"
    lines = ["theorem even32_q_cover (q : ℕ) (hq : q < 25365) : even32QCovered q := by"]
    for shard in range(shard_count - 1):
        hi = (shard + 1) * 2048
        lines += [f"  by_cases h{shard} : q < {hi}",
                  f"  · exact even32ScanPow_get even32_candidate_cover_scan_{shard} (by omega) h{shard}"]
    lines += [f"  · exact even32ScanPow_get even32_candidate_cover_scan_{shard_count - 1} (by omega) (by omega)"]
    write(f"{PREFIX}CandidateCoverScans", imports + "\n" + NS_OPEN + "\n" + "\n".join(lines) + NS_CLOSE)


def generate_candidate_logic() -> None:
    disjunction = " ∨ ".join(f"r.val = {r}" for r in verify.P17_CLASSES)
    class_lemmas = []
    for r in verify.P17_CLASSES:
        term = "17 * q" if r == 0 else f"17 * q + {r}"
        class_lemmas.append(
            f"private lemma even32_qcover_rest_{r} {{q : ℕ}} (h : even32QCovered q)\n"
            f"    (hb : {term} ≤ {verify.CANDIDATE_COUNT}) :\n"
            f"    even32CandidateAllowedRest ({term}) = false := by\n"
            "  change even32QCoveredBool q = true at h\n"
            f"  cases hr : even32CandidateAllowedRest ({term})\n"
            "  · rfl\n"
            f"  · have hlt : ¬{verify.CANDIDATE_COUNT} < {term} := by omega\n"
            "    simp [even32QCoveredBool, hlt, hr] at h"
        )
    cases_pattern = " | ".join(f"h{r}" for r in verify.P17_CLASSES)
    branches = []
    for r in verify.P17_CLASSES:
        term = "17 * q" if r == 0 else f"17 * q + {r}"
        branches.append(
            f"  · have ht : t = {term} := by dsimp [fr, q, r] at *; omega\n"
            f"    have hrfalse := even32_qcover_rest_{r} hqcover (by omega)\n"
            "    simp [even32CandidateAllowed, ht, hrfalse]"
        )
    body = (
        f"import ErdosProblems.{PREFIX}CandidateCoverScans\n" + NS_OPEN + "\n"
        "private theorem even32_mod17_classes : ∀ r : Fin 17,\n"
        f"    even32A17 ((-({verify.FIXED} * (r.val : ℤ)) : ℤ) : ZMod 17) = true →\n"
        f"      {disjunction} := by decide\n\n" +
        "\n\n".join(class_lemmas) + "\n\n"
        "theorem even32_candidate_cover_of_qcover\n"
        "    (qcover : ∀ q : ℕ, q < 25365 → even32QCovered q)\n"
        f"    (t : ℕ) (htpos : 1 ≤ t) (htbound : t ≤ {verify.CANDIDATE_COUNT}) :\n"
        "    even32CandidateAllowed t = false := by\n"
        f"  by_cases h17 : even32A17 ((-({verify.FIXED} * (t : ℤ)) : ℤ) : ZMod 17) = false\n"
        "  · change (even32A17 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 17) &&\n"
        "        even32CandidateAllowedRest t) = false\n"
        "    rw [h17]\n    rfl\n"
        f"  have h17' : even32A17 ((-({verify.FIXED} * (t : ℤ)) : ℤ) : ZMod 17) = true := by\n"
        f"    cases hA : even32A17 ((-({verify.FIXED} * (t : ℤ)) : ℤ) : ZMod 17) <;> simp_all\n"
        "  let q := t / 17\n  let r := t % 17\n"
        "  have hrlt : r < 17 := by dsimp [r]; exact Nat.mod_lt t (by norm_num)\n"
        "  let fr : Fin 17 := ⟨r, hrlt⟩\n"
        f"  have hcast : ((-({verify.FIXED} * (t : ℤ)) : ℤ) : ZMod 17) =\n"
        f"      ((-({verify.FIXED} * (r : ℤ)) : ℤ) : ZMod 17) := by\n"
        "    push_cast\n    rw [ZMod.natCast_mod]\n"
        f"  have hfr : even32A17 ((-({verify.FIXED} * (fr.val : ℤ)) : ℤ) : ZMod 17) = true := by\n"
        "    dsimp [fr]\n    rw [← hcast]\n    exact h17'\n"
        "  have hdecomp := Nat.mod_add_div t 17\n"
        "  have hqbound : q < 25365 := by dsimp [q, r] at *; omega\n"
        "  have hqcover := qcover q hqbound\n"
        f"  rcases even32_mod17_classes fr hfr with {cases_pattern}\n" +
        "\n".join(branches) + NS_CLOSE
    )
    write(f"{PREFIX}CandidateLogic", body)

    cover_body = (
        f"import ErdosProblems.{PREFIX}CandidateLogic\n"
        + NS_OPEN + "\n"
        "theorem even32_candidate_cover (t : ℕ) (htpos : 1 ≤ t)\n"
        f"    (htbound : t ≤ {verify.CANDIDATE_COUNT}) : even32CandidateAllowed t = false :=\n"
        "  even32_candidate_cover_of_qcover even32_q_cover t htpos htbound\n" + NS_CLOSE
    )
    write(f"{PREFIX}CandidateCover", cover_body)


def generate_finite_strip() -> None:
    shard_count = 12
    for shard in range(shard_count):
        lo = 32 + 8 * shard
        hi = lo + 8
        dependency = (f"{PREFIX}Defs" if shard == 0 else
                      f"{PREFIX}FiniteStripS{shard - 1}")
        body = (
            f"import ErdosProblems.{dependency}\n" + NS_OPEN +
            "\nset_option maxHeartbeats 100000000 in\n"
            "set_option maxRecDepth 1000000 in\n"
            f"theorem even32_finite_strip_shard_{shard} :\n"
            f"    ∀ d : Fin 128, {lo} ≤ d.val → d.val < {hi} → ∀ a : Fin 222,\n"
            "      evenTable32S\n"
            "          (2 * (((22 * d.val - 31 + a.val) + d.val : ℕ) : ℤ) + 33) ≠\n"
            "        4 * evenTable32S (2 * ((22 * d.val - 31 + a.val : ℕ) : ℤ) + 33) := by decide\n" + NS_CLOSE
        )
        write(f"{PREFIX}FiniteStripS{shard}", body)
    imports = f"import ErdosProblems.{PREFIX}FiniteStripS{shard_count - 1}"
    proof = ["theorem even32_finite_strip :",
             "    ∀ d : Fin 128, 32 ≤ d.val → ∀ n : Fin 2984,",
             "      22 * d.val < n.val + 32 → 2 * n.val + 2 < 47 * d.val →",
             "        evenTable32S (2 * ((n.val + d.val : ℕ) : ℤ) + 33) ≠",
             "          4 * evenTable32S (2 * (n.val : ℤ) + 33) := by",
             "  intro d hd n hlo hhi",
             "  let base := 22 * d.val - 31",
             "  let a := n.val - base",
             "  have hbase : base ≤ n.val := by dsimp [base]; omega",
             "  have hna : base + a = n.val := by dsimp [a]; omega",
             "  have halt : a < 222 := by dsimp [a, base] at *; omega",
             "  let fa : Fin 222 := ⟨a, halt⟩"]
    for shard in range(shard_count - 1):
        hi = 40 + 8 * shard
        proof += [f"  by_cases h{shard} : d.val < {hi}",
                  f"  · have h := even32_finite_strip_shard_{shard} d (by omega) h{shard} fa",
                  "    dsimp [fa] at h",
                  "    rw [← hna]",
                  "    exact h"]
    proof += [f"  · have h := even32_finite_strip_shard_{shard_count - 1} d (by omega) (by omega) fa",
              "    dsimp [fa] at h",
              "    rw [← hna]",
              "    exact h"]
    write(f"{PREFIX}FiniteStrip", imports + "\n" + NS_OPEN + "\n" + "\n".join(proof) + NS_CLOSE)


def main() -> None:
    report = verify.audit()
    generate_defs(report)
    generate_prime_tables(report)
    generate_candidate_defs()
    generate_cover_scans()
    generate_candidate_logic()
    generate_finite_strip()
    print("generated isolated k=32 Lean modules")


if __name__ == "__main__":
    main()
