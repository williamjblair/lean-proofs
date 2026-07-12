import ErdosProblems.Erdos686EvenK32CandidateCoverScans
namespace Erdos686.Erdos686Variant

private theorem even32_mod17_classes : ∀ r : Fin 17,
    even32A17 ((-(3221225472 * (r.val : ℤ)) : ℤ) : ZMod 17) = true →
      r.val = 0 ∨ r.val = 3 ∨ r.val = 6 ∨ r.val = 7 ∨ r.val = 10 ∨ r.val = 13 ∨ r.val = 14 := by decide

private lemma even32_qcover_rest_0 {q : ℕ} (h : even32QCovered q)
    (hb : 17 * q ≤ 431188) :
    even32CandidateAllowedRest (17 * q) = false := by
  change even32QCoveredBool q = true at h
  cases hr : even32CandidateAllowedRest (17 * q)
  · rfl
  · have hlt : ¬431188 < 17 * q := by omega
    simp [even32QCoveredBool, hlt, hr] at h

private lemma even32_qcover_rest_3 {q : ℕ} (h : even32QCovered q)
    (hb : 17 * q + 3 ≤ 431188) :
    even32CandidateAllowedRest (17 * q + 3) = false := by
  change even32QCoveredBool q = true at h
  cases hr : even32CandidateAllowedRest (17 * q + 3)
  · rfl
  · have hlt : ¬431188 < 17 * q + 3 := by omega
    simp [even32QCoveredBool, hlt, hr] at h

private lemma even32_qcover_rest_6 {q : ℕ} (h : even32QCovered q)
    (hb : 17 * q + 6 ≤ 431188) :
    even32CandidateAllowedRest (17 * q + 6) = false := by
  change even32QCoveredBool q = true at h
  cases hr : even32CandidateAllowedRest (17 * q + 6)
  · rfl
  · have hlt : ¬431188 < 17 * q + 6 := by omega
    simp [even32QCoveredBool, hlt, hr] at h

private lemma even32_qcover_rest_7 {q : ℕ} (h : even32QCovered q)
    (hb : 17 * q + 7 ≤ 431188) :
    even32CandidateAllowedRest (17 * q + 7) = false := by
  change even32QCoveredBool q = true at h
  cases hr : even32CandidateAllowedRest (17 * q + 7)
  · rfl
  · have hlt : ¬431188 < 17 * q + 7 := by omega
    simp [even32QCoveredBool, hlt, hr] at h

private lemma even32_qcover_rest_10 {q : ℕ} (h : even32QCovered q)
    (hb : 17 * q + 10 ≤ 431188) :
    even32CandidateAllowedRest (17 * q + 10) = false := by
  change even32QCoveredBool q = true at h
  cases hr : even32CandidateAllowedRest (17 * q + 10)
  · rfl
  · have hlt : ¬431188 < 17 * q + 10 := by omega
    simp [even32QCoveredBool, hlt, hr] at h

private lemma even32_qcover_rest_13 {q : ℕ} (h : even32QCovered q)
    (hb : 17 * q + 13 ≤ 431188) :
    even32CandidateAllowedRest (17 * q + 13) = false := by
  change even32QCoveredBool q = true at h
  cases hr : even32CandidateAllowedRest (17 * q + 13)
  · rfl
  · have hlt : ¬431188 < 17 * q + 13 := by omega
    simp [even32QCoveredBool, hlt, hr] at h

private lemma even32_qcover_rest_14 {q : ℕ} (h : even32QCovered q)
    (hb : 17 * q + 14 ≤ 431188) :
    even32CandidateAllowedRest (17 * q + 14) = false := by
  change even32QCoveredBool q = true at h
  cases hr : even32CandidateAllowedRest (17 * q + 14)
  · rfl
  · have hlt : ¬431188 < 17 * q + 14 := by omega
    simp [even32QCoveredBool, hlt, hr] at h

theorem even32_candidate_cover_of_qcover
    (qcover : ∀ q : ℕ, q < 25365 → even32QCovered q)
    (t : ℕ) (htpos : 1 ≤ t) (htbound : t ≤ 431188) :
    even32CandidateAllowed t = false := by
  by_cases h17 : even32A17 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 17) = false
  · change (even32A17 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 17) &&
        even32CandidateAllowedRest t) = false
    rw [h17]
    rfl
  have h17' : even32A17 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 17) = true := by
    cases hA : even32A17 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 17) <;> simp_all
  let q := t / 17
  let r := t % 17
  have hrlt : r < 17 := by dsimp [r]; exact Nat.mod_lt t (by norm_num)
  let fr : Fin 17 := ⟨r, hrlt⟩
  have hcast : ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 17) =
      ((-(3221225472 * (r : ℤ)) : ℤ) : ZMod 17) := by
    push_cast
    rw [ZMod.natCast_mod]
  have hfr : even32A17 ((-(3221225472 * (fr.val : ℤ)) : ℤ) : ZMod 17) = true := by
    dsimp [fr]
    rw [← hcast]
    exact h17'
  have hdecomp := Nat.mod_add_div t 17
  have hqbound : q < 25365 := by dsimp [q, r] at *; omega
  have hqcover := qcover q hqbound
  rcases even32_mod17_classes fr hfr with h0 | h3 | h6 | h7 | h10 | h13 | h14
  · have ht : t = 17 * q := by dsimp [fr, q, r] at *; omega
    have hrfalse := even32_qcover_rest_0 hqcover (by omega)
    simp [even32CandidateAllowed, ht, hrfalse]
  · have ht : t = 17 * q + 3 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even32_qcover_rest_3 hqcover (by omega)
    simp [even32CandidateAllowed, ht, hrfalse]
  · have ht : t = 17 * q + 6 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even32_qcover_rest_6 hqcover (by omega)
    simp [even32CandidateAllowed, ht, hrfalse]
  · have ht : t = 17 * q + 7 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even32_qcover_rest_7 hqcover (by omega)
    simp [even32CandidateAllowed, ht, hrfalse]
  · have ht : t = 17 * q + 10 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even32_qcover_rest_10 hqcover (by omega)
    simp [even32CandidateAllowed, ht, hrfalse]
  · have ht : t = 17 * q + 13 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even32_qcover_rest_13 hqcover (by omega)
    simp [even32CandidateAllowed, ht, hrfalse]
  · have ht : t = 17 * q + 14 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even32_qcover_rest_14 hqcover (by omega)
    simp [even32CandidateAllowed, ht, hrfalse]
end Erdos686.Erdos686Variant
