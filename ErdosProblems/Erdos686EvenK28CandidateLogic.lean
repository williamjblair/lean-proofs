import ErdosProblems.Erdos686EvenK28CandidateCoverScans
namespace Erdos686.Erdos686Variant

private theorem even28_mod29_classes : ∀ r : Fin 29,
    even28A29 ((-(50176 * (r.val : ℤ)) : ℤ) : ZMod 29) = true →
      r.val = 5 ∨ r.val = 14 ∨ r.val = 15 ∨ r.val = 24 := by decide

private lemma even28_qcover_rest_5 {q : ℕ} (h : even28QCovered q)
    (hb : 29 * q + 5 ≤ 1049958) :
    even28CandidateAllowedRest (29 * q + 5) = false := by
  change even28QCoveredBool q = true at h
  cases hr : even28CandidateAllowedRest (29 * q + 5)
  · rfl
  · have hlt : ¬1049958 < 29 * q + 5 := by omega
    simp [even28QCoveredBool, hlt, hr] at h

private lemma even28_qcover_rest_14 {q : ℕ} (h : even28QCovered q)
    (hb : 29 * q + 14 ≤ 1049958) :
    even28CandidateAllowedRest (29 * q + 14) = false := by
  change even28QCoveredBool q = true at h
  cases hr : even28CandidateAllowedRest (29 * q + 14)
  · rfl
  · have hlt : ¬1049958 < 29 * q + 14 := by omega
    simp [even28QCoveredBool, hlt, hr] at h

private lemma even28_qcover_rest_15 {q : ℕ} (h : even28QCovered q)
    (hb : 29 * q + 15 ≤ 1049958) :
    even28CandidateAllowedRest (29 * q + 15) = false := by
  change even28QCoveredBool q = true at h
  cases hr : even28CandidateAllowedRest (29 * q + 15)
  · rfl
  · have hlt : ¬1049958 < 29 * q + 15 := by omega
    simp [even28QCoveredBool, hlt, hr] at h

private lemma even28_qcover_rest_24 {q : ℕ} (h : even28QCovered q)
    (hb : 29 * q + 24 ≤ 1049958) :
    even28CandidateAllowedRest (29 * q + 24) = false := by
  change even28QCoveredBool q = true at h
  cases hr : even28CandidateAllowedRest (29 * q + 24)
  · rfl
  · have hlt : ¬1049958 < 29 * q + 24 := by omega
    simp [even28QCoveredBool, hlt, hr] at h

theorem even28_candidate_cover_of_qcover
    (qcover : ∀ q : ℕ, q < 36206 → even28QCovered q)
    (t : ℕ) (htpos : 1 ≤ t) (htbound : t ≤ 1049958) :
    even28CandidateAllowed t = false := by
  by_cases h29 : even28A29 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 29) = false
  · change (even28A29 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 29) &&
        even28CandidateAllowedRest t) = false
    rw [h29]
    rfl
  have h29' : even28A29 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 29) = true := by
    cases hA : even28A29 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 29) <;> simp_all
  let q := t / 29
  let r := t % 29
  have hrlt : r < 29 := by dsimp [r]; exact Nat.mod_lt t (by norm_num)
  let fr : Fin 29 := ⟨r, hrlt⟩
  have hcast : ((-(50176 * (t : ℤ)) : ℤ) : ZMod 29) =
      ((-(50176 * (r : ℤ)) : ℤ) : ZMod 29) := by
    push_cast
    rw [ZMod.natCast_mod]
  have hfr : even28A29 ((-(50176 * (fr.val : ℤ)) : ℤ) : ZMod 29) = true := by
    dsimp [fr]
    rw [← hcast]
    exact h29'
  have hdecomp := Nat.mod_add_div t 29
  have hqbound : q < 36206 := by dsimp [q, r] at *; omega
  have hqcover := qcover q hqbound
  rcases even28_mod29_classes fr hfr with h5 | h14 | h15 | h24
  · have ht : t = 29 * q + 5 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even28_qcover_rest_5 hqcover (by omega)
    simp [even28CandidateAllowed, ht, hrfalse]
  · have ht : t = 29 * q + 14 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even28_qcover_rest_14 hqcover (by omega)
    simp [even28CandidateAllowed, ht, hrfalse]
  · have ht : t = 29 * q + 15 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even28_qcover_rest_15 hqcover (by omega)
    simp [even28CandidateAllowed, ht, hrfalse]
  · have ht : t = 29 * q + 24 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even28_qcover_rest_24 hqcover (by omega)
    simp [even28CandidateAllowed, ht, hrfalse]
end Erdos686.Erdos686Variant
