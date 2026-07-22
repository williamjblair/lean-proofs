import ErdosProblems.Erdos686.EvenK.K18.CandidateDefs
namespace Erdos686.Erdos686Variant

private theorem even18_mod19_classes : ∀ r : Fin 19,
    even18A19 ((-(81 * (r.val : ℤ)) : ℤ) : ZMod 19) = true →
      r.val = 1 ∨ r.val = 3 ∨ r.val = 16 ∨ r.val = 18 := by decide

private lemma even18_qcover_rest_1 {q : ℕ} (h : even18QCovered q)
    (hb : 19 * q + 1 ≤ 2990976) :
    even18CandidateAllowedRest (19 * q + 1) = false := by
  change even18QCoveredBool q = true at h
  cases hr : even18CandidateAllowedRest (19 * q + 1)
  · rfl
  · have hlt : ¬2990976 < 19 * q + 1 := by omega
    simp [even18QCoveredBool, hlt, hr] at h

private lemma even18_qcover_rest_3 {q : ℕ} (h : even18QCovered q)
    (hb : 19 * q + 3 ≤ 2990976) :
    even18CandidateAllowedRest (19 * q + 3) = false := by
  change even18QCoveredBool q = true at h
  cases hr : even18CandidateAllowedRest (19 * q + 3)
  · rfl
  · have hlt : ¬2990976 < 19 * q + 3 := by omega
    simp [even18QCoveredBool, hlt, hr] at h

private lemma even18_qcover_rest_16 {q : ℕ} (h : even18QCovered q)
    (hb : 19 * q + 16 ≤ 2990976) :
    even18CandidateAllowedRest (19 * q + 16) = false := by
  change even18QCoveredBool q = true at h
  cases hr : even18CandidateAllowedRest (19 * q + 16)
  · rfl
  · have hlt : ¬2990976 < 19 * q + 16 := by omega
    simp [even18QCoveredBool, hlt, hr] at h

private lemma even18_qcover_rest_18 {q : ℕ} (h : even18QCovered q)
    (hb : 19 * q + 18 ≤ 2990976) :
    even18CandidateAllowedRest (19 * q + 18) = false := by
  change even18QCoveredBool q = true at h
  cases hr : even18CandidateAllowedRest (19 * q + 18)
  · rfl
  · have hlt : ¬2990976 < 19 * q + 18 := by omega
    simp [even18QCoveredBool, hlt, hr] at h

/-- No positive candidate in the strict large-gap trap satisfies every
prime-field residue condition. -/
theorem even18_candidate_cover_of_qcover
    (qcover : ∀ q : ℕ, q < 157420 → even18QCovered q) (t : ℕ) (htpos : 1 ≤ t)
    (htbound : t ≤ 2990976) : even18CandidateAllowed t = false := by
  by_cases h19 : even18A19 ((-(81 * (t : ℤ)) : ℤ) : ZMod 19) = false
  · change (even18A19 ((-(81 * (t : ℤ)) : ℤ) : ZMod 19) &&
        even18CandidateAllowedRest t) = false
    rw [h19]
    rfl
  have h19' : even18A19 ((-(81 * (t : ℤ)) : ℤ) : ZMod 19) = true := by
    cases hA : even18A19 ((-(81 * (t : ℤ)) : ℤ) : ZMod 19) <;> simp_all
  let q := t / 19
  let r := t % 19
  have hrlt : r < 19 := by dsimp [r]; exact Nat.mod_lt t (by norm_num)
  let fr : Fin 19 := ⟨r, hrlt⟩
  have hcast : ((-(81 * (t : ℤ)) : ℤ) : ZMod 19) =
      ((-(81 * (r : ℤ)) : ℤ) : ZMod 19) := by
    push_cast
    rw [ZMod.natCast_mod]
  have hfr : even18A19 ((-(81 * (fr.val : ℤ)) : ℤ) : ZMod 19) = true := by
    dsimp [fr]
    rw [← hcast]
    exact h19'
  have hdecomp := Nat.mod_add_div t 19
  have hqbound : q < 157420 := by dsimp [q, r] at *; omega
  have hqcover := qcover q hqbound
  rcases even18_mod19_classes fr hfr with h1 | h3 | h16 | h18
  · have ht : t = 19 * q + 1 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even18_qcover_rest_1 hqcover (by omega)
    simp [even18CandidateAllowed, ht, hrfalse]
  · have ht : t = 19 * q + 3 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even18_qcover_rest_3 hqcover (by omega)
    simp [even18CandidateAllowed, ht, hrfalse]
  · have ht : t = 19 * q + 16 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even18_qcover_rest_16 hqcover (by omega)
    simp [even18CandidateAllowed, ht, hrfalse]
  · have ht : t = 19 * q + 18 := by dsimp [fr, q, r] at *; omega
    have hrfalse := even18_qcover_rest_18 hqcover (by omega)
    simp [even18CandidateAllowed, ht, hrfalse]

end Erdos686.Erdos686Variant
