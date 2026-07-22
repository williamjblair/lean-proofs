import ErdosProblems.Erdos686.EvenK.K28.FiniteStrip
namespace Erdos686.Erdos686Variant

/-- Residue conditions after the four-class modulus-29 prefilter. -/
def even28CandidateAllowedRest (t : ℕ) : Bool :=
  even28A349 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 349) &&
    even28A347 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 347) &&
    even28A317 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 317) &&
    even28A331 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 331) &&
    even28A353 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 353) &&
    even28A283 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 283) &&
    even28A337 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 337) &&
    even28A293 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 293) &&
    even28A281 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 281) &&
    even28A307 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 307) &&
    even28A257 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 257) &&
    even28A271 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 271) &&
    even28A239 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 239) &&
    even28A197 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 197) &&
    even28A313 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 313) &&
    even28A241 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 241) &&
    even28A277 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 277) &&
    even28A5 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 5) &&
    even28A37 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 37)

/-- All prime-field conditions in the k=28 large-gap cover. -/
def even28CandidateAllowed (t : ℕ) : Bool :=
  even28A29 ((-(50176 * (t : ℤ)) : ℤ) : ZMod 29) &&
    even28CandidateAllowedRest t

def even28QCoveredBool (q : ℕ) : Bool :=
  ((1049958 < 29 * q + 5) || !(even28CandidateAllowedRest (29 * q + 5))) &&
  ((1049958 < 29 * q + 14) || !(even28CandidateAllowedRest (29 * q + 14))) &&
  ((1049958 < 29 * q + 15) || !(even28CandidateAllowedRest (29 * q + 15))) &&
  ((1049958 < 29 * q + 24) || !(even28CandidateAllowedRest (29 * q + 24)))

abbrev even28QCovered (q : ℕ) : Prop := even28QCoveredBool q = true

def even28ScanPow (f : ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => f lo
  | e + 1 => even28ScanPow f lo e && even28ScanPow f (lo + 2 ^ e) e

theorem even28ScanPow_get {f : ℕ → Bool} {lo e q : ℕ}
    (hscan : even28ScanPow f lo e = true)
    (hlo : lo ≤ q) (hhi : q < lo + 2 ^ e) : f q = true := by
  induction e generalizing lo with
  | zero =>
      simp only [pow_zero, Nat.add_one] at hhi
      have : q = lo := by omega
      simpa [even28ScanPow, this] using hscan
  | succ e ih =>
      simp only [even28ScanPow, Bool.and_eq_true] at hscan
      rw [pow_succ] at hhi
      by_cases hmid : q < lo + 2 ^ e
      · exact ih hscan.1 hlo hmid
      · exact ih hscan.2 (by omega) (by omega)

end Erdos686.Erdos686Variant
