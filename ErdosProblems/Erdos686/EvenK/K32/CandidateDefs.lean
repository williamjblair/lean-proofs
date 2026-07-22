import ErdosProblems.Erdos686.EvenK.K32.Defs
namespace Erdos686.Erdos686Variant

/-- Residue conditions after the seven-class modulus-17 prefilter. -/
def even32CandidateAllowedRest (t : ℕ) : Bool :=
  even32A521 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 521) &&
    even32A509 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 509) &&
    even32A491 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 491) &&
    even32A457 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 457) &&
    even32A463 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 463) &&
    even32A487 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 487) &&
    even32A383 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 383) &&
    even32A449 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 449) &&
    even32A439 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 439) &&
    even32A499 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 499) &&
    even32A443 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 443) &&
    even32A7 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 7) &&
    even32A431 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 431) &&
    even32A397 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 397) &&
    even32A467 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 467) &&
    even32A409 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 409)

/-- All prime-field conditions in the k=32 large-gap cover. -/
def even32CandidateAllowed (t : ℕ) : Bool :=
  even32A17 ((-(3221225472 * (t : ℤ)) : ℤ) : ZMod 17) &&
    even32CandidateAllowedRest t

def even32QCoveredBool (q : ℕ) : Bool :=
  ((431188 < 17 * q) || !(even32CandidateAllowedRest (17 * q))) &&
  ((431188 < 17 * q + 3) || !(even32CandidateAllowedRest (17 * q + 3))) &&
  ((431188 < 17 * q + 6) || !(even32CandidateAllowedRest (17 * q + 6))) &&
  ((431188 < 17 * q + 7) || !(even32CandidateAllowedRest (17 * q + 7))) &&
  ((431188 < 17 * q + 10) || !(even32CandidateAllowedRest (17 * q + 10))) &&
  ((431188 < 17 * q + 13) || !(even32CandidateAllowedRest (17 * q + 13))) &&
  ((431188 < 17 * q + 14) || !(even32CandidateAllowedRest (17 * q + 14)))

abbrev even32QCovered (q : ℕ) : Prop := even32QCoveredBool q = true

def even32ScanPow (f : ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => f lo
  | e + 1 => even32ScanPow f lo e && even32ScanPow f (lo + 2 ^ e) e

theorem even32ScanPow_get {f : ℕ → Bool} {lo e q : ℕ}
    (hscan : even32ScanPow f lo e = true)
    (hlo : lo ≤ q) (hhi : q < lo + 2 ^ e) : f q = true := by
  induction e generalizing lo with
  | zero =>
      simp only [pow_zero, Nat.add_one] at hhi
      have : q = lo := by omega
      simpa [even32ScanPow, this] using hscan
  | succ e ih =>
      simp only [even32ScanPow, Bool.and_eq_true] at hscan
      rw [pow_succ] at hhi
      by_cases hmid : q < lo + 2 ^ e
      · exact ih hscan.1 hlo hmid
      · exact ih hscan.2 (by omega) (by omega)

end Erdos686.Erdos686Variant
