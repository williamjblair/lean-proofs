import ErdosProblems.Erdos686.EvenK.K18.Table.TableDefs
namespace Erdos686.Erdos686Variant

/-- The residue conditions after the four-class modulus-19 prefilter. -/
def even18CandidateAllowedRest (t : ℕ) : Bool :=
  even18A857 ((-(81 * (t : ℤ)) : ℤ) : ZMod 857) &&
  even18A797 ((-(81 * (t : ℤ)) : ℤ) : ZMod 797) &&
  even18A541 ((-(81 * (t : ℤ)) : ℤ) : ZMod 541) &&
  even18A467 ((-(81 * (t : ℤ)) : ℤ) : ZMod 467) &&
  even18A491 ((-(81 * (t : ℤ)) : ℤ) : ZMod 491) &&
  even18A523 ((-(81 * (t : ℤ)) : ℤ) : ZMod 523) &&
  even18A509 ((-(81 * (t : ℤ)) : ℤ) : ZMod 509) &&
  even18A487 ((-(81 * (t : ℤ)) : ℤ) : ZMod 487) &&
  even18A359 ((-(81 * (t : ℤ)) : ℤ) : ZMod 359) &&
  even18A431 ((-(81 * (t : ℤ)) : ℤ) : ZMod 431) &&
  even18A281 ((-(81 * (t : ℤ)) : ℤ) : ZMod 281) &&
  even18A373 ((-(81 * (t : ℤ)) : ℤ) : ZMod 373) &&
  even18A439 ((-(81 * (t : ℤ)) : ℤ) : ZMod 439) &&
  even18A463 ((-(81 * (t : ℤ)) : ℤ) : ZMod 463) &&
  even18A409 ((-(81 * (t : ℤ)) : ℤ) : ZMod 409) &&
  even18A347 ((-(81 * (t : ℤ)) : ℤ) : ZMod 347) &&
  even18A433 ((-(81 * (t : ℤ)) : ℤ) : ZMod 433) &&
  even18A389 ((-(81 * (t : ℤ)) : ℤ) : ZMod 389) &&
  even18A521 ((-(81 * (t : ℤ)) : ℤ) : ZMod 521) &&
  even18A307 ((-(81 * (t : ℤ)) : ℤ) : ZMod 307) &&
  even18A443 ((-(81 * (t : ℤ)) : ℤ) : ZMod 443) &&
  even18A421 ((-(81 * (t : ℤ)) : ℤ) : ZMod 421) &&
  even18A227 ((-(81 * (t : ℤ)) : ℤ) : ZMod 227) &&
  even18A311 ((-(81 * (t : ℤ)) : ℤ) : ZMod 311) &&
  even18A419 ((-(81 * (t : ℤ)) : ℤ) : ZMod 419) &&
  even18A271 ((-(81 * (t : ℤ)) : ℤ) : ZMod 271) &&
  even18A331 ((-(81 * (t : ℤ)) : ℤ) : ZMod 331) &&
  even18A193 ((-(81 * (t : ℤ)) : ℤ) : ZMod 193) &&
  even18A379 ((-(81 * (t : ℤ)) : ℤ) : ZMod 379) &&
  even18A367 ((-(81 * (t : ℤ)) : ℤ) : ZMod 367) &&
  even18A353 ((-(81 * (t : ℤ)) : ℤ) : ZMod 353) &&
  even18A191 ((-(81 * (t : ℤ)) : ℤ) : ZMod 191) &&
  even18A241 ((-(81 * (t : ℤ)) : ℤ) : ZMod 241) &&
  even18A337 ((-(81 * (t : ℤ)) : ℤ) : ZMod 337) &&
  even18A349 ((-(81 * (t : ℤ)) : ℤ) : ZMod 349) &&
  even18A269 ((-(81 * (t : ℤ)) : ℤ) : ZMod 269) &&
  even18A397 ((-(81 * (t : ℤ)) : ℤ) : ZMod 397) &&
  even18A317 ((-(81 * (t : ℤ)) : ℤ) : ZMod 317) &&
  even18A283 ((-(81 * (t : ℤ)) : ℤ) : ZMod 283) &&
  even18A211 ((-(81 * (t : ℤ)) : ℤ) : ZMod 211) &&
  even18A251 ((-(81 * (t : ℤ)) : ℤ) : ZMod 251) &&
  even18A173 ((-(81 * (t : ℤ)) : ℤ) : ZMod 173) &&
  even18A313 ((-(81 * (t : ℤ)) : ℤ) : ZMod 313) &&
  even18A383 ((-(81 * (t : ℤ)) : ℤ) : ZMod 383) &&
  even18A137 ((-(81 * (t : ℤ)) : ℤ) : ZMod 137) &&
  even18A229 ((-(81 * (t : ℤ)) : ℤ) : ZMod 229) &&
  even18A257 ((-(81 * (t : ℤ)) : ℤ) : ZMod 257) &&
  even18A179 ((-(81 * (t : ℤ)) : ℤ) : ZMod 179) &&
  even18A181 ((-(81 * (t : ℤ)) : ℤ) : ZMod 181) &&
  even18A151 ((-(81 * (t : ℤ)) : ℤ) : ZMod 151) &&
  even18A239 ((-(81 * (t : ℤ)) : ℤ) : ZMod 239) &&
  even18A149 ((-(81 * (t : ℤ)) : ℤ) : ZMod 149) &&
  even18A223 ((-(81 * (t : ℤ)) : ℤ) : ZMod 223) &&
  even18A97 ((-(81 * (t : ℤ)) : ℤ) : ZMod 97) &&
  even18A131 ((-(81 * (t : ℤ)) : ℤ) : ZMod 131) &&
  even18A139 ((-(81 * (t : ℤ)) : ℤ) : ZMod 139) &&
  even18A197 ((-(81 * (t : ℤ)) : ℤ) : ZMod 197) &&
  even18A233 ((-(81 * (t : ℤ)) : ℤ) : ZMod 233) &&
  even18A263 ((-(81 * (t : ℤ)) : ℤ) : ZMod 263) &&
  even18A277 ((-(81 * (t : ℤ)) : ℤ) : ZMod 277) &&
  even18A293 ((-(81 * (t : ℤ)) : ℤ) : ZMod 293)

/-- All prime-field residue conditions used by the large-gap k=18 cover. -/
def even18CandidateAllowed (t : ℕ) : Bool :=
  even18A19 ((-(81 * (t : ℤ)) : ℤ) : ZMod 19) &&
    even18CandidateAllowedRest t

/-- Boolean certificate for the four modulus-19 progressions at a quotient. -/
def even18QCoveredBool (q : ℕ) : Bool :=
  ((2990976 < 19 * q + 1) || !(even18CandidateAllowedRest (19 * q + 1))) &&
  ((2990976 < 19 * q + 3) || !(even18CandidateAllowedRest (19 * q + 3))) &&
  ((2990976 < 19 * q + 16) || !(even18CandidateAllowedRest (19 * q + 16))) &&
  ((2990976 < 19 * q + 18) || !(even18CandidateAllowedRest (19 * q + 18)))

abbrev even18QCovered (q : ℕ) : Prop := even18QCoveredBool q = true

/-- Balanced scan of 2^e consecutive values. -/
def even18ScanPow (f : ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => f lo
  | e + 1 => even18ScanPow f lo e && even18ScanPow f (lo + 2 ^ e) e

theorem even18ScanPow_get {f : ℕ → Bool} {lo e q : ℕ}
    (hscan : even18ScanPow f lo e = true)
    (hlo : lo ≤ q) (hhi : q < lo + 2 ^ e) : f q = true := by
  induction e generalizing lo with
  | zero =>
      simp only [pow_zero, Nat.add_one] at hhi
      have : q = lo := by omega
      simpa [even18ScanPow, this] using hscan
  | succ e ih =>
      simp only [even18ScanPow, Bool.and_eq_true] at hscan
      rw [pow_succ] at hhi
      by_cases hmid : q < lo + 2 ^ e
      · exact ih hscan.1 hlo hmid
      · exact ih hscan.2 (by omega) (by omega)

end Erdos686.Erdos686Variant
