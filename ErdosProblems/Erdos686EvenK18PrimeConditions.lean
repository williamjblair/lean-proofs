import ErdosProblems.Erdos686EvenK18CandidateDefs
import ErdosProblems.Erdos686EvenK18TableP19
import ErdosProblems.Erdos686EvenK18TableP857
import ErdosProblems.Erdos686EvenK18TableP797
import ErdosProblems.Erdos686EvenK18TableP541
import ErdosProblems.Erdos686EvenK18TableP467
import ErdosProblems.Erdos686EvenK18TableP491
import ErdosProblems.Erdos686EvenK18TableP523
import ErdosProblems.Erdos686EvenK18TableP509
import ErdosProblems.Erdos686EvenK18TableP487
import ErdosProblems.Erdos686EvenK18TableP359
import ErdosProblems.Erdos686EvenK18TableP431
import ErdosProblems.Erdos686EvenK18TableP281
import ErdosProblems.Erdos686EvenK18TableP373
import ErdosProblems.Erdos686EvenK18TableP439
import ErdosProblems.Erdos686EvenK18TableP463
import ErdosProblems.Erdos686EvenK18TableP409
import ErdosProblems.Erdos686EvenK18TableP347
import ErdosProblems.Erdos686EvenK18TableP433
import ErdosProblems.Erdos686EvenK18TableP389
import ErdosProblems.Erdos686EvenK18TableP521
import ErdosProblems.Erdos686EvenK18TableP307
import ErdosProblems.Erdos686EvenK18TableP443
import ErdosProblems.Erdos686EvenK18TableP421
import ErdosProblems.Erdos686EvenK18TableP227
import ErdosProblems.Erdos686EvenK18TableP311
import ErdosProblems.Erdos686EvenK18TableP419
import ErdosProblems.Erdos686EvenK18TableP271
import ErdosProblems.Erdos686EvenK18TableP331
import ErdosProblems.Erdos686EvenK18TableP193
import ErdosProblems.Erdos686EvenK18TableP379
import ErdosProblems.Erdos686EvenK18TableP367
import ErdosProblems.Erdos686EvenK18TableP353
import ErdosProblems.Erdos686EvenK18TableP191
import ErdosProblems.Erdos686EvenK18TableP241
import ErdosProblems.Erdos686EvenK18TableP337
import ErdosProblems.Erdos686EvenK18TableP349
import ErdosProblems.Erdos686EvenK18TableP269
import ErdosProblems.Erdos686EvenK18TableP397
import ErdosProblems.Erdos686EvenK18TableP317
import ErdosProblems.Erdos686EvenK18TableP283
import ErdosProblems.Erdos686EvenK18TableP211
import ErdosProblems.Erdos686EvenK18TableP251
import ErdosProblems.Erdos686EvenK18TableP173
import ErdosProblems.Erdos686EvenK18TableP313
import ErdosProblems.Erdos686EvenK18TableP383
import ErdosProblems.Erdos686EvenK18TableP137
import ErdosProblems.Erdos686EvenK18TableP229
import ErdosProblems.Erdos686EvenK18TableP257
import ErdosProblems.Erdos686EvenK18TableP179
import ErdosProblems.Erdos686EvenK18TableP181
import ErdosProblems.Erdos686EvenK18TableP151
import ErdosProblems.Erdos686EvenK18TableP239
import ErdosProblems.Erdos686EvenK18TableP149
import ErdosProblems.Erdos686EvenK18TableP223
import ErdosProblems.Erdos686EvenK18TableP97
import ErdosProblems.Erdos686EvenK18TableP131
import ErdosProblems.Erdos686EvenK18TableP139
import ErdosProblems.Erdos686EvenK18TableP197
import ErdosProblems.Erdos686EvenK18TableP233
import ErdosProblems.Erdos686EvenK18TableP263
import ErdosProblems.Erdos686EvenK18TableP277
import ErdosProblems.Erdos686EvenK18TableP293

namespace Erdos686.Erdos686Variant

private lemma k18_allowed_int
    {p : ℕ} [NeZero p] (A : ZMod p → Bool)
    (hallow : ∀ w v : ZMod p,
      evenTable18S w = 4 * evenTable18S v →
        A (evenTable18T w - 2 * evenTable18T v) = true)
    {w v m : ℤ} (hS : evenTable18S w = 4 * evenTable18S v)
    (hm : m = evenTable18T w - 2 * evenTable18T v) : A (m : ZMod p) = true := by
  have hSp : evenTable18S (w : ZMod p) = 4 * evenTable18S (v : ZMod p) := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) hS
    simpa [evenTable18S] using h
  subst m
  simpa [evenTable18T] using hallow (w : ZMod p) (v : ZMod p) hSp

/-- Every integral center pair induces all 62 residue conditions. -/
theorem even18_candidate_allowed_of_centers
    {w v : ℤ} {t : ℕ} (hS : evenTable18S w = 4 * evenTable18S v)
    (hm : -(81 * (t : ℤ)) = evenTable18T w - 2 * evenTable18T v) :
    even18CandidateAllowed t = true := by
  have h19 := k18_allowed_int even18A19 even18_allowed_19 hS hm
  have h857 := k18_allowed_int even18A857 even18_allowed_857 hS hm
  have h797 := k18_allowed_int even18A797 even18_allowed_797 hS hm
  have h541 := k18_allowed_int even18A541 even18_allowed_541 hS hm
  have h467 := k18_allowed_int even18A467 even18_allowed_467 hS hm
  have h491 := k18_allowed_int even18A491 even18_allowed_491 hS hm
  have h523 := k18_allowed_int even18A523 even18_allowed_523 hS hm
  have h509 := k18_allowed_int even18A509 even18_allowed_509 hS hm
  have h487 := k18_allowed_int even18A487 even18_allowed_487 hS hm
  have h359 := k18_allowed_int even18A359 even18_allowed_359 hS hm
  have h431 := k18_allowed_int even18A431 even18_allowed_431 hS hm
  have h281 := k18_allowed_int even18A281 even18_allowed_281 hS hm
  have h373 := k18_allowed_int even18A373 even18_allowed_373 hS hm
  have h439 := k18_allowed_int even18A439 even18_allowed_439 hS hm
  have h463 := k18_allowed_int even18A463 even18_allowed_463 hS hm
  have h409 := k18_allowed_int even18A409 even18_allowed_409 hS hm
  have h347 := k18_allowed_int even18A347 even18_allowed_347 hS hm
  have h433 := k18_allowed_int even18A433 even18_allowed_433 hS hm
  have h389 := k18_allowed_int even18A389 even18_allowed_389 hS hm
  have h521 := k18_allowed_int even18A521 even18_allowed_521 hS hm
  have h307 := k18_allowed_int even18A307 even18_allowed_307 hS hm
  have h443 := k18_allowed_int even18A443 even18_allowed_443 hS hm
  have h421 := k18_allowed_int even18A421 even18_allowed_421 hS hm
  have h227 := k18_allowed_int even18A227 even18_allowed_227 hS hm
  have h311 := k18_allowed_int even18A311 even18_allowed_311 hS hm
  have h419 := k18_allowed_int even18A419 even18_allowed_419 hS hm
  have h271 := k18_allowed_int even18A271 even18_allowed_271 hS hm
  have h331 := k18_allowed_int even18A331 even18_allowed_331 hS hm
  have h193 := k18_allowed_int even18A193 even18_allowed_193 hS hm
  have h379 := k18_allowed_int even18A379 even18_allowed_379 hS hm
  have h367 := k18_allowed_int even18A367 even18_allowed_367 hS hm
  have h353 := k18_allowed_int even18A353 even18_allowed_353 hS hm
  have h191 := k18_allowed_int even18A191 even18_allowed_191 hS hm
  have h241 := k18_allowed_int even18A241 even18_allowed_241 hS hm
  have h337 := k18_allowed_int even18A337 even18_allowed_337 hS hm
  have h349 := k18_allowed_int even18A349 even18_allowed_349 hS hm
  have h269 := k18_allowed_int even18A269 even18_allowed_269 hS hm
  have h397 := k18_allowed_int even18A397 even18_allowed_397 hS hm
  have h317 := k18_allowed_int even18A317 even18_allowed_317 hS hm
  have h283 := k18_allowed_int even18A283 even18_allowed_283 hS hm
  have h211 := k18_allowed_int even18A211 even18_allowed_211 hS hm
  have h251 := k18_allowed_int even18A251 even18_allowed_251 hS hm
  have h173 := k18_allowed_int even18A173 even18_allowed_173 hS hm
  have h313 := k18_allowed_int even18A313 even18_allowed_313 hS hm
  have h383 := k18_allowed_int even18A383 even18_allowed_383 hS hm
  have h137 := k18_allowed_int even18A137 even18_allowed_137 hS hm
  have h229 := k18_allowed_int even18A229 even18_allowed_229 hS hm
  have h257 := k18_allowed_int even18A257 even18_allowed_257 hS hm
  have h179 := k18_allowed_int even18A179 even18_allowed_179 hS hm
  have h181 := k18_allowed_int even18A181 even18_allowed_181 hS hm
  have h151 := k18_allowed_int even18A151 even18_allowed_151 hS hm
  have h239 := k18_allowed_int even18A239 even18_allowed_239 hS hm
  have h149 := k18_allowed_int even18A149 even18_allowed_149 hS hm
  have h223 := k18_allowed_int even18A223 even18_allowed_223 hS hm
  have h97 := k18_allowed_int even18A97 even18_allowed_97 hS hm
  have h131 := k18_allowed_int even18A131 even18_allowed_131 hS hm
  have h139 := k18_allowed_int even18A139 even18_allowed_139 hS hm
  have h197 := k18_allowed_int even18A197 even18_allowed_197 hS hm
  have h233 := k18_allowed_int even18A233 even18_allowed_233 hS hm
  have h263 := k18_allowed_int even18A263 even18_allowed_263 hS hm
  have h277 := k18_allowed_int even18A277 even18_allowed_277 hS hm
  have h293 := k18_allowed_int even18A293 even18_allowed_293 hS hm
  simp only [even18CandidateAllowed, even18CandidateAllowedRest,
    h19, h857, h797, h541, h467, h491, h523, h509,
    h487, h359, h431, h281, h373, h439, h463, h409,
    h347, h433, h389, h521, h307, h443, h421, h227,
    h311, h419, h271, h331, h193, h379, h367, h353,
    h191, h241, h337, h349, h269, h397, h317, h283,
    h211, h251, h173, h313, h383, h137, h229, h257,
    h179, h181, h151, h239, h149, h223, h97, h131,
    h139, h197, h233, h263, h277, h293,
    Bool.true_and]

end Erdos686.Erdos686Variant
