import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b29_s2_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (32000000 + (r.val : ZMod 499)) + 29))) = true →
      (1635095401623228141532869002734908603828238334370435528792604302136238574541543294301676716650766135572967088328191137032127620312379220135785077906687).testBit r.val = true := by decide

theorem even22_b29_s2_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (32000000 + (i : ZMod 499)) + 29))) = true) :
    (1635095401623228141532869002734908603828238334370435528792604302136238574541543294301676716650766135572967088328191137032127620312379220135785077906687).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_499_fin r
  change even22A499
    (-(33 * (46 * (32000000 + ((i % 499 : ℕ) : ZMod 499)) + 29))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (32000000 + (r.val : ZMod 503)) + 29))) = true →
      (25982536925848905820515046175098982311964838426325438814300731810212186890095762298442054287504247816245712099932047321049347287168319757097258919870457).testBit r.val = true := by decide

theorem even22_b29_s2_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (32000000 + (i : ZMod 503)) + 29))) = true) :
    (25982536925848905820515046175098982311964838426325438814300731810212186890095762298442054287504247816245712099932047321049347287168319757097258919870457).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_503_fin r
  change even22A503
    (-(33 * (46 * (32000000 + ((i % 503 : ℕ) : ZMod 503)) + 29))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (32000000 + (r.val : ZMod 509)) + 29))) = true →
      (1201307128301330579421534233403049101575766439424800085320828914283261745590219395997859258801162004728829472589460756395638999242608280064997659951225831).testBit r.val = true := by decide

theorem even22_b29_s2_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (32000000 + (i : ZMod 509)) + 29))) = true) :
    (1201307128301330579421534233403049101575766439424800085320828914283261745590219395997859258801162004728829472589460756395638999242608280064997659951225831).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_509_fin r
  change even22A509
    (-(33 * (46 * (32000000 + ((i % 509 : ℕ) : ZMod 509)) + 29))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (32000000 + (r.val : ZMod 521)) + 29))) = true →
      (5066473765548714135582186257826401163131679937932552197667604940911405765862739862877242674222593817492012559504499507730120656391209021973686577488160555005).testBit r.val = true := by decide

theorem even22_b29_s2_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (32000000 + (i : ZMod 521)) + 29))) = true) :
    (5066473765548714135582186257826401163131679937932552197667604940911405765862739862877242674222593817492012559504499507730120656391209021973686577488160555005).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_521_fin r
  change even22A521
    (-(33 * (46 * (32000000 + ((i % 521 : ℕ) : ZMod 521)) + 29))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (32000000 + (r.val : ZMod 523)) + 29))) = true →
      (27459137447811209600080750735189788758251212221628590827688614559216316195642871536042868198213030906502671544564472819161938301961108411238947123464335523194).testBit r.val = true := by decide

theorem even22_b29_s2_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (32000000 + (i : ZMod 523)) + 29))) = true) :
    (27459137447811209600080750735189788758251212221628590827688614559216316195642871536042868198213030906502671544564472819161938301961108411238947123464335523194).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_523_fin r
  change even22A523
    (-(33 * (46 * (32000000 + ((i % 523 : ℕ) : ZMod 523)) + 29))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (32000000 + (r.val : ZMod 541)) + 29))) = true →
      (1349645791087480960845380631871890214427574621921531826611017635915725004939614731538099825708711266782993516723921115143996148306654732425407872235614474390732783).testBit r.val = true := by decide

theorem even22_b29_s2_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (32000000 + (i : ZMod 541)) + 29))) = true) :
    (1349645791087480960845380631871890214427574621921531826611017635915725004939614731538099825708711266782993516723921115143996148306654732425407872235614474390732783).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_541_fin r
  change even22A541
    (-(33 * (46 * (32000000 + ((i % 541 : ℕ) : ZMod 541)) + 29))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (32000000 + (r.val : ZMod 547)) + 29))) = true →
      (456622175969139630473218365958609950010358580401878516220952265670454124155826455566268308150861255946526296352676550790381163680523700956612874077887286849740726015).testBit r.val = true := by decide

theorem even22_b29_s2_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (32000000 + (i : ZMod 547)) + 29))) = true) :
    (456622175969139630473218365958609950010358580401878516220952265670454124155826455566268308150861255946526296352676550790381163680523700956612874077887286849740726015).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_547_fin r
  change even22A547
    (-(33 * (46 * (32000000 + ((i % 547 : ℕ) : ZMod 547)) + 29))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b29_s2_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (32000000 + (r.val : ZMod 557)) + 29))) = true →
      (468461979985101025409630952829637663995530409515051905363423121966599436005056890833541081454690320127619327400507104464456660550558229086875401146466885876134822281210).testBit r.val = true := by decide

theorem even22_b29_s2_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (32000000 + (i : ZMod 557)) + 29))) = true) :
    (468461979985101025409630952829637663995530409515051905363423121966599436005056890833541081454690320127619327400507104464456660550558229086875401146466885876134822281210).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b29_s2_map_557_fin r
  change even22A557
    (-(33 * (46 * (32000000 + ((i % 557 : ℕ) : ZMod 557)) + 29))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB29S2Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 1635095401623228141532869002734908603828238334370435528792604302136238574541543294301676716650766135572967088328191137032127620312379220135785077906687) (.leaf 503 25982536925848905820515046175098982311964838426325438814300731810212186890095762298442054287504247816245712099932047321049347287168319757097258919870457)) (.node (.leaf 509 1201307128301330579421534233403049101575766439424800085320828914283261745590219395997859258801162004728829472589460756395638999242608280064997659951225831) (.leaf 521 5066473765548714135582186257826401163131679937932552197667604940911405765862739862877242674222593817492012559504499507730120656391209021973686577488160555005))) (.node (.node (.leaf 523 27459137447811209600080750735189788758251212221628590827688614559216316195642871536042868198213030906502671544564472819161938301961108411238947123464335523194) (.leaf 541 1349645791087480960845380631871890214427574621921531826611017635915725004939614731538099825708711266782993516723921115143996148306654732425407872235614474390732783)) (.node (.leaf 547 456622175969139630473218365958609950010358580401878516220952265670454124155826455566268308150861255946526296352676550790381163680523700956612874077887286849740726015) (.leaf 557 468461979985101025409630952829637663995530409515051905363423121966599436005056890833541081454690320127619327400507104464456660550558229086875401146466885876134822281210))))

set_option maxRecDepth 10000 in
theorem even22PackedB29S2Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (32000000 + (i : ℤ)) + 29)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB29S2Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b29_s2_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
