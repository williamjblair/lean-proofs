import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b21_s1_map_401_fin : ∀ r : Fin 401,
    even22A401 (-(33 * (46 * (16000000 + (r.val : ZMod 401)) + 21))) = true →
      (5081282718467016205489851722135780341095263279745153614890770525687030582485731476747858591439131545346681892809483992575).testBit r.val = true := by decide

theorem even22_b21_s1_map_401 (i : ℕ)
    (h : even22A401 (-(33 * (46 * (16000000 + (i : ZMod 401)) + 21))) = true) :
    (5081282718467016205489851722135780341095263279745153614890770525687030582485731476747858591439131545346681892809483992575).testBit (i % 401) = true := by
  let r : Fin 401 := ⟨i % 401, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_401_fin r
  change even22A401
    (-(33 * (46 * (16000000 + ((i % 401 : ℕ) : ZMod 401)) + 21))) = true
  have hcast : (i : ZMod 401) = ((i % 401 : ℕ) : ZMod 401) :=
    (ZMod.natCast_mod i 401).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_409_fin : ∀ r : Fin 409,
    even22A409 (-(33 * (46 * (16000000 + (r.val : ZMod 409)) + 21))) = true →
      (1322069068177971361297183029517011611011870359391966203222128138750380276843909413435853104938351439463223735398954237411263).testBit r.val = true := by decide

theorem even22_b21_s1_map_409 (i : ℕ)
    (h : even22A409 (-(33 * (46 * (16000000 + (i : ZMod 409)) + 21))) = true) :
    (1322069068177971361297183029517011611011870359391966203222128138750380276843909413435853104938351439463223735398954237411263).testBit (i % 409) = true := by
  let r : Fin 409 := ⟨i % 409, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_409_fin r
  change even22A409
    (-(33 * (46 * (16000000 + ((i % 409 : ℕ) : ZMod 409)) + 21))) = true
  have hcast : (i : ZMod 409) = ((i % 409 : ℕ) : ZMod 409) :=
    (ZMod.natCast_mod i 409).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_419_fin : ∀ r : Fin 419,
    even22A419 (-(33 * (46 * (16000000 + (r.val : ZMod 419)) + 21))) = true →
      (1322101285464311115421181568096182519995270580684054654383902191498822149919949024286376360103640970454637742430897049077546495).testBit r.val = true := by decide

theorem even22_b21_s1_map_419 (i : ℕ)
    (h : even22A419 (-(33 * (46 * (16000000 + (i : ZMod 419)) + 21))) = true) :
    (1322101285464311115421181568096182519995270580684054654383902191498822149919949024286376360103640970454637742430897049077546495).testBit (i % 419) = true := by
  let r : Fin 419 := ⟨i % 419, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_419_fin r
  change even22A419
    (-(33 * (46 * (16000000 + ((i % 419 : ℕ) : ZMod 419)) + 21))) = true
  have hcast : (i : ZMod 419) = ((i % 419 : ℕ) : ZMod 419) :=
    (ZMod.natCast_mod i 419).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_421_fin : ∀ r : Fin 421,
    even22A421 (-(33 * (46 * (16000000 + (r.val : ZMod 421)) + 21))) = true →
      (5288444920942721485170313956094123849462858236540116908762399032726944820946323948056364304728643900340892820225330047145147895).testBit r.val = true := by decide

theorem even22_b21_s1_map_421 (i : ℕ)
    (h : even22A421 (-(33 * (46 * (16000000 + (i : ZMod 421)) + 21))) = true) :
    (5288444920942721485170313956094123849462858236540116908762399032726944820946323948056364304728643900340892820225330047145147895).testBit (i % 421) = true := by
  let r : Fin 421 := ⟨i % 421, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_421_fin r
  change even22A421
    (-(33 * (46 * (16000000 + ((i % 421 : ℕ) : ZMod 421)) + 21))) = true
  have hcast : (i : ZMod 421) = ((i % 421 : ℕ) : ZMod 421) :=
    (ZMod.natCast_mod i 421).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_431_fin : ∀ r : Fin 431,
    even22A431 (-(33 * (46 * (16000000 + (r.val : ZMod 431)) + 21))) = true →
      (5445151715999556643121150169132265046281435424851972066305752860676504024279020421828916186727922327443304385118015295669467872255).testBit r.val = true := by decide

theorem even22_b21_s1_map_431 (i : ℕ)
    (h : even22A431 (-(33 * (46 * (16000000 + (i : ZMod 431)) + 21))) = true) :
    (5445151715999556643121150169132265046281435424851972066305752860676504024279020421828916186727922327443304385118015295669467872255).testBit (i % 431) = true := by
  let r : Fin 431 := ⟨i % 431, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_431_fin r
  change even22A431
    (-(33 * (46 * (16000000 + ((i % 431 : ℕ) : ZMod 431)) + 21))) = true
  have hcast : (i : ZMod 431) = ((i % 431 : ℕ) : ZMod 431) :=
    (ZMod.natCast_mod i 431).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_433_fin : ∀ r : Fin 433,
    even22A433 (-(33 * (46 * (16000000 + (r.val : ZMod 433)) + 21))) = true →
      (22181346976071017912796413074004893016610975889943134720777197521253099584139330399859328440748409768199002068914290585760383889391).testBit r.val = true := by decide

theorem even22_b21_s1_map_433 (i : ℕ)
    (h : even22A433 (-(33 * (46 * (16000000 + (i : ZMod 433)) + 21))) = true) :
    (22181346976071017912796413074004893016610975889943134720777197521253099584139330399859328440748409768199002068914290585760383889391).testBit (i % 433) = true := by
  let r : Fin 433 := ⟨i % 433, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_433_fin r
  change even22A433
    (-(33 * (46 * (16000000 + ((i % 433 : ℕ) : ZMod 433)) + 21))) = true
  have hcast : (i : ZMod 433) = ((i % 433 : ℕ) : ZMod 433) :=
    (ZMod.natCast_mod i 433).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_439_fin : ∀ r : Fin 439,
    even22A439 (-(33 * (46 * (16000000 + (r.val : ZMod 439)) + 21))) = true →
      (1130989255109563222067296819135474157251948021331024372558240800976223070273252592437830232696427538297250023766826609026055439111101).testBit r.val = true := by decide

theorem even22_b21_s1_map_439 (i : ℕ)
    (h : even22A439 (-(33 * (46 * (16000000 + (i : ZMod 439)) + 21))) = true) :
    (1130989255109563222067296819135474157251948021331024372558240800976223070273252592437830232696427538297250023766826609026055439111101).testBit (i % 439) = true := by
  let r : Fin 439 := ⟨i % 439, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_439_fin r
  change even22A439
    (-(33 * (46 * (16000000 + ((i % 439 : ℕ) : ZMod 439)) + 21))) = true
  have hcast : (i : ZMod 439) = ((i % 439 : ℕ) : ZMod 439) :=
    (ZMod.natCast_mod i 439).symm
  rw [← hcast]
  exact h


theorem even22_b21_s1_map_443_fin : ∀ r : Fin 443,
    even22A443 (-(33 * (46 * (16000000 + (r.val : ZMod 443)) + 21))) = true →
      (21277356529482104966828028452465231865919992919230556984186870081258026981797619480938022901280983379687196714312263566552446542020607).testBit r.val = true := by decide

theorem even22_b21_s1_map_443 (i : ℕ)
    (h : even22A443 (-(33 * (46 * (16000000 + (i : ZMod 443)) + 21))) = true) :
    (21277356529482104966828028452465231865919992919230556984186870081258026981797619480938022901280983379687196714312263566552446542020607).testBit (i % 443) = true := by
  let r : Fin 443 := ⟨i % 443, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b21_s1_map_443_fin r
  change even22A443
    (-(33 * (46 * (16000000 + ((i % 443 : ℕ) : ZMod 443)) + 21))) = true
  have hcast : (i : ZMod 443) = ((i % 443 : ℕ) : ZMod 443) :=
    (ZMod.natCast_mod i 443).symm
  rw [← hcast]
  exact h

def even22PackedB21S1Group6Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 401 5081282718467016205489851722135780341095263279745153614890770525687030582485731476747858591439131545346681892809483992575) (.leaf 409 1322069068177971361297183029517011611011870359391966203222128138750380276843909413435853104938351439463223735398954237411263)) (.node (.leaf 419 1322101285464311115421181568096182519995270580684054654383902191498822149919949024286376360103640970454637742430897049077546495) (.leaf 421 5288444920942721485170313956094123849462858236540116908762399032726944820946323948056364304728643900340892820225330047145147895))) (.node (.node (.leaf 431 5445151715999556643121150169132265046281435424851972066305752860676504024279020421828916186727922327443304385118015295669467872255) (.leaf 433 22181346976071017912796413074004893016610975889943134720777197521253099584139330399859328440748409768199002068914290585760383889391)) (.node (.leaf 439 1130989255109563222067296819135474157251948021331024372558240800976223070273252592437830232696427538297250023766826609026055439111101) (.leaf 443 21277356529482104966828028452465231865919992919230556984186870081258026981797619480938022901280983379687196714312263566552446542020607))))

set_option maxRecDepth 10000 in
theorem even22PackedB21S1Group6TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 16000000)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (16000000 + (i : ℤ)) + 21)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB21S1Group6Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_401 i
          have hA := even22_allowed_int even22A401 even22_allowed_401 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_409 i
          have hA := even22_allowed_int even22A409 even22_allowed_409 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_419 i
          have hA := even22_allowed_int even22A419 even22_allowed_419 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_421 i
          have hA := even22_allowed_int even22A421 even22_allowed_421 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_431 i
          have hA := even22_allowed_int even22A431 even22_allowed_431 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_433 i
          have hA := even22_allowed_int even22A433 even22_allowed_433 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_439 i
          have hA := even22_allowed_int even22A439 even22_allowed_439 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b21_s1_map_443 i
          have hA := even22_allowed_int even22A443 even22_allowed_443 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
