import ErdosProblems.Erdos686EvenK22PackedDefs

namespace Erdos686.Erdos686Variant

-- Keep finite decisions below the process-stack danger zone.
set_option maxRecDepth 10000

theorem even22_b25_s5_map_499_fin : ∀ r : Fin 499,
    even22A499 (-(33 * (46 * (80000000 + (r.val : ZMod 499)) + 25))) = true →
      (887061922634673538628588004532632670510944724284487610913828636713121223943521806594408764738888560584360950388166793297930986467599339734790827933693).testBit r.val = true := by decide

theorem even22_b25_s5_map_499 (i : ℕ)
    (h : even22A499 (-(33 * (46 * (80000000 + (i : ZMod 499)) + 25))) = true) :
    (887061922634673538628588004532632670510944724284487610913828636713121223943521806594408764738888560584360950388166793297930986467599339734790827933693).testBit (i % 499) = true := by
  let r : Fin 499 := ⟨i % 499, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_499_fin r
  change even22A499
    (-(33 * (46 * (80000000 + ((i % 499 : ℕ) : ZMod 499)) + 25))) = true
  have hcast : (i : ZMod 499) = ((i % 499 : ℕ) : ZMod 499) :=
    (ZMod.natCast_mod i 499).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_503_fin : ∀ r : Fin 503,
    even22A503 (-(33 * (46 * (80000000 + (r.val : ZMod 503)) + 25))) = true →
      (18310525200951872147260080928414462710237982219740399637578917320239803483469249173699395503949574604136093018560209473431031872745235074877318141304799).testBit r.val = true := by decide

theorem even22_b25_s5_map_503 (i : ℕ)
    (h : even22A503 (-(33 * (46 * (80000000 + (i : ZMod 503)) + 25))) = true) :
    (18310525200951872147260080928414462710237982219740399637578917320239803483469249173699395503949574604136093018560209473431031872745235074877318141304799).testBit (i % 503) = true := by
  let r : Fin 503 := ⟨i % 503, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_503_fin r
  change even22A503
    (-(33 * (46 * (80000000 + ((i % 503 : ℕ) : ZMod 503)) + 25))) = true
  have hcast : (i : ZMod 503) = ((i % 503 : ℕ) : ZMod 503) :=
    (ZMod.natCast_mod i 503).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_509_fin : ∀ r : Fin 509,
    even22A509 (-(33 * (46 * (80000000 + (r.val : ZMod 509)) + 25))) = true →
      (1545027180633284087969814487207770559840087552561190883573746247556079979109338187009661074880534093874705672475462801795163431571966658282112900647613428).testBit r.val = true := by decide

theorem even22_b25_s5_map_509 (i : ℕ)
    (h : even22A509 (-(33 * (46 * (80000000 + (i : ZMod 509)) + 25))) = true) :
    (1545027180633284087969814487207770559840087552561190883573746247556079979109338187009661074880534093874705672475462801795163431571966658282112900647613428).testBit (i % 509) = true := by
  let r : Fin 509 := ⟨i % 509, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_509_fin r
  change even22A509
    (-(33 * (46 * (80000000 + ((i % 509 : ℕ) : ZMod 509)) + 25))) = true
  have hcast : (i : ZMod 509) = ((i % 509 : ℕ) : ZMod 509) :=
    (ZMod.natCast_mod i 509).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_521_fin : ∀ r : Fin 521,
    even22A521 (-(33 * (46 * (80000000 + (r.val : ZMod 521)) + 25))) = true →
      (3372063694373490458982643185052100453383034293736337510137611708064364563833984456565956531994911450244534405778700999254640762190586586452769388843369459647).testBit r.val = true := by decide

theorem even22_b25_s5_map_521 (i : ℕ)
    (h : even22A521 (-(33 * (46 * (80000000 + (i : ZMod 521)) + 25))) = true) :
    (3372063694373490458982643185052100453383034293736337510137611708064364563833984456565956531994911450244534405778700999254640762190586586452769388843369459647).testBit (i % 521) = true := by
  let r : Fin 521 := ⟨i % 521, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_521_fin r
  change even22A521
    (-(33 * (46 * (80000000 + ((i % 521 : ℕ) : ZMod 521)) + 25))) = true
  have hcast : (i : ZMod 521) = ((i % 521 : ℕ) : ZMod 521) :=
    (ZMod.natCast_mod i 521).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_523_fin : ∀ r : Fin 523,
    even22A523 (-(33 * (46 * (80000000 + (r.val : ZMod 523)) + 25))) = true →
      (25434611233927084839351117616592587968344067061103719210639316773634919776296793627138741967446934586363584384122452110285898419644469903787310054156636225407).testBit r.val = true := by decide

theorem even22_b25_s5_map_523 (i : ℕ)
    (h : even22A523 (-(33 * (46 * (80000000 + (i : ZMod 523)) + 25))) = true) :
    (25434611233927084839351117616592587968344067061103719210639316773634919776296793627138741967446934586363584384122452110285898419644469903787310054156636225407).testBit (i % 523) = true := by
  let r : Fin 523 := ⟨i % 523, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_523_fin r
  change even22A523
    (-(33 * (46 * (80000000 + ((i % 523 : ℕ) : ZMod 523)) + 25))) = true
  have hcast : (i : ZMod 523) = ((i % 523 : ℕ) : ZMod 523) :=
    (ZMod.natCast_mod i 523).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_541_fin : ∀ r : Fin 541,
    even22A541 (-(33 * (46 * (80000000 + (r.val : ZMod 541)) + 25))) = true →
      (3598230868875623841975302125654390711272430336043863581034422463074246623239702941002081295225485421826761977418737074620476757030885967769693571618488730713781694).testBit r.val = true := by decide

theorem even22_b25_s5_map_541 (i : ℕ)
    (h : even22A541 (-(33 * (46 * (80000000 + (i : ZMod 541)) + 25))) = true) :
    (3598230868875623841975302125654390711272430336043863581034422463074246623239702941002081295225485421826761977418737074620476757030885967769693571618488730713781694).testBit (i % 541) = true := by
  let r : Fin 541 := ⟨i % 541, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_541_fin r
  change even22A541
    (-(33 * (46 * (80000000 + ((i % 541 : ℕ) : ZMod 541)) + 25))) = true
  have hcast : (i : ZMod 541) = ((i % 541 : ℕ) : ZMod 541) :=
    (ZMod.natCast_mod i 541).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_547_fin : ∀ r : Fin 547,
    even22A547 (-(33 * (46 * (80000000 + (r.val : ZMod 547)) + 25))) = true →
      (449889505361199923860699012491276302348023481466682419684451169239529288665394288623906354784417152630376288485708626671711796314573555015890849339687240189498883839).testBit r.val = true := by decide

theorem even22_b25_s5_map_547 (i : ℕ)
    (h : even22A547 (-(33 * (46 * (80000000 + (i : ZMod 547)) + 25))) = true) :
    (449889505361199923860699012491276302348023481466682419684451169239529288665394288623906354784417152630376288485708626671711796314573555015890849339687240189498883839).testBit (i % 547) = true := by
  let r : Fin 547 := ⟨i % 547, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_547_fin r
  change even22A547
    (-(33 * (46 * (80000000 + ((i % 547 : ℕ) : ZMod 547)) + 25))) = true
  have hcast : (i : ZMod 547) = ((i % 547 : ℕ) : ZMod 547) :=
    (ZMod.natCast_mod i 547).symm
  rw [← hcast]
  exact h


theorem even22_b25_s5_map_557_fin : ∀ r : Fin 557,
    even22A557 (-(33 * (46 * (80000000 + (r.val : ZMod 557)) + 25))) = true →
      (410473696350758157975729431140012813015050859129290202611339418510602643159179644695479365597119710327078604939972144578688911389041635379114356692311566285475640504319).testBit r.val = true := by decide

theorem even22_b25_s5_map_557 (i : ℕ)
    (h : even22A557 (-(33 * (46 * (80000000 + (i : ZMod 557)) + 25))) = true) :
    (410473696350758157975729431140012813015050859129290202611339418510602643159179644695479365597119710327078604939972144578688911389041635379114356692311566285475640504319).testBit (i % 557) = true := by
  let r : Fin 557 := ⟨i % 557, Nat.mod_lt _ (by norm_num)⟩
  apply even22_b25_s5_map_557_fin r
  change even22A557
    (-(33 * (46 * (80000000 + ((i % 557 : ℕ) : ZMod 557)) + 25))) = true
  have hcast : (i : ZMod 557) = ((i % 557 : ℕ) : ZMod 557) :=
    (ZMod.natCast_mod i 557).symm
  rw [← hcast]
  exact h

def even22PackedB25S5Group8Tree : Even22PeriodicTree :=
  (.node (.node (.node (.leaf 499 887061922634673538628588004532632670510944724284487610913828636713121223943521806594408764738888560584360950388166793297930986467599339734790827933693) (.leaf 503 18310525200951872147260080928414462710237982219740399637578917320239803483469249173699395503949574604136093018560209473431031872745235074877318141304799)) (.node (.leaf 509 1545027180633284087969814487207770559840087552561190883573746247556079979109338187009661074880534093874705672475462801795163431571966658282112900647613428) (.leaf 521 3372063694373490458982643185052100453383034293736337510137611708064364563833984456565956531994911450244534405778700999254640762190586586452769388843369459647))) (.node (.node (.leaf 523 25434611233927084839351117616592587968344067061103719210639316773634919776296793627138741967446934586363584384122452110285898419644469903787310054156636225407) (.leaf 541 3598230868875623841975302125654390711272430336043863581034422463074246623239702941002081295225485421826761977418737074620476757030885967769693571618488730713781694)) (.node (.leaf 547 449889505361199923860699012491276302348023481466682419684451169239529288665394288623906354784417152630376288485708626671711796314573555015890849339687240189498883839) (.leaf 557 410473696350758157975729431140012813015050859129290202611339418510602643159179644695479365597119710327078604939972144578688911389041635379114356692311566285475640504319))))

set_option maxRecDepth 10000 in
theorem even22PackedB25S5Group8TreeSupports
    {w v : ℤ} {i : ℕ}
    (hi : i < 2503185)
    (hS : evenTable22S w = 4 * evenTable22S v)
    (hm : -(33 * (46 * (80000000 + (i : ℤ)) + 25)) =
      evenTable22T w - 2 * evenTable22T v) :
    even22PackedB25S5Group8Tree.Supports i 18 := by
  constructor
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_499 i
          have hA := even22_allowed_int even22A499 even22_allowed_499 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_503 i
          have hA := even22_allowed_int even22A503 even22_allowed_503 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_509 i
          have hA := even22_allowed_int even22A509 even22_allowed_509 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_521 i
          have hA := even22_allowed_int even22A521 even22_allowed_521 hS hm
          simpa using hA
  · constructor
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_523 i
          have hA := even22_allowed_int even22A523 even22_allowed_523 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_541 i
          have hA := even22_allowed_int even22A541 even22_allowed_541 hS hm
          simpa using hA
    · constructor
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_547 i
          have hA := even22_allowed_int even22A547 even22_allowed_547 hS hm
          simpa using hA
      · constructor
        · norm_num at hi ⊢
          omega
        · apply even22_b25_s5_map_557 i
          have hA := even22_allowed_int even22A557 even22_allowed_557 hS hm
          simpa using hA
end Erdos686.Erdos686Variant
