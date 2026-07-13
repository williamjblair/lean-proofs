import «compute».campaign686.agent_k22_packed_kernel.PackedPeriodicCover

namespace Erdos686.K22PackedKernelReview

/-- The exact low-bit-first mask obtained by the independent `p = 23`
enumeration.  Its true bits are `2`, `6`, `17`, and `21`. -/
def auditedP23Mask : ℕ := 2228292

/-- Kernel-checked decoding of every bit of the audited `p = 23` mask. -/
theorem auditedP23Mask_testBit_iff (r : ℕ) (hr : r < 23) :
    auditedP23Mask.testBit r = true ↔
      r = 2 ∨ r = 6 ∨ r = 17 ∨ r = 21 := by
  interval_cases r <;> decide +kernel

/-- Combining odd parity with the exact `p = 23` mask produces precisely the
four odd residue classes modulo `46`. -/
theorem parity_p23Mask_branch_disjunction (t : ℕ) (hodd : t % 2 = 1)
    (hmask : auditedP23Mask.testBit (t % 23) = true) :
    (∃ q : ℕ, t = 46 * q + 17) ∨
    (∃ q : ℕ, t = 46 * q + 21) ∨
    (∃ q : ℕ, t = 46 * q + 25) ∨
    (∃ q : ℕ, t = 46 * q + 29) := by
  have h23 :
      t % 23 = 2 ∨ t % 23 = 6 ∨ t % 23 = 17 ∨ t % 23 = 21 :=
    (auditedP23Mask_testBit_iff (t % 23)
      (Nat.mod_lt _ (by norm_num))).mp hmask
  rcases h23 with h2 | h6 | h17 | h21
  · right
    right
    left
    refine ⟨t / 46, ?_⟩
    have h46 : t % 46 = 25 := by omega
    omega
  · right
    right
    right
    refine ⟨t / 46, ?_⟩
    have h46 : t % 46 = 29 := by omega
    omega
  · left
    refine ⟨t / 46, ?_⟩
    have h46 : t % 46 = 17 := by omega
    omega
  · right
    left
    refine ⟨t / 46, ?_⟩
    have h46 : t % 46 = 21 := by omega
    omega

/-- The exact four branch representatives used by the packed sieve. -/
def p23BranchResidues : Finset ℕ := {17, 21, 25, 29}

/-- Set-valued form of the branch decomposition requested by the sieve:
`t = 46*q+a` for one of the four exact representatives. -/
theorem parity_p23Mask_branch_decomposition (t : ℕ) (hodd : t % 2 = 1)
    (hmask : auditedP23Mask.testBit (t % 23) = true) :
    ∃ q a : ℕ, a ∈ p23BranchResidues ∧ t = 46 * q + a := by
  rcases parity_p23Mask_branch_disjunction t hodd hmask with
      ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
  · exact ⟨q, 17, by simp [p23BranchResidues], hq⟩
  · exact ⟨q, 21, by simp [p23BranchResidues], hq⟩
  · exact ⟨q, 25, by simp [p23BranchResidues], hq⟩
  · exact ⟨q, 29, by simp [p23BranchResidues], hq⟩

/-- The same decomposition with the `Odd t` hypothesis exported by the k=22
Runge reduction. -/
theorem odd_p23Mask_branch_decomposition (t : ℕ) (hodd : Odd t)
    (hmask : auditedP23Mask.testBit (t % 23) = true) :
    ∃ q a : ℕ, a ∈ p23BranchResidues ∧ t = 46 * q + a := by
  rw [Nat.odd_iff] at hodd
  exact parity_p23Mask_branch_decomposition t hodd hmask

/-- Exactness of the decomposition: the four progressions are neither missing
nor adding any parity-plus-mask cases. -/
theorem parity_p23Mask_branch_iff (t : ℕ) :
    (t % 2 = 1 ∧ auditedP23Mask.testBit (t % 23) = true) ↔
      ∃ q a : ℕ, a ∈ p23BranchResidues ∧ t = 46 * q + a := by
  constructor
  · rintro ⟨hodd, hmask⟩
    exact parity_p23Mask_branch_decomposition t hodd hmask
  · rintro ⟨q, a, ha, rfl⟩
    simp only [p23BranchResidues, Finset.mem_insert,
      Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    all_goals
      constructor
      · omega
      · norm_num [auditedP23Mask, Nat.add_mod, Nat.mul_mod]
        decide +kernel

/-- The early-zero branch is semantically absorbing; it cannot create a
spurious surviving bit by skipping the remaining masks. -/
@[simp] theorem intersectPeriodicItems_zero
    (w e : ℕ) (items : List (ℕ × ℕ)) :
    Erdos686.K22PackedKernel.intersectPeriodicItems w e
        (BitVec.zero w) items = BitVec.zero w := by
  cases items <;> simp [Erdos686.K22PackedKernel.intersectPeriodicItems]

#print axioms auditedP23Mask_testBit_iff
#print axioms parity_p23Mask_branch_disjunction
#print axioms parity_p23Mask_branch_decomposition
#print axioms odd_p23Mask_branch_decomposition
#print axioms parity_p23Mask_branch_iff
#print axioms intersectPeriodicItems_zero
#print axioms Erdos686.K22PackedKernel.periodicPowMask_getLsbD_true
#print axioms Erdos686.K22PackedKernel.intersectPeriodicItems_getLsbD_true
#print axioms Erdos686.K22PackedKernel.no_index_of_intersection_zero

end Erdos686.K22PackedKernelReview
