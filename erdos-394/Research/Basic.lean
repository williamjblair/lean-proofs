import Research.FirstQuestion
import Research.DenseHierarchyLittleO

/-!
# Erdős Problem 394: faithful formal targets

The definitions and two propositions imported from `Research.Defs` formalize
`problem.md`.  A full resolution must prove each proposition (an affirmative
answer) or its negation (a negative answer), without proof escape hatches.
The line-by-line fidelity audit is in `check_answer/README.md`.
-/

namespace Research

/-- The first assertion of Erdős Problem 394. -/
theorem erdos394_first_target : FirstQuestion :=
  erdos394_first_question_proved

/-- The second assertion of Erdős Problem 394. -/
theorem erdos394_second_target : SecondQuestion :=
  erdos394_second_target_proved

end Research
