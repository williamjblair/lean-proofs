import ChallengeDeps
import Submission

open OeisA303656

theorem conjecture (n : ℕ) (hn : 1 < n) : A n := by
  exact Submission.conjecture n hn
