import Research.Basic

/-!
# Faithful formalization of Erdős Problem 321

`Research.Basic` is now the single canonical source of the exact definitions
used by both the verifier and the final proof.  It defines exact rational
reciprocal subset sums, validity over the full powerset, admissibility in
`{1,…,N}`, and the attained finite maximum `Erdos321.extremalSize`.
-/

#check Erdos321.reciprocalSubsetSum
#check Erdos321.Valid
#check Erdos321.Admissible
#check Erdos321.extremalSize
#check Erdos321.card_le_extremalSize
#check Erdos321.exists_extremizer
