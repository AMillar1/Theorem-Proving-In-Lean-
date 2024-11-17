import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

theorem sum_first_natural_numbers (n : ℕ) : ∑ i in Finset.range (n + 1), i = n * (n + 1) / 2 :=
by
