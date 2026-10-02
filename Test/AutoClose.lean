import Mathlib

open scoped Nat

namespace AutoClose

-- Q1: does `rw` close a goal that becomes `n ≤ n` after rewriting?
theorem rw_closes_le (n : ℕ) : n + 0 ≤ n := by
  rw [Nat.add_zero]

end AutoClose
