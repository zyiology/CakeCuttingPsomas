module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! # Query accounting for Section 2

The cost of `Dominate` and the sum over strictly decreasing recursive agent
counts in the proof of `thm: main theorem` in `paper/main.tex`.
-/

@[expose] public section

namespace CakeCuttingPsomas

/-- The bound in Section 2's `lem: dominate`. -/
def dominateQueryBound (n : ℕ) : ℕ := 32 ^ n * n ^ 7 * (Nat.factorial n) ^ 2

/-- The explicit query bound in Section 2's `thm: main theorem`. -/
def queryBound (n : ℕ) : ℕ := 2 * 32 ^ n * n ^ 7 * (Nat.factorial n) ^ 2

/-- Section 2's accounting: at most two terminal queries plus one `Dominate`
call at each size from 3 through `n`. Zero or one agent requires no queries. -/
def divideQueryCost (n : ℕ) : ℕ :=
  if n < 2 then 0 else 2 + ∑ m ∈ Finset.Icc 3 n, dominateQueryBound m

@[simp]
theorem divideQueryCost_zero : divideQueryCost 0 = 0 := by simp [divideQueryCost]

@[simp]
theorem divideQueryCost_one : divideQueryCost 1 = 0 := by simp [divideQueryCost]

@[simp]
theorem divideQueryCost_two : divideQueryCost 2 = 2 := by norm_num [divideQueryCost]

theorem divideQueryCost_mono : Monotone divideQueryCost := by
  intro m n hmn
  by_cases hm : m < 2
  · simp [divideQueryCost, hm]
  · have hn : ¬n < 2 := by omega
    simp only [divideQueryCost, ite_eq_right hm, ite_eq_right hn]
    apply Nat.add_le_add_left
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl hmn) (fun _ _ _ ↦ Nat.zero_le _)

theorem divideQueryCost_succ {n : ℕ} (hn : 2 ≤ n) :
    divideQueryCost (n + 1) = divideQueryCost n + dominateQueryBound (n + 1) := by
  simp only [divideQueryCost, ite_eq_right (show ¬n + 1 < 2 by omega),
    ite_eq_right (show ¬n < 2 by omega), Finset.sum_Icc_succ_top (by omega : 3 ≤ n + 1)]
  omega

/-- Section 2 (`thm: main theorem`): the cost of one domination call and a
recursive call on a proper group fits the sum over all remaining sizes. -/
theorem divideQueryCost_step {m n : ℕ} (hn : 3 ≤ n) (hm : m < n) :
    dominateQueryBound n + divideQueryCost m ≤ divideQueryCost n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change dominateQueryBound (k + 1) + divideQueryCost m ≤ divideQueryCost (k + 1)
  rw [divideQueryCost_succ (by omega : 2 ≤ k)]
  have := divideQueryCost_mono (show m ≤ k by omega)
  omega

private theorem dominateQueryBound_growth (n : ℕ) :
    32 * dominateQueryBound n ≤ dominateQueryBound (n + 1) := by
  have hp : n ^ 7 * (Nat.factorial n) ^ 2 ≤
      (n + 1) ^ 7 * (Nat.factorial (n + 1)) ^ 2 :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_succ n) 7)
      (Nat.pow_le_pow_left (Nat.factorial_le (Nat.le_succ n)) 2)
  calc
    32 * dominateQueryBound n = 32 ^ (n + 1) * (n ^ 7 * (Nat.factorial n) ^ 2) := by
      simp only [dominateQueryBound, pow_succ]
      ring
    _ ≤ 32 ^ (n + 1) * ((n + 1) ^ 7 * (Nat.factorial (n + 1)) ^ 2) :=
      Nat.mul_le_mul_left _ hp
    _ = dominateQueryBound (n + 1) := by simp only [dominateQueryBound]; ring

/-- Section 2's explicit bound (`thm: main theorem`). The cumulative cost is
bounded by twice the largest domination cost, using its geometric growth. -/
theorem divideQueryCost_le_queryBound (n : ℕ) : divideQueryCost n ≤ queryBound n := by
  have h (n : ℕ) : divideQueryCost n ≤ 2 * dominateQueryBound n := by
    induction n with
    | zero => simp
    | succ n ih =>
      by_cases hn : n < 2
      · interval_cases n <;> norm_num [dominateQueryBound, divideQueryCost]
      · rw [divideQueryCost_succ (by omega)]
        have hg := dominateQueryBound_growth n
        omega
  calc
    divideQueryCost n ≤ 2 * dominateQueryBound n := h n
    _ = queryBound n := by simp only [dominateQueryBound, queryBound]; ring

/-- Section 2's main theorem (`thm: main theorem`): an elementary upper bound
on the explicit query count, used to derive `2^{O(n log n)}`. -/
theorem queryBound_le_pow {n : ℕ} (hn : 2 ≤ n) :
    queryBound n ≤ n ^ (11 * n) := by
  have h32 : 32 ≤ n ^ 5 := by
    calc
      32 = 2 ^ 5 := by norm_num
      _ ≤ n ^ 5 := Nat.pow_le_pow_left hn 5
  calc
    queryBound n ≤ n * (n ^ 5) ^ n * n ^ 7 * (n ^ n) ^ 2 := by
      unfold queryBound
      gcongr
      exact Nat.factorial_le_pow n
    _ = n ^ (7 * n + 8) := by ring
    _ ≤ n ^ (11 * n) := Nat.pow_le_pow_right (by omega) (by omega)

end CakeCuttingPsomas
