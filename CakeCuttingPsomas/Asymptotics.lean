module

public import CakeCuttingPsomas.QueryBound
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.header false

/-! # Asymptotic query bound

The `2^{O(n log n)}` corollary of Section 2's main theorem in `paper/main.tex`.
Logarithms are natural logarithms; changing their base only changes the constant.
-/

@[expose] public section

namespace CakeCuttingPsomas

/-- Section 2 (`thm: main theorem`): the logarithm of the explicit query bound
is at most `11 n log n` for at least two agents. -/
theorem log_queryBound_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log (queryBound n : ℝ) ≤ 11 * (n : ℝ) * Real.log (n : ℝ) := by
  have hpos : 0 < queryBound n := by
    unfold queryBound
    positivity
  have hbound : (queryBound n : ℝ) ≤ (n : ℝ) ^ (11 * n) := by
    exact_mod_cast queryBound_le_pow hn
  calc
    Real.log (queryBound n : ℝ) ≤ Real.log ((n : ℝ) ^ (11 * n)) :=
      Real.log_le_log (by exact_mod_cast hpos) hbound
    _ = 11 * (n : ℝ) * Real.log (n : ℝ) := by
      rw [Real.log_pow]
      push_cast
      ring

/-- Section 2 (`thm: main theorem`): `log(queryBound n) = O(n log n)` at infinity,
the logarithmic formulation of the paper's exponential asymptotic bound. -/
theorem log_queryBound_isBigO :
    (fun n : ℕ ↦ Real.log (queryBound n : ℝ))
      =O[Filter.atTop] (fun n ↦ (n : ℝ) * Real.log (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 11
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hq : (1 : ℝ) ≤ queryBound n := by
    have hpos : 0 < queryBound n := by unfold queryBound; positivity
    exact_mod_cast (show 1 ≤ queryBound n by omega)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hq),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hn')),
    mul_assoc] using log_queryBound_le hn

/-- Section 2 (`thm: main theorem`): an explicit base-two upper bound witnessing
`queryBound n ∈ 2^{O(n log n)}`. -/
theorem queryBound_le_two_rpow {n : ℕ} (hn : 2 ≤ n) :
    (queryBound n : ℝ) ≤
      (2 : ℝ) ^ ((11 / Real.log 2) * (n : ℝ) * Real.log (n : ℝ)) := by
  have hpos : 0 < queryBound n := by
    unfold queryBound
    positivity
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have heq : Real.log 2 * ((11 / Real.log 2) * (n : ℝ) * Real.log (n : ℝ)) =
      11 * (n : ℝ) * Real.log (n : ℝ) := by
    field_simp
  rw [heq, ← Real.exp_log (by exact_mod_cast hpos : (0 : ℝ) < queryBound n)]
  exact Real.exp_le_exp.mpr (log_queryBound_le hn)

end CakeCuttingPsomas
