module

public import CakeCuttingPsomas.DominateShrinking
public import CakeCuttingPsomas.QueryBound
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.style.header false

/-! # Query accounting for Section 3's Dominate

The final returning iteration calls Core once. Each of at most `n²`
continuations additionally calls Repair and the bounded shrinking loop.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.DominateCost

/-- Section 3's uniform ceiling bound on shrinking Core calls. -/
def shrinkBudget (n : ℕ) : ℕ :=
  ⌈(n : ℝ) * (n + 1) * Real.log (4 * (n : ℝ) ^ 2)⌉₊

/-- Section 3's Repair bound at the smallest allowed geometric scale. -/
def repairBudget (n : ℕ) : ℕ := n * (4 * n ^ 2) ^ (n + 1) + coreQueryBound n

/-- One non-returning iteration: initial Core, Repair, and shrinking. -/
def continuationBudget (n : ℕ) : ℕ :=
  coreQueryBound n + repairBudget n + shrinkBudget n * coreQueryBound n

/-- Section 3's full cost, including the final returning Core call. -/
def totalBudget (n : ℕ) : ℕ := n ^ 2 * continuationBudget n + coreQueryBound n

theorem scale_price_le {n t : ℕ} (hn : 3 ≤ n) (ht : t ≤ n + 1) :
    (n : ℝ) / DominateChoice.scale n t ≤ (n * (4 * n ^ 2) ^ (n + 1) : ℕ) := by
  have hB : (1 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  simp only [DominateChoice.scale, div_eq_mul_inv, ← inv_pow, inv_inv,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB ht) (Nat.cast_nonneg n)

/-- Section 3, proof of `lem: dominate`: the real-valued Repair bound implies
the uniform natural query budget without introducing a rounding cost. -/
theorem repair_count_le {n t count : ℕ} (hn : 3 ≤ n) (ht : t ≤ n + 1)
    (hc : (count : ℝ) ≤ (n : ℝ) / DominateChoice.scale n t + coreQueryBound n) :
    count ≤ repairBudget n := by
  have h := hc.trans (add_le_add (scale_price_le hn ht) (le_refl (coreQueryBound n : ℝ)))
  exact_mod_cast h

/-- A convenient polynomial upper bound for the ceiling in the paper's
shrinking-call count. Keeping the ceiling earlier avoids any per-call rounding. -/
theorem shrinkBudget_le {n : ℕ} (hn : 3 ≤ n) : shrinkBudget n ≤ 6 * n ^ 4 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := Real.log_le_self (show 0 ≤ 4 * (n : ℝ) ^ 2 by positivity)
  apply Nat.ceil_le.mpr
  push_cast
  calc
    (n : ℝ) * (n + 1) * Real.log (4 * (n : ℝ) ^ 2) ≤
        n * (n + 1) * (4 * n ^ 2) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ ≤ 6 * n ^ 4 := by
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) ^ 3 by positivity)
        (show 0 ≤ 2 * (n : ℝ) - 4 by linarith)]

/-- The factorial lower bound used in Section 3's last query inequality.
Stirling supplies `(n/e)^n ≤ n!`, and `e² < 8` absorbs the exponential factor. -/
theorem power_le_factorial {n : ℕ} (hn : 3 ≤ n) :
    ((n : ℝ) ^ n) ^ 2 ≤ (8 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    have := Real.two_le_pi
    nlinarith
  have hst := Stirling.le_factorial_stirling n
  have hsmall : ((n : ℝ) / Real.exp 1) ^ n ≤ (Nat.factorial n : ℝ) :=
    (le_mul_of_one_le_left (by positivity) hsqrt).trans hst
  rw [div_pow, div_le_iff₀ (by positivity)] at hsmall
  have he : (Real.exp 1) ^ 2 ≤ (8 : ℝ) := by
    have h := Real.exp_one_lt_d9
    have := Real.exp_pos (1 : ℝ)
    nlinarith
  calc
    ((n : ℝ) ^ n) ^ 2 ≤ ((Nat.factorial n : ℝ) * Real.exp 1 ^ n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsmall 2
    _ = (Real.exp 1 ^ 2) ^ n * (Nat.factorial n : ℝ) ^ 2 := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      ring
    _ ≤ (8 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2 := by gcongr

private theorem polynomial_le_exp {n : ℕ} (hn : 3 ≤ n) : 14 * n ^ 2 ≤ 32 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ (32 : ℕ) n]
    have hn' : 3 ≤ n := hn
    nlinarith

/-- Section 3, proof of `lem: dominate`, final query inequality: the full
call-count budget fits `32^n n^7 (n!)²`. The polynomial estimate on the logarithm
is deliberately loose; the paper's explicit final bound is unchanged. -/
theorem totalBudget_le {n : ℕ} (hn : 3 ≤ n) : totalBudget n ≤ dominateQueryBound n := by
  have hb := shrinkBudget_le hn
  have hp := power_le_factorial hn
  have he := polynomial_le_exp hn
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hb' : (shrinkBudget n : ℝ) ≤ 6 * (n : ℝ) ^ 4 := by exact_mod_cast hb
  have he' : 14 * (n : ℝ) ^ 2 ≤ (32 : ℝ) ^ n := by exact_mod_cast he
  have hfirst : (n : ℝ) ^ 3 * (4 * (n : ℝ) ^ 2) ^ (n + 1) ≤
      4 * (32 : ℝ) ^ n * (n : ℝ) ^ 5 * (Nat.factorial n : ℝ) ^ 2 := by
    calc
      (n : ℝ) ^ 3 * (4 * (n : ℝ) ^ 2) ^ (n + 1) =
          (4 * (4 : ℝ) ^ n * (n : ℝ) ^ 5) * ((n : ℝ) ^ n) ^ 2 := by
        rw [pow_succ, mul_pow, ← pow_mul, ← pow_mul]
        ring
      _ ≤ (4 * (4 : ℝ) ^ n * (n : ℝ) ^ 5) *
          ((8 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) := by gcongr
      _ = 4 * (32 : ℝ) ^ n * (n : ℝ) ^ 5 * (Nat.factorial n : ℝ) ^ 2 := by
        rw [show (32 : ℝ) = 4 * 8 by norm_num, mul_pow]
        ring
  have htail : ((n : ℝ) ^ 2 * (2 + shrinkBudget n) + 1) *
      ((n : ℝ) ^ 3 * (Nat.factorial n : ℝ) ^ 2) ≤
      7 * (n : ℝ) ^ 9 * (Nat.factorial n : ℝ) ^ 2 := by
    have hpoly : (n : ℝ) ^ 2 * (2 + shrinkBudget n) + 1 ≤ 7 * (n : ℝ) ^ 6 := by
      have hpow : 2 * (n : ℝ) ^ 2 + 1 ≤ (n : ℝ) ^ 6 := by
        nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 1),
          mul_nonneg (show 0 ≤ (n : ℝ) ^ 2 - 3 by nlinarith)
            (show 0 ≤ (n : ℝ) ^ 4 by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hb' (sq_nonneg (n : ℝ))]
    calc
      _ ≤ (7 * (n : ℝ) ^ 6) * ((n : ℝ) ^ 3 * (Nat.factorial n : ℝ) ^ 2) := by gcongr
      _ = _ := by ring
  have hhalf1 : 4 * (32 : ℝ) ^ n * (n : ℝ) ^ 5 * (Nat.factorial n : ℝ) ^ 2 ≤
      (32 : ℝ) ^ n * (n : ℝ) ^ 7 * (Nat.factorial n : ℝ) ^ 2 / 2 := by
    have hpoly : 8 * (n : ℝ) ^ 5 ≤ (n : ℝ) ^ 7 := by
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) ^ 2 - 8 by nlinarith)
        (show 0 ≤ (n : ℝ) ^ 5 by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hpoly
      (show 0 ≤ (32 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2 by positivity)]
  have hhalf2 : 7 * (n : ℝ) ^ 9 * (Nat.factorial n : ℝ) ^ 2 ≤
      (32 : ℝ) ^ n * (n : ℝ) ^ 7 * (Nat.factorial n : ℝ) ^ 2 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right he'
      (show 0 ≤ (n : ℝ) ^ 7 * (Nat.factorial n : ℝ) ^ 2 by positivity)]
  have htotal : (totalBudget n : ℝ) =
      (n : ℝ) ^ 3 * (4 * (n : ℝ) ^ 2) ^ (n + 1) +
        ((n : ℝ) ^ 2 * (2 + shrinkBudget n) + 1) *
          ((n : ℝ) ^ 3 * (Nat.factorial n : ℝ) ^ 2) := by
    simp only [totalBudget, continuationBudget, repairBudget, coreQueryBound]
    push_cast
    ring
  have hbound : (totalBudget n : ℝ) ≤ (dominateQueryBound n : ℝ) := by
    rw [htotal]
    simp only [dominateQueryBound, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  exact_mod_cast hbound

end CakeCuttingPsomas.DominateCost
