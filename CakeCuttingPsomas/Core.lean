module

public import CakeCuttingPsomas.RecordedAllocation
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

set_option linter.style.header false

/-! # The interface to Core

Section 3's `lem:core main`, with Section 1.3's inherited records.
This specifies a protocol family without asserting its existence.
-/

@[expose] public section

namespace CakeCuttingPsomas

/-- The query bound in `lem:core main`. -/
def coreQueryBound (n : ℕ) : ℕ := n ^ 3 * (Nat.factorial n) ^ 2

/-- A valuation-independent family for Core, including the designated cutter. -/
def CoreProtocol := (n : ℕ) → 2 ≤ n → RecordedState n →
  (C : Piece) → Fin n → RWProtocol n (RecordedAllocationResult n C)

/-- Section 3's `lem:core main`, including inherited records. Empty cakes and
zero-valued cakes are allowed; normalization is not assumed. -/
def CoreProtocol.Correct (K : CoreProtocol) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (s : RecordedState n) (C : Piece) (c : Fin n)
    (v : Fin n → Valuation), s.Correct v → s.Compatible C →
    ∃ (r : RecordedAllocationResult n C) (count : ℕ),
      (K n hn s C c).Runs v r count ∧ r.state.Correct v ∧ r.Inherits s ∧
      r.allocation.EnvyFree v ∧
      (v c).value (r.allocation.bundle c).support = (v c).value C.support / n ∧
      count ≤ coreQueryBound n

/-- Section 3, proof of `lem: dominate` (repeated Core calls): a cutter receiving
exactly a `1/n` share leaves at most `(n-1)/n` of her input value in the residue. -/
theorem RecordedAllocationResult.cutter_residue_le {n : ℕ} {C : Piece}
    (r : RecordedAllocationResult n C) (hn : 2 ≤ n) (v : Fin n → Valuation)
    (c : Fin n)
    (hshare : (v c).value (r.allocation.bundle c).support =
      (v c).value C.support / n) :
    (v c).value r.residue.support ≤ ((n : ℝ) - 1) / n * (v c).value C.support := by
  have hsum := (v c).value_union (r.allocation.bundle c).measurableSet_support
    r.allocation.measurableSet_residue (r.allocation.bundle c).support_subset_unit
    r.allocation.residue_subset_unit (r.allocation.disjoint_bundle_residue c)
  have hle := (v c).value_mono
    ((r.allocation.bundle c).measurableSet_support.union r.allocation.measurableSet_residue)
    C.measurableSet_support
    (Set.union_subset (r.allocation.contained c) r.allocation.residue_subset)
    C.support_subset_unit
  rw [hsum, hshare] at hle
  rw [r.residue_eq]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hid : ((n : ℝ) - 1) / n * (v c).value C.support =
      (v c).value C.support - (v c).value C.support / n := by
    field_simp
  rw [hid]
  linarith

end CakeCuttingPsomas
