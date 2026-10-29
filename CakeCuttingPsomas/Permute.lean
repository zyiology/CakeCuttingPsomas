module

public import CakeCuttingPsomas.RecordedAllocation
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic

set_option linter.style.header false

/-! # The interface to Permute

Section 4's `lem:permute`, with Section 1.3's inherited records. This contract
does not assert the existence of an implementation of Section 5's protocol.
-/

@[expose] public section

namespace CakeCuttingPsomas

/-- Section 5's number of prefix cuts, converted using Section 1.3's cost. -/
def permuteQueryBound (n : ℕ) : ℕ := (n + 1) * (n.choose 2 * (Nat.factorial n) ^ 2)

/-- Permute keeps the input labels, including labels of empty pieces. -/
structure PermuteResult (n : ℕ) (C : Piece) extends RecordedAllocationResult n C where
  assignment : Equiv.Perm (Fin n)

/-- A uniform family, independent of valuations. The input pieces partition C;
their geometric and recorded preconditions occur only in the correctness contract. -/
def PermuteProtocol := (n : ℕ) → 0 < n → RecordedState n →
  (C : Piece) → (Fin n → Piece) → RWProtocol n (PermuteResult n C)

/-- Section 4's `lem:permute`, including both additional guarantees (i) and (ii).
Support equality accommodates subdivision of interval lists by inherited records.
Empty pieces, zero values, and unnormalized valuations are allowed. -/
def PermuteProtocol.Correct (P : PermuteProtocol) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (s : RecordedState n) (C : Piece) (pieces : Fin n → Piece)
    (v : Fin n → Valuation), s.Correct v →
    (∀ j, s.Represents (pieces j).support) →
    (∀ i j, i ≠ j → Disjoint (pieces i).support (pieces j).support) →
    (⋃ j, (pieces j).support) = C.support →
    ∃ (r : PermuteResult n C) (count : ℕ),
      (P n hn s C pieces).Runs v r count ∧ r.state.Correct v ∧
      r.toRecordedAllocationResult.Inherits s ∧ r.allocation.EnvyFree v ∧
      (∀ i, (r.allocation.bundle i).IsSuffix (pieces (r.assignment i))) ∧
      (∃ i, (r.allocation.bundle i).support = (pieces (r.assignment i)).support) ∧
      (∀ S : Finset (Fin n), S.Nonempty →
        (∀ i ∈ S, (r.allocation.bundle i).support ≠ (pieces (r.assignment i)).support) →
        ∃ i ∈ S, ∃ j ∉ S,
          (v j).value (r.allocation.bundle i).support =
            (v j).value (r.allocation.bundle j).support) ∧
      count ≤ permuteQueryBound n

end CakeCuttingPsomas
