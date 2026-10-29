module

public import CakeCuttingPsomas.Allocation
public import CakeCuttingPsomas.RecordedProtocol

set_option linter.style.header false

/-! # Recorded outputs of partial-allocation subroutines

Section 1.3's inherited-record convention for the subroutines of Section 3.
-/

@[expose] public section

namespace CakeCuttingPsomas

/-- Valuation-independent partial allocation, updated records, and exact residue. -/
structure RecordedAllocationResult (n : ℕ) (C : Piece) where
  allocation : Allocation n C
  state : RecordedState n
  residue : Piece
  residue_eq : residue.support = allocation.residue

/-- Section 1.3: earlier pieces remain representable, output bundles have recorded
representations, and the residue can be passed directly to the next subroutine.
Refinement may subdivide old interval lists, so literal compatibility of those
lists is deliberately not required. -/
def RecordedAllocationResult.Inherits {n : ℕ} {C : Piece}
    (r : RecordedAllocationResult n C) (s : RecordedState n) : Prop :=
  s.Refines r.state ∧ (∀ i, r.state.Represents (r.allocation.bundle i).support) ∧
    r.state.Compatible r.residue

end CakeCuttingPsomas
