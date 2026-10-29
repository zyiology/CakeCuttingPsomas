module

public import CakeCuttingPsomas.Allocation
public import CakeCuttingPsomas.RecordedProtocol
public import CakeCuttingPsomas.QueryBound
public import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-! # The interface to Dominate

Section 2's `lem: dominate` and Section 1.3's inherited-record convention.
This module specifies the subroutine; it does not assume or implement it.
-/

@[expose] public section

namespace CakeCuttingPsomas

/-- Valuation-independent output data for Section 2's `Dominate`.
The residue has exact support; correctness of values and domination are separate
execution guarantees. The group can be checked before recursing even on query
answers that do not correspond to legal executions. -/
structure DominateResult (n : ℕ) (C : Piece) where
  allocation : Allocation n C
  group : Finset (Fin n)
  state : RecordedState n
  residue : Piece
  residue_eq : residue.support = allocation.residue

namespace DominateResult

/-- Relabel a recursive group by consecutive agent indices (Section 1.3). -/
noncomputable def agents {n : ℕ} {C : Piece} (r : DominateResult n C) :
    Fin r.group.card ≃ (↑r.group : Set (Fin n)) := r.group.equivFin.symm

/-- The participating agents viewed in the original profile. -/
noncomputable def inclusion {n : ℕ} {C : Piece} (r : DominateResult n C) :
    Fin r.group.card → Fin n := fun i ↦ (r.agents i).val

/-- Section 2's dominated group is nonempty and has strictly fewer agents,
which is the well-founded measure for the recursive `Divide` call. -/
theorem group_size {n : ℕ} {C : Piece} (r : DominateResult n C)
    (v : Fin n → Valuation) (h : r.allocation.DominatedGroup v (↑r.group)) :
    0 < r.group.card ∧ r.group.card < n := by
  classical
  constructor
  · exact Finset.card_pos.mpr h.1
  · have hne : r.group ≠ Finset.univ := by
      intro heq
      apply h.2.1
      simp [heq]
    have hlt := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩)
    simpa using hlt

end DominateResult

/-- A family of query protocols, chosen independently of valuations, for all
instances where Section 2 calls `Dominate`. -/
def DominateProtocol := (n : ℕ) → 3 ≤ n → RecordedState n →
  (C : Piece) → RWProtocol n (DominateResult n C)

/-- Section 2's `lem: dominate`, with the inherited records required by
Section 1.3: the output records are correct and the exact residue is compatible.
No normalization, positive-value, or nonempty-cake assumption is made.
This is an explicit hypothesis for the reduction, not an axiom asserting existence. -/
def DominateProtocol.Correct (D : DominateProtocol) : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (s : RecordedState n) (C : Piece) (v : Fin n → Valuation),
    s.Correct v → s.Compatible C →
    ∃ (r : DominateResult n C) (count : ℕ),
      (D n hn s C).Runs v r count ∧ r.state.Correct v ∧ r.state.Compatible r.residue ∧
      r.allocation.EnvyFree v ∧ r.allocation.DominatedGroup v (↑r.group) ∧
      count ≤ dominateQueryBound n

end CakeCuttingPsomas
