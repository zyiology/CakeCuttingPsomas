module

public import CakeCuttingPsomas.Core

set_option linter.style.header false

/-! # The interface to Repair

Section 3's `lem:repair main`, with the bundle permutation oriented as in the
proof of `lem: dominate`: `permutation j` receives old bundle `j` plus its addition.
-/

@[expose] public section

namespace CakeCuttingPsomas

/-- Repair's valuation-independent output. Each old bundle stays intact, with a
disjoint addition from its residue, and the resulting bundles are permuted. -/
structure RepairResult (n : ℕ) (C : Piece) (D : Allocation n C)
    extends RecordedAllocationResult n C where
  permutation : Equiv.Perm (Fin n)
  addition : Fin n → Piece
  addition_subset : ∀ j, (addition j).support ⊆ D.residue
  addition_disjoint : ∀ j k, j ≠ k → Disjoint (addition j).support (addition k).support
  bundle_eq : ∀ j, (allocation.bundle (permutation j)).support =
    (D.bundle j).support ∪ (addition j).support

/-- A valuation-independent family for Repair. Its guarantees apply only under
the epsilon, positive-residue, and almost-envy-free hypotheses below. -/
def RepairProtocol := (n : ℕ) → 2 ≤ n → RecordedState n →
  (C : Piece) → (D : Allocation n C) → ℝ → RWProtocol n (RepairResult n C D)

/-- Section 3's `lem:repair main` with inherited records. The query inequality is
over the reals, preserving the paper's `n/ε` bound without rounding it upward. -/
def RepairProtocol.Correct (P : RepairProtocol) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (s : RecordedState n) (C : Piece)
    (D : Allocation n C) (ε : ℝ) (v : Fin n → Valuation),
    s.Correct v → s.Compatible C →
    (∀ j, s.Represents (D.bundle j).support) →
    0 < ε → ε ≤ 1 / (6 * (n : ℝ) ^ 3) →
    (∀ i, 0 < (v i).value D.residue) →
    (∀ i j, (v i).value (D.bundle j).support - ε * (v i).value D.residue ≤
      (v i).value (D.bundle i).support) →
    ∃ (r : RepairResult n C D) (count : ℕ),
      (P n hn s C D ε).Runs v r count ∧ r.state.Correct v ∧
      r.toRecordedAllocationResult.Inherits s ∧ r.allocation.EnvyFree v ∧
      (∀ i j, (v i).value (r.addition j).support ≤
        3 * (n : ℝ) ^ 2 * ε * (v i).value D.residue) ∧
      (count : ℝ) ≤ (n : ℝ) / ε + coreQueryBound n

/-- Section 3, proof of `lem: dominate`: Repair preserves every old bundle under
the returned permutation. -/
theorem RepairResult.old_bundle_subset {n : ℕ} {C : Piece} {D : Allocation n C}
    (r : RepairResult n C D) (j : Fin n) :
    (D.bundle j).support ⊆ (r.allocation.bundle (r.permutation j)).support := by
  rw [r.bundle_eq]
  exact Set.subset_union_left

/-- Section 3, proof of `lem: dominate`, the post-Repair advantage calculation:
the value of a reassigned bundle is its old value plus its addition's value. -/
theorem RepairResult.value_bundle {n : ℕ} {C : Piece} {D : Allocation n C}
    (r : RepairResult n C D) (v : Valuation) (j : Fin n) :
    v.value (r.allocation.bundle (r.permutation j)).support =
      v.value (D.bundle j).support + v.value (r.addition j).support := by
  rw [r.bundle_eq]
  exact v.value_union (D.bundle j).measurableSet_support (r.addition j).measurableSet_support
    (D.bundle j).support_subset_unit (r.addition j).support_subset_unit
    ((D.disjoint_bundle_residue j).mono_right (r.addition_subset j))

/-- Section 3's `lem:repair main`: the output residue is exactly the old residue
minus the additions. This follows from the bundle identities and permutation. -/
theorem RepairResult.residue_removed {n : ℕ} {C : Piece} {D : Allocation n C}
    (r : RepairResult n C D) :
    r.residue.support = D.residue \ ⋃ j, (r.addition j).support := by
  have ha : r.allocation.allocated = D.allocated ∪ ⋃ j, (r.addition j).support := by
    ext x
    simp only [Allocation.allocated, Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨j, rfl⟩ := r.permutation.surjective k
      rw [r.bundle_eq] at hk
      exact hk.elim (fun h ↦ Or.inl ⟨j, h⟩) (fun h ↦ Or.inr ⟨j, h⟩)
    · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
      · exact ⟨r.permutation j, (r.bundle_eq j).symm ▸ Or.inl hj⟩
      · exact ⟨r.permutation j, (r.bundle_eq j).symm ▸ Or.inr hj⟩
  rw [r.residue_eq, Allocation.residue, ha, Allocation.residue]
  ext x
  simp only [Set.mem_sdiff, Set.mem_union, not_or]
  exact and_assoc.symm

end CakeCuttingPsomas
