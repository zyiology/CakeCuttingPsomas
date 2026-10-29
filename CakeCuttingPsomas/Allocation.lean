module

public import CakeCuttingPsomas.Valuation
public import CakeCuttingPsomas.Piece

-- This project does not prescribe mathlib's copyright/license header format.
set_option linter.style.header false

/-! # Combining allocations with allocations from their residue

The composition operation and domination definition are from Section 2
(Reduction to Domination) of `paper/main.tex`.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas.Allocation

variable {n : ℕ} {C : Piece}

theorem disjoint_bundle_of_allocated_subset_residue (X Y : Allocation n C)
    (hY : Y.allocated ⊆ X.residue) (i j : Fin n) :
    Disjoint (X.bundle i).support (Y.bundle j).support :=
  (X.disjoint_bundle_residue i).mono_right ((Y.bundle_subset_allocated j).trans hY)

/-- Give each agent her old bundle followed by her new intervals from the residue.
This is `X ⊕ Y` from Section 2 of the paper. -/
def combine (X Y : Allocation n C) (hY : Y.allocated ⊆ X.residue) : Allocation n C where
  bundle i := (X.bundle i).append (Y.bundle i)
    (disjoint_bundle_of_allocated_subset_residue X Y hY i i)
  contained i := by
    simp only [Piece.support_append]
    exact Set.union_subset (X.contained i) (Y.contained i)
  disjoint i j hij := by
    simp only [Piece.support_append]
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Set.disjoint_left.mp (X.disjoint i j hij) hx hy
    · exact Set.disjoint_left.mp
        (disjoint_bundle_of_allocated_subset_residue X Y hY i j) hx hy
    · exact Set.disjoint_left.mp
        (disjoint_bundle_of_allocated_subset_residue X Y hY j i) hy hx
    · exact Set.disjoint_left.mp (Y.disjoint i j hij) hx hy

@[simp]
theorem support_bundle_combine (X Y : Allocation n C) (hY : Y.allocated ⊆ X.residue)
    (i : Fin n) :
    ((X.combine Y hY).bundle i).support = (X.bundle i).support ∪ (Y.bundle i).support :=
  Piece.support_append _ _ (disjoint_bundle_of_allocated_subset_residue X Y hY i i)

theorem allocated_combine (X Y : Allocation n C) (hY : Y.allocated ⊆ X.residue) :
    (X.combine Y hY).allocated = X.allocated ∪ Y.allocated := by
  ext x
  simp only [allocated, Set.mem_iUnion, support_bundle_combine, Set.mem_union]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨i, hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr hi⟩

/-- Filling exactly the residue makes the combined allocation complete, as in
Section 2's proof of the main theorem (`thm: main theorem`) in the paper. -/
theorem complete_combine (X Y : Allocation n C) (hY : Y.allocated ⊆ X.residue)
    (hfill : Y.allocated = X.residue) : (X.combine Y hY).Complete := by
  rw [Complete, allocated_combine, hfill]
  ext x
  constructor
  · exact fun hx ↦ hx.elim (fun ha ↦ X.allocated_subset ha) (fun hr ↦ hr.1)
  · intro hx
    by_cases ha : x ∈ X.allocated
    · exact Or.inl ha
    · exact Or.inr ⟨hx, ha⟩

theorem residue_combine (X Y : Allocation n C) (hY : Y.allocated ⊆ X.residue) :
    (X.combine Y hY).residue = X.residue \ Y.allocated := by
  rw [residue, allocated_combine]
  ext x
  constructor
  · rintro ⟨hx, hxy⟩
    exact ⟨⟨hx, fun h ↦ hxy (Or.inl h)⟩, fun h ↦ hxy (Or.inr h)⟩
  · rintro ⟨⟨hx, hX⟩, hY⟩
    exact ⟨hx, fun h ↦ h.elim hX hY⟩

theorem bundle_union_residue_combine_subset (X Y : Allocation n C)
    (hY : Y.allocated ⊆ X.residue) (i : Fin n) :
    (Y.bundle i).support ∪ (X.combine Y hY).residue ⊆ X.residue := by
  rw [residue_combine]
  exact Set.union_subset ((Y.bundle_subset_allocated i).trans hY) Set.sdiff_subset

theorem disjoint_bundle_residue_combine (X Y : Allocation n C)
    (hY : Y.allocated ⊆ X.residue) (i : Fin n) :
    Disjoint (Y.bundle i).support (X.combine Y hY).residue := by
  rw [residue_combine]
  exact Set.disjoint_left.mpr fun _ hx hr ↦ hr.2 (Y.bundle_subset_allocated i hx)

theorem value_bundle_combine (X Y : Allocation n C) (hY : Y.allocated ⊆ X.residue)
    (v : Valuation) (i : Fin n) :
    v.value ((X.combine Y hY).bundle i).support =
      v.value (X.bundle i).support + v.value (Y.bundle i).support := by
  rw [support_bundle_combine]
  exact v.value_union (X.bundle i).measurableSet_support (Y.bundle i).measurableSet_support
    (X.bundle i).support_subset_unit (Y.bundle i).support_subset_unit
    (disjoint_bundle_of_allocated_subset_residue X Y hY i i)

/-- Section 3, proof of `lem: dominate`, the shrinking loop: adding an envy-free
allocation from the residue does not decrease any agent's bundle advantage. -/
theorem advantage_le_combine (X Y : Allocation n C) (hY : Y.allocated ⊆ X.residue)
    (v : Fin n → Valuation) (hYef : Y.EnvyFree v) (i j : Fin n) :
    (v i).value (X.bundle i).support - (v i).value (X.bundle j).support ≤
      (v i).value ((X.combine Y hY).bundle i).support -
        (v i).value ((X.combine Y hY).bundle j).support := by
  rw [value_bundle_combine, value_bundle_combine]
  linarith [hYef i j]

/-- Combining two envy-free allocations on disjoint parts preserves envy-freeness,
as stated in Section 2 of the paper immediately after the domination definition. -/
theorem envyFree_combine (X Y : Allocation n C) (hY : Y.allocated ⊆ X.residue)
    (v : Fin n → Valuation) (hXef : X.EnvyFree v) (hYef : Y.EnvyFree v) :
    (X.combine Y hY).EnvyFree v := by
  intro i j
  rw [value_bundle_combine, value_bundle_combine]
  exact add_le_add (hXef i j) (hYef i j)

/-- Allocating residue envy-freely among a dominated group preserves global
envy-freeness. This is the four-case argument in Section 2's proof of the main
theorem (`thm: main theorem`); the added allocation need not be complete. -/
theorem envyFree_combine_dominatedGroup (X Y : Allocation n C)
    (hY : Y.allocated ⊆ X.residue) (v : Fin n → Valuation) (E : Set (Fin n))
    (hXef : X.EnvyFree v) (hE : X.DominatedGroup v E)
    (hempty : ∀ i, i ∉ E → (Y.bundle i).support = ∅)
    (hYef : ∀ i ∈ E, ∀ j ∈ E,
      (v i).value (Y.bundle j).support ≤ (v i).value (Y.bundle i).support) :
    (X.combine Y hY).EnvyFree v := by
  intro i j
  rw [value_bundle_combine, value_bundle_combine]
  by_cases hi : i ∈ E
  · by_cases hj : j ∈ E
    · exact add_le_add (hXef i j) (hYef i hi j hj)
    · rw [hempty j hj, Valuation.value_empty, add_zero]
      exact (hXef i j).trans (le_add_of_nonneg_right
        ((v i).value_nonneg (Y.bundle i).measurableSet_support
          (Y.bundle i).support_subset_unit))
  · rw [hempty i hi, Valuation.value_empty, add_zero]
    by_cases hj : j ∈ E
    · calc
        _ ≤ (v i).value (X.bundle j).support + (v i).value X.residue :=
          add_le_add le_rfl ((v i).value_mono (Y.bundle j).measurableSet_support
            X.measurableSet_residue ((Y.bundle_subset_allocated j).trans hY)
            X.residue_subset_unit)
        _ ≤ (v i).value (X.bundle i).support := hE.2.2 i hi j hj
    · simpa only [hempty j hj, Valuation.value_empty, add_zero] using hXef i j

/-- Completing the residue among a dominated group yields a complete envy-free
allocation, as in Section 2's proof of the main theorem (`thm: main theorem`). -/
theorem complete_envyFree_combine_dominatedGroup (X Y : Allocation n C)
    (hY : Y.allocated ⊆ X.residue) (v : Fin n → Valuation) (E : Set (Fin n))
    (hXef : X.EnvyFree v) (hE : X.DominatedGroup v E)
    (hempty : ∀ i, i ∉ E → (Y.bundle i).support = ∅)
    (hYef : ∀ i ∈ E, ∀ j ∈ E,
      (v i).value (Y.bundle j).support ≤ (v i).value (Y.bundle i).support)
    (hfill : Y.allocated = X.residue) :
    (X.combine Y hY).Complete ∧ (X.combine Y hY).EnvyFree v :=
  ⟨complete_combine X Y hY hfill,
    envyFree_combine_dominatedGroup X Y hY v E hXef hE hempty hYef⟩

/-- Allocating further cake from the residue preserves every old domination.
This follows from the domination definition in Section 2 of the paper and is
used in Section 3's proof of `Dominate`, when further `Core` outputs are added.
Neither allocation needs to be envy-free. -/
theorem dominates_combine (X Y : Allocation n C) (hY : Y.allocated ⊆ X.residue)
    (v : Fin n → Valuation) (i j : Fin n) (hdom : X.Dominates v i j) :
    (X.combine Y hY).Dominates v i j := by
  let Z := X.combine Y hY
  have hbudget : (v i).value (Y.bundle j).support + (v i).value Z.residue ≤
      (v i).value X.residue := by
    rw [← (v i).value_union (Y.bundle j).measurableSet_support Z.measurableSet_residue
      (Y.bundle j).support_subset_unit Z.residue_subset_unit
      (disjoint_bundle_residue_combine X Y hY j)]
    exact (v i).value_mono
      ((Y.bundle j).measurableSet_support.union Z.measurableSet_residue)
      X.measurableSet_residue (bundle_union_residue_combine_subset X Y hY j)
      X.residue_subset_unit
  change (v i).value (Z.bundle j).support + (v i).value Z.residue ≤
    (v i).value (Z.bundle i).support
  dsimp only [Z]
  rw [value_bundle_combine, value_bundle_combine]
  calc
    _ = (v i).value (X.bundle j).support +
        ((v i).value (Y.bundle j).support + (v i).value Z.residue) := by
      rw [add_assoc]
    _ ≤ (v i).value (X.bundle j).support + (v i).value X.residue :=
      add_le_add le_rfl hbudget
    _ ≤ (v i).value (X.bundle i).support := hdom
    _ ≤ (v i).value (X.bundle i).support + (v i).value (Y.bundle i).support :=
      le_add_of_nonneg_right ((v i).value_nonneg (Y.bundle i).measurableSet_support
        (Y.bundle i).support_subset_unit)

variable {m : ℕ} {R : Piece}

/-- Relabel an allocation on a smaller cake and agent set, giving empty pieces
to outsiders. This implements `Y_i = ∅` for `i ∉ E` in Section 2's `Divide`. -/
def extendTo (Y : Allocation m R) {E : Set (Fin n)} (e : Fin m ≃ E)
    (hRC : R.support ⊆ C.support) : Allocation n C := by
  classical
  refine {
    bundle := fun i ↦ if hi : i ∈ E then Y.bundle (e.symm ⟨i, hi⟩) else Piece.empty
    contained := ?_
    disjoint := ?_
  }
  · intro i
    split
    · exact (Y.contained _).trans hRC
    · simp
  · intro i j hij
    split <;> split
    · apply Y.disjoint
      intro heq
      have := congrArg (fun k ↦ (e k).val) heq
      simp only [Equiv.apply_symm_apply] at this
      exact hij this
    all_goals simp

@[simp]
theorem bundle_extendTo_mem (Y : Allocation m R) {E : Set (Fin n)} (e : Fin m ≃ E)
    (hRC : R.support ⊆ C.support) (i : Fin n) (hi : i ∈ E) :
    (Y.extendTo e hRC).bundle i = Y.bundle (e.symm ⟨i, hi⟩) := by
  classical
  simp [extendTo, hi]

@[simp]
theorem bundle_extendTo_notMem (Y : Allocation m R) {E : Set (Fin n)} (e : Fin m ≃ E)
    (hRC : R.support ⊆ C.support) (i : Fin n) (hi : i ∉ E) :
    (Y.extendTo e hRC).bundle i = Piece.empty := by
  classical
  simp [extendTo, hi]

theorem allocated_extendTo (Y : Allocation m R) {E : Set (Fin n)} (e : Fin m ≃ E)
    (hRC : R.support ⊆ C.support) : (Y.extendTo e hRC).allocated = Y.allocated := by
  classical
  ext x
  simp only [allocated, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hx⟩
    by_cases hi : i ∈ E
    · rw [bundle_extendTo_mem Y e hRC i hi] at hx
      exact ⟨_, hx⟩
    · simp only [bundle_extendTo_notMem Y e hRC i hi, Piece.support_empty,
        Set.mem_empty_iff_false] at hx
  · rintro ⟨k, hx⟩
    refine ⟨(e k).val, ?_⟩
    rw [bundle_extendTo_mem Y e hRC _ (e k).property]
    change x ∈ (Y.bundle (e.symm (e k))).support
    simpa only [Equiv.symm_apply_apply] using hx

theorem envyFree_extendTo_on (Y : Allocation m R) {E : Set (Fin n)} (e : Fin m ≃ E)
    (hRC : R.support ⊆ C.support) (v : Fin n → Valuation)
    (hYef : Y.EnvyFree (fun k ↦ v (e k).val)) :
    ∀ i ∈ E, ∀ j ∈ E,
      (v i).value ((Y.extendTo e hRC).bundle j).support ≤
        (v i).value ((Y.extendTo e hRC).bundle i).support := by
  intro i hi j hj
  rw [bundle_extendTo_mem Y e hRC j hj, bundle_extendTo_mem Y e hRC i hi]
  simpa only [Equiv.apply_symm_apply] using hYef (e.symm ⟨i, hi⟩) (e.symm ⟨j, hj⟩)

theorem allocated_extendTo_subset_residue (X : Allocation n C) (Y : Allocation m R)
    {E : Set (Fin n)} (e : Fin m ≃ E) (hR : R.support = X.residue) :
    (Y.extendTo e (hR.subset.trans X.residue_subset)).allocated ⊆ X.residue := by
  rw [allocated_extendTo]
  exact Y.allocated_subset.trans hR.subset

/-- Append a recursively obtained allocation of a represented residue, extending
it by empty pieces outside the recursive group, as in Section 2's `Divide`. -/
def combineRecursive (X : Allocation n C) (Y : Allocation m R)
    {E : Set (Fin n)} (e : Fin m ≃ E) (hR : R.support = X.residue) : Allocation n C :=
  X.combine (Y.extendTo e (hR.subset.trans X.residue_subset))
    (allocated_extendTo_subset_residue X Y e hR)

/-- A complete envy-free recursive allocation of the residue among a dominated
group completes the original allocation envy-freely. This is the induction step
in Section 2's proof of the main theorem (`thm: main theorem`). This version
accepts any exact representation; `complete_envyFree_combineResidue` uses the
constructed residue. -/
theorem complete_envyFree_combineRecursive (X : Allocation n C) (Y : Allocation m R)
    (v : Fin n → Valuation) {E : Set (Fin n)} (e : Fin m ≃ E)
    (hR : R.support = X.residue) (hXef : X.EnvyFree v) (hE : X.DominatedGroup v E)
    (hYcomplete : Y.Complete) (hYef : Y.EnvyFree (fun k ↦ v (e k).val)) :
    (X.combineRecursive Y e hR).Complete ∧ (X.combineRecursive Y e hR).EnvyFree v := by
  apply complete_envyFree_combine_dominatedGroup X _ _ v E hXef hE
  · intro i hi
    rw [bundle_extendTo_notMem Y e _ i hi, Piece.support_empty]
  · exact envyFree_extendTo_on Y e _ v hYef
  · rw [allocated_extendTo, hYcomplete, hR]

/-- Combine with an allocation of the constructed residue, without a separate
representation argument. This is Section 2's `X ⊕ Divide(E,R)`. -/
def combineResidue (X : Allocation n C) (Y : Allocation m X.residuePiece)
    {E : Set (Fin n)} (e : Fin m ≃ E) : Allocation n C :=
  X.combineRecursive Y e X.support_residuePiece

/-- Completing the constructed residue among a dominated group completes the
cake envy-freely, as in Section 2's main theorem (`thm: main theorem`). -/
theorem complete_envyFree_combineResidue (X : Allocation n C)
    (Y : Allocation m X.residuePiece) (v : Fin n → Valuation)
    {E : Set (Fin n)} (e : Fin m ≃ E)
    (hXef : X.EnvyFree v) (hE : X.DominatedGroup v E)
    (hYcomplete : Y.Complete) (hYef : Y.EnvyFree (fun k ↦ v (e k).val)) :
    (X.combineResidue Y e).Complete ∧ (X.combineResidue Y e).EnvyFree v :=
  complete_envyFree_combineRecursive X Y v e X.support_residuePiece
    hXef hE hYcomplete hYef

end CakeCuttingPsomas.Allocation
