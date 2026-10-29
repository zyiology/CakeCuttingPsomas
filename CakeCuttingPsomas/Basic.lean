module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Cake, pieces, valuations, and allocations

Definitions from the introduction and Sections 1.3 and 2 of `paper/main.tex`.
Pieces retain an ordered list of intervals, rather than just their union.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas

/-- A nondegenerate interval in the unit cake. Empty pieces use an empty list. -/
structure CakeInterval where
  left : ℝ
  right : ℝ
  left_nonneg : 0 ≤ left
  ordered : left < right
  right_le_one : right ≤ 1

/-- Intervals are half-open, except that an interval ending at 1 includes 1. -/
def CakeInterval.support (I : CakeInterval) : Set ℝ :=
  if I.right = 1 then Set.Icc I.left I.right else Set.Ico I.left I.right

/-- A finite, ordered list of pairwise disjoint intervals. The empty list is allowed. -/
structure Piece where
  intervals : List CakeInterval
  disjoint : intervals.Pairwise (fun I J ↦ Disjoint I.support J.support)

/-- The points belonging to a piece; the list order is forgotten here. -/
def Piece.support (P : Piece) : Set ℝ :=
  {x | ∃ I ∈ P.intervals, x ∈ I.support}

/-- The piece with no intervals. -/
def Piece.empty : Piece where
  intervals := []
  disjoint := by simp

@[simp]
theorem Piece.support_empty : Piece.empty.support = ∅ := by
  ext x
  simp [Piece.support, Piece.empty]

theorem CakeInterval.measurableSet_support (I : CakeInterval) : MeasurableSet I.support := by
  unfold CakeInterval.support
  split
  · exact measurableSet_Icc
  · exact measurableSet_Ico

theorem CakeInterval.support_subset_unit (I : CakeInterval) :
    I.support ⊆ Set.Icc 0 1 := by
  intro x hx
  unfold CakeInterval.support at hx
  split at hx
  · exact ⟨I.left_nonneg.trans hx.1, hx.2.trans I.right_le_one⟩
  · exact ⟨I.left_nonneg.trans hx.1, hx.2.le.trans I.right_le_one⟩

theorem Piece.measurableSet_support (P : Piece) : MeasurableSet P.support := by
  have hs : P.support = ⋃ I ∈ P.intervals, I.support := by
    ext x
    simp [Piece.support]
  rw [hs]
  exact P.intervals.finite_toSet.measurableSet_biUnion fun I _ ↦ I.measurableSet_support

theorem Piece.support_subset_unit (P : Piece) : P.support ⊆ Set.Icc 0 1 := by
  rintro x ⟨I, _, hx⟩
  exact I.support_subset_unit hx

/-- Concatenate two disjoint pieces, preserving their specified interval orders. -/
def Piece.append (P Q : Piece) (h : Disjoint P.support Q.support) : Piece where
  intervals := P.intervals ++ Q.intervals
  disjoint := by
    rw [List.pairwise_append]
    refine ⟨P.disjoint, Q.disjoint, ?_⟩
    intro I hI J hJ
    have hIP : I.support ⊆ P.support := fun _ hx ↦ ⟨I, hI, hx⟩
    have hJQ : J.support ⊆ Q.support := fun _ hx ↦ ⟨J, hJ, hx⟩
    exact h.mono hIP hJQ

@[simp]
theorem Piece.support_append (P Q : Piece) (h : Disjoint P.support Q.support) :
    (P.append Q h).support = P.support ∪ Q.support := by
  ext x
  simp only [Piece.support, Piece.append, List.mem_append, Set.mem_ofPred_eq,
    Set.mem_union]
  constructor
  · rintro ⟨I, hI | hI, hx⟩
    · exact Or.inl ⟨I, hI, hx⟩
    · exact Or.inr ⟨I, hI, hx⟩
  · rintro (⟨I, hI, hx⟩ | ⟨I, hI, hx⟩)
    · exact ⟨I, Or.inl hI, hx⟩
    · exact ⟨I, Or.inr hI, hx⟩

/-- The original cake `[0,1]`. Recursive calls may use other pieces. -/
def unitCake : Piece where
  intervals := [⟨0, 1, le_rfl, zero_lt_one, le_rfl⟩]
  disjoint := by simp

/-- A nonnegative integrable density on the unit cake.
Normalization is separate because recursive calls need unnormalized valuations. -/
structure Valuation where
  density : ℝ → ℝ
  nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ density x
  integrable : MeasureTheory.IntegrableOn density (Set.Icc (0 : ℝ) 1)

/-- An agent's value of a set, with respect to Lebesgue measure. -/
noncomputable def Valuation.value (v : Valuation) (S : Set ℝ) : ℝ :=
  ∫ x in S, v.density x

/-- The initial densities have total value one, as in the introduction. -/
def Valuation.Normalized (v : Valuation) : Prop :=
  v.value (Set.Icc 0 1) = 1

/-- A partial allocation of `C` to `n` agents. `Fin n` indexes the agents. -/
structure Allocation (n : ℕ) (C : Piece) where
  bundle : Fin n → Piece
  contained : ∀ i, (bundle i).support ⊆ C.support
  disjoint : ∀ i j, i ≠ j → Disjoint (bundle i).support (bundle j).support

namespace Allocation

/-- The union of all allocated bundles. -/
def allocated {n : ℕ} {C : Piece} (A : Allocation n C) : Set ℝ :=
  ⋃ i, (A.bundle i).support

/-- The unallocated part of the input cake. -/
def residue {n : ℕ} {C : Piece} (A : Allocation n C) : Set ℝ :=
  C.support \ A.allocated

theorem measurableSet_allocated {n : ℕ} {C : Piece} (A : Allocation n C) :
    MeasurableSet A.allocated :=
  MeasurableSet.iUnion fun i ↦ (A.bundle i).measurableSet_support

theorem allocated_subset {n : ℕ} {C : Piece} (A : Allocation n C) :
    A.allocated ⊆ C.support := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact A.contained i hi

theorem bundle_subset_allocated {n : ℕ} {C : Piece} (A : Allocation n C) (i : Fin n) :
    (A.bundle i).support ⊆ A.allocated :=
  Set.subset_iUnion (fun j ↦ (A.bundle j).support) i

theorem measurableSet_residue {n : ℕ} {C : Piece} (A : Allocation n C) :
    MeasurableSet A.residue :=
  C.measurableSet_support.diff A.measurableSet_allocated

theorem residue_subset {n : ℕ} {C : Piece} (A : Allocation n C) :
    A.residue ⊆ C.support := Set.sdiff_subset

theorem allocated_subset_unit {n : ℕ} {C : Piece} (A : Allocation n C) :
    A.allocated ⊆ Set.Icc 0 1 :=
  A.allocated_subset.trans C.support_subset_unit

theorem residue_subset_unit {n : ℕ} {C : Piece} (A : Allocation n C) :
    A.residue ⊆ Set.Icc 0 1 :=
  A.residue_subset.trans C.support_subset_unit

theorem disjoint_allocated_residue {n : ℕ} {C : Piece} (A : Allocation n C) :
    Disjoint A.allocated A.residue := by
  exact Set.disjoint_left.mpr fun _ hx hr ↦ hr.2 hx

theorem disjoint_bundle_residue {n : ℕ} {C : Piece} (A : Allocation n C) (i : Fin n) :
    Disjoint (A.bundle i).support A.residue :=
  A.disjoint_allocated_residue.mono_left (A.bundle_subset_allocated i)

/-- Completeness is exact set equality, including endpoints. -/
def Complete {n : ℕ} {C : Piece} (A : Allocation n C) : Prop :=
  A.allocated = C.support

/-- Every agent weakly prefers their bundle to every other bundle. -/
def EnvyFree {n : ℕ} {C : Piece} (A : Allocation n C)
    (v : Fin n → Valuation) : Prop :=
  ∀ i j, (v i).value (A.bundle j).support ≤ (v i).value (A.bundle i).support

/-- Agent `i` would not envy `j` even if `j` received all the residue. -/
def Dominates {n : ℕ} {C : Piece} (A : Allocation n C)
    (v : Fin n → Valuation) (i j : Fin n) : Prop :=
  (v i).value (A.bundle j).support + (v i).value A.residue ≤
    (v i).value (A.bundle i).support

/-- A nonempty proper group dominated by every agent outside it. -/
def DominatedGroup {n : ℕ} {C : Piece} (A : Allocation n C)
    (v : Fin n → Valuation) (E : Set (Fin n)) : Prop :=
  E.Nonempty ∧ E ≠ Set.univ ∧ ∀ i, i ∉ E → ∀ j ∈ E, A.Dominates v i j

end Allocation
end CakeCuttingPsomas
