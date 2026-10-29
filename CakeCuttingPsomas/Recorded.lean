module

public import CakeCuttingPsomas.Prefix

-- This project does not prescribe mathlib's copyright/license header format.
set_option linter.style.header false

/-! # Recorded interval values

The shared partition and inherited records of Section 1.3 of `paper/main.tex`.
Data contain only cut geometry and real query answers. Correctness relative to
valuations is a separate predicate, never an input to internal computation.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas

local instance : DecidableEq CakeInterval := Classical.decEq _

namespace Piece

/-- Replace a component by a representation of the same support, keeping order. -/
def replaceInterval (P : Piece) (I : CakeInterval) (Q : Piece)
    (hQ : Q.support = I.support) : Piece where
  intervals := P.intervals.flatMap fun J ↦ if J = I then Q.intervals else [J]
  disjoint := by
    rw [List.pairwise_flatMap]
    constructor
    · intro J _
      split_ifs
      · exact Q.disjoint
      · simp
    · apply P.disjoint.imp
      intro J K hJK A hA B hB
      have sub (J A : CakeInterval)
          (hA : A ∈ if J = I then Q.intervals else [J]) : A.support ⊆ J.support := by
        split_ifs at hA with h
        · subst J
          exact fun x hx ↦ hQ ▸ (show x ∈ Q.support from ⟨A, hA, hx⟩)
        · simp only [List.mem_singleton] at hA
          subst A
          exact Set.Subset.rfl
      exact hJK.mono (sub J A hA) (sub K B hB)

@[simp]
theorem support_replaceInterval (P : Piece) (I : CakeInterval) (Q : Piece)
    (hQ : Q.support = I.support) : (P.replaceInterval I Q hQ).support = P.support := by
  ext x
  simp only [support, replaceInterval, List.mem_flatMap, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨A, ⟨J, hJ, hA⟩, hx⟩
    by_cases h : J = I
    · subst J
      simp only [↓reduceIte] at hA
      exact ⟨I, hJ, hQ ▸ (show x ∈ Q.support from ⟨A, hA, hx⟩)⟩
    · simp only [ite_eq_right h, List.mem_singleton] at hA
      exact ⟨J, hJ, hA ▸ hx⟩
  · rintro ⟨J, hJ, hx⟩
    by_cases h : J = I
    · subst J
      obtain ⟨A, hA, hxA⟩ := (hQ.symm ▸ hx : x ∈ Q.support)
      exact ⟨A, ⟨I, hJ, by simpa using hA⟩, hxA⟩
    · exact ⟨J, ⟨J, hJ, by simp [h]⟩, hx⟩

/-- Finite additivity for an ordered piece; no queries are required to sum values. -/
theorem value_eq_sum (P : Piece) (v : Valuation) :
    v.value P.support = (P.intervals.map fun I ↦ v.value I.support).sum := by
  obtain ⟨Is, h⟩ := P
  induction Is with
  | nil => simp [support]
  | cons I Is ih =>
    let T : Piece := ⟨Is, (List.pairwise_cons.mp h).2⟩
    have hs : (⟨I :: Is, h⟩ : Piece).support = I.support ∪ T.support := by
      ext x
      simp [support, T]
    have hd : Disjoint I.support T.support := by
      rw [Set.disjoint_left]
      rintro x hx ⟨J, hJ, hxJ⟩
      exact Set.disjoint_left.mp ((List.pairwise_cons.mp h).1 J hJ) hx hxJ
    rw [hs, v.value_union I.measurableSet_support T.measurableSet_support
      I.support_subset_unit T.support_subset_unit hd]
    simpa [T] using congrArg (v.value I.support + ·) (ih T.disjoint)

end Piece

/-- A shared partition of the unit cake and recorded values for the current agents.
The partition's list order is independent of each handled piece's traversal order. -/
structure RecordedState (n : ℕ) where
  partition : Piece
  covers : partition.support = Set.Icc 0 1
  values : Fin n → CakeInterval → ℝ

namespace RecordedState

/-- Each stored cell value is correct. No normalization is required. -/
def Correct {n : ℕ} (s : RecordedState n) (v : Fin n → Valuation) : Prop :=
  ∀ i I, I ∈ s.partition.intervals → s.values i I = (v i).value I.support

/-- Pieces retain their own interval order but use cells of the shared partition. -/
def Compatible {n : ℕ} (s : RecordedState n) (P : Piece) : Prop :=
  ∀ I ∈ P.intervals, I ∈ s.partition.intervals

/-- Free internal computation from inherited records. -/
def pieceValue {n : ℕ} (s : RecordedState n) (i : Fin n) (P : Piece) : ℝ :=
  (P.intervals.map (s.values i)).sum

/-- Recorded sums recover exact bundle and residue values (Section 1.3). -/
theorem pieceValue_eq {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) {P : Piece} (hP : s.Compatible P) (i : Fin n) :
    s.pieceValue i P = (v i).value P.support := by
  rw [P.value_eq_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro I hI
  exact hs i I (hP I hI)

/-- Restriction to participating agents inherits the partition and records for free. -/
def restrict {m n : ℕ} (s : RecordedState n) (f : Fin m → Fin n) : RecordedState m :=
  ⟨s.partition, s.covers, fun i ↦ s.values (f i)⟩

theorem correct_restrict {m n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) (f : Fin m → Fin n) : (s.restrict f).Correct (v ∘ f) :=
  fun i I hI ↦ hs (f i) I hI

@[simp]
theorem compatible_restrict {m n : ℕ} (s : RecordedState n) (f : Fin m → Fin n)
    (P : Piece) : (s.restrict f).Compatible P ↔ s.Compatible P := Iff.rfl

/-- Initial records are the known normalized values, without any Eval queries. -/
def initial (n : ℕ) : RecordedState n where
  partition := unitCake
  covers := by ext x; simp [unitCake, Piece.support, CakeInterval.support]
  values := fun _ _ ↦ 1

theorem correct_initial {n : ℕ} (v : Fin n → Valuation) (hv : ∀ i, (v i).Normalized) :
    (initial n).Correct v := by
  intro i I hI
  simp only [initial, unitCake, List.mem_singleton] at hI
  subst I
  simpa [initial, CakeInterval.support, Valuation.Normalized] using (hv i).symm

end RecordedState
namespace CakeInterval

/-- Left cell of a genuine interior split. -/
def leftCell (I : CakeInterval) (x : ℝ) (hl : I.left < x) (hr : x < I.right) : CakeInterval :=
  ⟨I.left, x, I.left_nonneg, hl, hr.le.trans I.right_le_one⟩

/-- Right cell of a genuine interior split. -/
def rightCell (I : CakeInterval) (x : ℝ) (hl : I.left < x) (hr : x < I.right) : CakeInterval :=
  ⟨x, I.right, I.left_nonneg.trans hl.le, hr, I.right_le_one⟩

/-- The ordered two-cell replacement of an interval. -/
def splitCell (I : CakeInterval) (x : ℝ) : Piece :=
  (I.before x).append (I.after x) (I.split_disjoint x)

@[simp]
theorem support_splitCell (I : CakeInterval) (x : ℝ) : (I.splitCell x).support = I.support := by
  simp only [splitCell, Piece.support_append, I.split_union x]

theorem intervals_splitCell (I : CakeInterval) (x : ℝ)
    (hl : I.left < x) (hr : x < I.right) :
    (I.splitCell x).intervals = [I.leftCell x hl hr, I.rightCell x hl hr] := by
  simp [splitCell, before, after, not_le.mpr hr, not_le.mpr hl, hl,
    Piece.append, Piece.ofInterval, leftCell, rightCell]

theorem left_mem_support (I : CakeInterval) : I.left ∈ I.support := by
  simp only [support]
  split_ifs <;> exact ⟨le_rfl, by first | exact I.ordered.le | exact I.ordered⟩

theorem cell_ne_of_disjoint {I J K : CakeInterval} (hd : Disjoint J.support I.support)
    (hK : K.support ⊆ I.support) : J ≠ K := by
  rintro rfl
  exact Set.disjoint_left.mp hd J.left_mem_support (hK J.left_mem_support)

end CakeInterval

namespace RecordedState

/-- Refinement data after querying the left part of a genuinely split cell.
All other values are inherited; right values use subtraction (Section 1.3). -/
def split {n : ℕ} (s : RecordedState n) (I : CakeInterval) (x : ℝ)
    (hl : I.left < x) (hr : x < I.right) (a : Fin n → ℝ) : RecordedState n where
  partition := s.partition.replaceInterval I (I.splitCell x) (I.support_splitCell x)
  covers := by rw [Piece.support_replaceInterval]; exact s.covers
  values := fun i J ↦ if J = I.leftCell x hl hr then a i
    else if J = I.rightCell x hl hr then s.values i I - a i else s.values i J

/-- A piece's representation is refined without changing its support or order. -/
def refinePiece (P : Piece) (I : CakeInterval) (x : ℝ) : Piece :=
  P.replaceInterval I (I.splitCell x) (I.support_splitCell x)

@[simp]
theorem support_refinePiece (P : Piece) (I : CakeInterval) (x : ℝ) :
    (refinePiece P I x).support = P.support := P.support_replaceInterval _ _ _

/-- Updating a partition preserves every previously compatible piece by subdivision. -/
theorem compatible_split {n : ℕ} (s : RecordedState n) {P : Piece}
    (hP : s.Compatible P) (I : CakeInterval) (x : ℝ)
    (hl : I.left < x) (hr : x < I.right) (a : Fin n → ℝ) :
    (s.split I x hl hr a).Compatible (refinePiece P I x) := by
  intro J hJ
  obtain ⟨K, hK, hJ⟩ := List.mem_flatMap.mp hJ
  exact List.mem_flatMap.mpr ⟨K, hP K hK, hJ⟩

/-- The recorded-value update is sound, including zero-valued fragments.
This is the subtraction rule in Section 1.3 of the paper. -/
theorem correct_split {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) (I : CakeInterval) (hI : I ∈ s.partition.intervals) (x : ℝ)
    (hl : I.left < x) (hr : x < I.right) (a : Fin n → ℝ)
    (ha : ∀ i, a i = (v i).value (Set.Icc I.left x)) :
    (s.split I x hl hr a).Correct v := by
  let L := I.leftCell x hl hr
  let R := I.rightCell x hl hr
  have hb : I.before x = Piece.ofInterval L := by
    simp [CakeInterval.before, not_le.mpr hr, hl, L, CakeInterval.leftCell]
  have he : I.after x = Piece.ofInterval R := by
    simp [CakeInterval.after, not_le.mpr hr, not_le.mpr hl, R, CakeInterval.rightCell]
  have hL : L.support ⊆ I.support := by
    simpa [hb] using I.before_subset x
  have hR : R.support ⊆ I.support := by
    simpa [he] using I.after_subset x
  have hLR : L ≠ R := by
    intro h
    have hd := I.split_disjoint x
    rw [hb, he, Piece.support_ofInterval, Piece.support_ofInterval, h] at hd
    exact Set.disjoint_left.mp hd R.left_mem_support R.left_mem_support
  have valL (i : Fin n) : a i = (v i).value L.support := by
    rw [← Piece.support_ofInterval, ← hb, (v i).value_before I ⟨hl.le, hr.le⟩]
    exact ha i
  have valR (i : Fin n) : s.values i I - a i = (v i).value R.support := by
    have hv := (v i).value_union (I.before x).measurableSet_support
      (I.after x).measurableSet_support (I.before x).support_subset_unit
      (I.after x).support_subset_unit (I.split_disjoint x)
    rw [I.split_union, hb, he, Piece.support_ofInterval, Piece.support_ofInterval] at hv
    rw [hs i I hI, valL i]
    linarith
  intro i J hJ
  obtain ⟨K, hK, hJ⟩ := List.mem_flatMap.mp hJ
  by_cases hKI : K = I
  · subst K
    simp only [↓reduceIte, I.intervals_splitCell x hl hr, List.mem_cons,
      List.not_mem_nil, or_false] at hJ
    rcases hJ with rfl | rfl
    · simpa [split, L] using valL i
    · simpa [split, L, R, Ne.symm hLR] using valR i
  · simp only [ite_eq_right hKI, List.mem_singleton] at hJ
    subst J
    have hd : Disjoint K.support I.support := by
      have : Std.Symm (fun A B : CakeInterval ↦ Disjoint A.support B.support) :=
        ⟨fun _ _ h ↦ h.symm⟩
      exact s.partition.disjoint.forall hK hI hKI
    have hnL := CakeInterval.cell_ne_of_disjoint hd hL
    have hnR := CakeInterval.cell_ne_of_disjoint hd hR
    simpa [split, L, R, hnL, hnR] using hs i K hK

end RecordedState

namespace RecordedState

/-- A set is a union of current cells; its representation can be used in a later call. -/
def Represents {n : ℕ} (s : RecordedState n) (S : Set ℝ) : Prop :=
  ∃ P : Piece, s.Compatible P ∧ P.support = S

/-- Every previously represented piece remains representable after refinement. -/
def Refines {n : ℕ} (s s' : RecordedState n) : Prop :=
  ∀ P, s.Compatible P → s'.Represents P.support

theorem refines_refl {n : ℕ} (s : RecordedState n) : s.Refines s :=
  fun P hP ↦ ⟨P, hP, rfl⟩

theorem Refines.trans {n : ℕ} {s s' s'' : RecordedState n}
    (h : s.Refines s') (h' : s'.Refines s'') : s.Refines s'' := by
  intro P hP
  obtain ⟨Q, hQ, hQP⟩ := h P hP
  obtain ⟨R, hR, hRQ⟩ := h' Q hQ
  exact ⟨R, hR, hRQ.trans hQP⟩

/-- Cell subtraction uses only interval identities, without valuation queries. -/
def subtract {n : ℕ} (_s : RecordedState n) (P Q : Piece) : Piece where
  intervals := P.intervals.filter (fun I ↦ decide (I ∉ Q.intervals))
  disjoint := P.disjoint.filter _

theorem compatible_subtract {n : ℕ} {s : RecordedState n} {P Q : Piece}
    (hP : s.Compatible P) : s.Compatible (s.subtract P Q) := by
  intro I hI
  exact hP I (List.mem_filter.mp hI).1

/-- On compatible pieces cell subtraction agrees with exact set subtraction. -/
theorem support_subtract {n : ℕ} {s : RecordedState n} {P Q : Piece}
    (hP : s.Compatible P) (hQ : s.Compatible Q) :
    (s.subtract P Q).support = P.support \ Q.support := by
  ext x
  constructor
  · rintro ⟨I, hI, hxI⟩
    have hi := List.mem_filter.mp hI
    have hn : I ∉ Q.intervals := of_decide_eq_true hi.2
    refine ⟨⟨I, hi.1, hxI⟩, ?_⟩
    rintro ⟨J, hJ, hxJ⟩
    have hne : I ≠ J := fun h ↦ hn (h ▸ hJ)
    have : Std.Symm (fun A B : CakeInterval ↦ Disjoint A.support B.support) :=
      ⟨fun _ _ h ↦ h.symm⟩
    exact Set.disjoint_left.mp (s.partition.disjoint.forall (hP I hi.1) (hQ J hJ) hne)
      hxI hxJ
  · rintro ⟨⟨I, hI, hxI⟩, hn⟩
    exact ⟨I, List.mem_filter.mpr ⟨hI, by
      simp only [decide_eq_true_eq]
      exact fun h ↦ hn ⟨I, h, hxI⟩⟩, hxI⟩

/-- Residues of represented sets remain represented by inherited cells. -/
theorem Represents.diff {n : ℕ} {s : RecordedState n} {S T : Set ℝ}
    (hS : s.Represents S) (hT : s.Represents T) : s.Represents (S \ T) := by
  obtain ⟨P, hP, rfl⟩ := hS
  obtain ⟨Q, hQ, rfl⟩ := hT
  exact ⟨s.subtract P Q, compatible_subtract hP, support_subtract hP hQ⟩

/-- Disjoint represented pieces can be concatenated in the specified order. -/
theorem Represents.union {n : ℕ} {s : RecordedState n} {S T : Set ℝ}
    (hS : s.Represents S) (hT : s.Represents T) (hd : Disjoint S T) :
    s.Represents (S ∪ T) := by
  obtain ⟨P, hP, rfl⟩ := hS
  obtain ⟨Q, hQ, rfl⟩ := hT
  refine ⟨P.append Q hd, ?_, P.support_append Q hd⟩
  intro I hI
  rcases List.mem_append.mp hI with hI | hI
  · exact hP I hI
  · exact hQ I hI

theorem represents_empty {n : ℕ} (s : RecordedState n) : s.Represents ∅ :=
  by
    refine ⟨Piece.empty, ?_, Piece.support_empty⟩
    intro I h
    cases h

/-- Restricting participation retains every represented recursive input cake. -/
theorem Represents.restrict {m n : ℕ} {s : RecordedState n} {S : Set ℝ}
    (hS : s.Represents S) (f : Fin m → Fin n) : (s.restrict f).Represents S := hS

end RecordedState

namespace RecordedState

/-- All old pieces survive a cell refinement as unions of new cells. -/
theorem refines_split {n : ℕ} (s : RecordedState n) (I : CakeInterval) (x : ℝ)
    (hl : I.left < x) (hr : x < I.right) (a : Fin n → ℝ) :
    s.Refines (s.split I x hl hr a) := by
  intro P hP
  exact ⟨refinePiece P I x, compatible_split s hP I x hl hr a, support_refinePiece P I x⟩

/-- Both sides of a split are represented in the updated partition. -/
theorem compatible_split_fragments {n : ℕ} (s : RecordedState n) (I : CakeInterval)
    (hI : I ∈ s.partition.intervals) (x : ℝ) (hl : I.left < x) (hr : x < I.right)
    (a : Fin n → ℝ) :
    (s.split I x hl hr a).Compatible (I.before x) ∧
      (s.split I x hl hr a).Compatible (I.after x) := by
  have mem (J : CakeInterval) (hJ : J ∈ (I.splitCell x).intervals) :
      J ∈ (s.split I x hl hr a).partition.intervals :=
    List.mem_flatMap.mpr ⟨I, hI, by simpa using hJ⟩
  constructor
  · intro J hJ
    exact mem J (List.mem_append_left _ hJ)
  · intro J hJ
    exact mem J (List.mem_append_right _ hJ)

/-- Refinement preserves every cell other than the one being split. -/
theorem mem_split_of_ne {n : ℕ} (s : RecordedState n) (I J : CakeInterval)
    (hJ : J ∈ s.partition.intervals) (hne : J ≠ I) (x : ℝ)
    (hl : I.left < x) (hr : x < I.right) (a : Fin n → ℝ) :
    J ∈ (s.split I x hl hr a).partition.intervals :=
  List.mem_flatMap.mpr ⟨J, hJ, by simp [hne]⟩

end RecordedState

namespace RecordedState

/-- Build a residue from whole cells, retaining the input cake's traversal order.
Only interval identities are inspected; no new valuation queries are needed. -/
def allocationResidue {n : ℕ} (_s : RecordedState n) {C : Piece}
    (X : Allocation n C) : Piece where
  intervals := C.intervals.filter (fun I ↦ decide (∀ i, I ∉ (X.bundle i).intervals))
  disjoint := C.disjoint.filter _

theorem compatible_allocationResidue {n : ℕ} {s : RecordedState n} {C : Piece}
    (X : Allocation n C) (hC : s.Compatible C) : s.Compatible (s.allocationResidue X) := by
  intro I hI
  exact hC I (List.mem_filter.mp hI).1

/-- The cell-based residue represents Section 2's exact unallocated cake.
In particular recursive calls can reuse all participating agents' cell values. -/
theorem support_allocationResidue {n : ℕ} {s : RecordedState n} {C : Piece}
    (X : Allocation n C) (hC : s.Compatible C) (hX : ∀ i, s.Compatible (X.bundle i)) :
    (s.allocationResidue X).support = X.residue := by
  ext x
  constructor
  · rintro ⟨I, hI, hxI⟩
    have hi := List.mem_filter.mp hI
    have hn : ∀ i, I ∉ (X.bundle i).intervals := of_decide_eq_true hi.2
    refine ⟨⟨I, hi.1, hxI⟩, ?_⟩
    intro hx
    obtain ⟨i, J, hJ, hxJ⟩ := Set.mem_iUnion.mp hx
    have hne : I ≠ J := fun h ↦ hn i (h ▸ hJ)
    have : Std.Symm (fun A B : CakeInterval ↦ Disjoint A.support B.support) :=
      ⟨fun _ _ h ↦ h.symm⟩
    exact Set.disjoint_left.mp (s.partition.disjoint.forall (hC I hi.1) (hX i J hJ) hne)
      hxI hxJ
  · rintro ⟨⟨I, hI, hxI⟩, hn⟩
    refine ⟨I, List.mem_filter.mpr ⟨hI, ?_⟩, hxI⟩
    simp only [decide_eq_true_eq]
    intro i h
    exact hn (Set.mem_iUnion.mpr ⟨i, I, h, hxI⟩)

/-- Recursive residue values are sums of existing records, with zero queries. -/
theorem allocationResidue_value {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) {C : Piece} (X : Allocation n C) (hC : s.Compatible C)
    (hX : ∀ i, s.Compatible (X.bundle i)) (i : Fin n) :
    s.pieceValue i (s.allocationResidue X) = (v i).value X.residue := by
  rw [pieceValue_eq hs (compatible_allocationResidue X hC), support_allocationResidue X hC hX]

/-- A refinement can be inherited by a smaller participating group. -/
theorem Refines.restrict {m n : ℕ} {s s' : RecordedState n} (h : s.Refines s')
    (f : Fin m → Fin n) : (s.restrict f).Refines (s'.restrict f) :=
  fun P hP ↦ (h P hP).restrict f

end RecordedState

end CakeCuttingPsomas
