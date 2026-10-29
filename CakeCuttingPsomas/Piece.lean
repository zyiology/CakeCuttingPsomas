module

public import CakeCuttingPsomas.Basic

/-! # Exact operations on ordered pieces

Geometric operations for the piece conventions in Section 1.3 of `paper/main.tex`.
Empty fragments are omitted; splitting at a right endpoint keeps that endpoint
with the whole interval, including at 1.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas

/-- A piece consisting of one nondegenerate interval. -/
def Piece.ofInterval (I : CakeInterval) : Piece := ⟨[I], by simp⟩

@[simp]
theorem Piece.support_ofInterval (I : CakeInterval) :
    (Piece.ofInterval I).support = I.support := by
  ext x
  simp [Piece.support, Piece.ofInterval]

/-- The initial fragment at coordinate `x`, clamped to the interval. -/
def CakeInterval.before (I : CakeInterval) (x : ℝ) : Piece :=
  if hr : I.right ≤ x then Piece.ofInterval I
  else if hl : I.left < x then
    Piece.ofInterval ⟨I.left, x, I.left_nonneg, hl, (le_of_not_ge hr).trans I.right_le_one⟩
  else Piece.empty

/-- The remaining fragment at coordinate `x`, clamped to the interval. -/
def CakeInterval.after (I : CakeInterval) (x : ℝ) : Piece :=
  if hr : I.right ≤ x then Piece.empty
  else if hl : x ≤ I.left then Piece.ofInterval I
  else Piece.ofInterval ⟨x, I.right, I.left_nonneg.trans (le_of_not_ge hl),
    lt_of_not_ge hr, I.right_le_one⟩

theorem CakeInterval.support_before (I : CakeInterval) (x : ℝ) :
    (I.before x).support =
      if I.right ≤ x then I.support else I.support ∩ Set.Iio x := by
  unfold before
  split
  · simp_all
  · split
    · simp only [Piece.support_ofInterval]
      ext y
      simp only [CakeInterval.support, Set.mem_inter_iff, Set.mem_Iio]
      have := I.right_le_one
      have := I.ordered
      split_ifs <;> simp_all only [Set.mem_Icc, Set.mem_Ico] <;> grind
    · simp only [Piece.support_empty]
      ext y
      simp only [CakeInterval.support, Set.mem_inter_iff, Set.mem_Iio, Set.mem_empty_iff_false]
      split_ifs <;> simp_all only [Set.mem_Icc, Set.mem_Ico] <;> grind

theorem CakeInterval.support_after (I : CakeInterval) (x : ℝ) :
    (I.after x).support =
      if I.right ≤ x then ∅ else I.support ∩ Set.Ici x := by
  unfold after
  split
  · simp_all
  · split
    · simp only [Piece.support_ofInterval]
      ext y
      simp only [CakeInterval.support, Set.mem_inter_iff, Set.mem_Ici]
      split_ifs <;> simp_all only [Set.mem_Icc, Set.mem_Ico] <;> grind
    · simp only [Piece.support_ofInterval]
      ext y
      simp only [CakeInterval.support, Set.mem_inter_iff, Set.mem_Ici]
      split_ifs <;> simp_all only [Set.mem_Icc, Set.mem_Ico] <;> grind

theorem CakeInterval.before_subset (I : CakeInterval) (x : ℝ) :
    (I.before x).support ⊆ I.support := by
  rw [support_before]
  split <;> simp [Set.inter_subset_left]

theorem CakeInterval.after_subset (I : CakeInterval) (x : ℝ) :
    (I.after x).support ⊆ I.support := by
  rw [support_after]
  split <;> simp [Set.inter_subset_left]

/-- Splitting respects exact endpoint ownership, as required by the piece
conventions in Section 1.3 of the paper. -/
theorem CakeInterval.split_disjoint (I : CakeInterval) (x : ℝ) :
    Disjoint (I.before x).support (I.after x).support := by
  rw [support_before, support_after]
  split_ifs <;> simp_all [Set.disjoint_left]

/-- The two fragments cover the original interval exactly (Section 1.3). -/
theorem CakeInterval.split_union (I : CakeInterval) (x : ℝ) :
    (I.before x).support ∪ (I.after x).support = I.support := by
  rw [support_before, support_after]
  split_ifs
  · simp
  · ext y
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
    grind

@[simp]
theorem CakeInterval.before_left (I : CakeInterval) : I.before I.left = Piece.empty := by
  simp [before, not_le.mpr I.ordered]

@[simp]
theorem CakeInterval.after_left (I : CakeInterval) :
    I.after I.left = Piece.ofInterval I := by
  simp [after, not_le.mpr I.ordered]

@[simp]
theorem CakeInterval.before_right (I : CakeInterval) :
    I.before I.right = Piece.ofInterval I := by simp [before]

@[simp]
theorem CakeInterval.after_right (I : CakeInterval) : I.after I.right = Piece.empty := by
  simp [after]

/-- Remove an interval, retaining the left fragment before the right fragment. -/
def CakeInterval.diff (I J : CakeInterval) : Piece :=
  (I.before J.left).append
    (if J.right = 1 then Piece.empty else I.after J.right) (by
      have hJ := J.ordered
      have hI := I.ordered
      have hIr := I.right_le_one
      rw [support_before]
      split_ifs <;> simp only [Piece.support_empty, support_after]
      all_goals try split_ifs
      all_goals apply Set.disjoint_left.mpr
      all_goals intro y hy hz
      all_goals
        simp only [CakeInterval.support, Set.mem_inter_iff, Set.mem_Iio,
          Set.mem_Ici, Set.mem_empty_iff_false] at hy hz
      all_goals
        split_ifs at hy <;> simp_all only [Set.mem_Icc, Set.mem_Ico] <;> grind)

/-- Exact interval subtraction under the endpoint convention of Section 1.3.
There are at most two surviving fragments. -/
theorem CakeInterval.support_diff (I J : CakeInterval) :
    (I.diff J).support = I.support \ J.support := by
  rw [diff, Piece.support_append, support_before]
  have hJl : J.left < 1 := J.ordered.trans_le J.right_le_one
  have hI := I.ordered
  have hIr := I.right_le_one
  have hJ := J.ordered
  split_ifs <;> simp only [Piece.support_empty, support_after] <;>
    (try split_ifs) <;> ext y <;>
    simp only [CakeInterval.support, Set.mem_union, Set.mem_inter_iff,
      Set.mem_Iio, Set.mem_Ici, Set.mem_sdiff, Set.mem_empty_iff_false] <;>
    (try split_ifs) <;> simp_all only [Set.mem_Icc, Set.mem_Ico] <;> grind

/-- Interval subtraction creates at most two nonempty components. -/
theorem CakeInterval.length_diff_le_two (I J : CakeInterval) :
    (I.diff J).intervals.length ≤ 2 := by
  simp only [diff, Piece.append, List.length_append]
  unfold before after
  split_ifs <;> simp [Piece.ofInterval, Piece.empty]

/-- Subtract one interval from each component without changing component order. -/
def Piece.eraseInterval (P : Piece) (J : CakeInterval) : Piece where
  intervals := P.intervals.flatMap fun I ↦ (I.diff J).intervals
  disjoint := by
    rw [List.pairwise_flatMap]
    refine ⟨fun I _ ↦ (I.diff J).disjoint, ?_⟩
    apply P.disjoint.imp
    intro I K hIK A hA B hB
    have hsub (L : CakeInterval) (M : CakeInterval) (hM : M ∈ (L.diff J).intervals) :
        M.support ⊆ L.support := by
      intro x hx
      have : x ∈ (L.diff J).support := ⟨M, hM, hx⟩
      rw [CakeInterval.support_diff] at this
      exact this.1
    exact hIK.mono (hsub I A hA) (hsub K B hB)

theorem Piece.support_eraseInterval (P : Piece) (J : CakeInterval) :
    (P.eraseInterval J).support = P.support \ J.support := by
  ext x
  simp only [Piece.support, eraseInterval, List.mem_flatMap, Set.mem_ofPred_eq,
    Set.mem_sdiff]
  constructor
  · rintro ⟨K, ⟨I, hI, hK⟩, hx⟩
    have : x ∈ (I.diff J).support := ⟨K, hK, hx⟩
    rw [CakeInterval.support_diff] at this
    exact ⟨⟨I, hI, this.1⟩, this.2⟩
  · rintro ⟨⟨I, hI, hx⟩, hJ⟩
    have : x ∈ (I.diff J).support := by
      rw [CakeInterval.support_diff]
      exact ⟨hx, hJ⟩
    obtain ⟨K, hK, hxK⟩ := this
    exact ⟨K, ⟨I, hI, hK⟩, hxK⟩

/-- Subtract a list of intervals, retaining the source piece's order. -/
def Piece.diffIntervals (P : Piece) : List CakeInterval → Piece
  | [] => P
  | J :: Js => (P.eraseInterval J).diffIntervals Js

theorem Piece.support_diffIntervals (P : Piece) (Js : List CakeInterval) :
    (P.diffIntervals Js).support =
      P.support \ {x | ∃ J ∈ Js, x ∈ J.support} := by
  induction Js generalizing P with
  | nil => simp [diffIntervals]
  | cons J Js ih =>
    rw [diffIntervals, ih, support_eraseInterval]
    ext x
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, List.mem_cons]
    grind

/-- Exact subtraction of pieces, preserving the minuend's specified order. -/
def Piece.diff (P Q : Piece) : Piece := P.diffIntervals Q.intervals

/-- Piece subtraction represents exact set difference, including endpoints.
This supplies the residue required by Section 2's recursive `Divide`. -/
@[simp]
theorem Piece.support_diff (P Q : Piece) :
    (P.diff Q).support = P.support \ Q.support :=
  P.support_diffIntervals Q.intervals

@[simp]
theorem Piece.diff_empty (P : Piece) : P.diff Piece.empty = P := rfl

@[simp]
theorem Piece.support_empty_diff (P : Piece) :
    (Piece.empty.diff P).support = ∅ := by simp

@[simp]
theorem Piece.support_diff_self (P : Piece) : (P.diff P).support = ∅ := by simp

/-- A piece with empty support has no components, since stored intervals have
positive length. Its interval order therefore has a unique empty representation. -/
theorem Piece.eq_empty_of_support_eq_empty (P : Piece) (h : P.support = ∅) :
    P = Piece.empty := by
  cases P with
  | mk Is hd =>
    cases Is with
    | nil => rfl
    | cons I Is =>
      have hx : I.left ∈ I.support := by
        unfold CakeInterval.support
        split
        · exact ⟨le_rfl, I.ordered.le⟩
        · exact ⟨le_rfl, I.ordered⟩
      have : I.left ∈ (Piece.mk (I :: Is) hd).support := ⟨I, List.mem_cons_self, hx⟩
      rw [h] at this
      exact this.elim

namespace Allocation

/-- The residue as an ordered piece, constructed from endpoints alone.
This represents the input of the recursive call in Section 2's `Divide`. -/
def residuePiece {n : ℕ} {C : Piece} (X : Allocation n C) : Piece :=
  C.diffIntervals ((List.finRange n).flatMap fun i ↦ (X.bundle i).intervals)

/-- Every partial allocation has an exact represented residue, as needed in
Section 2's proof of the main theorem (`thm: main theorem`). -/
@[simp]
theorem support_residuePiece {n : ℕ} {C : Piece} (X : Allocation n C) :
    X.residuePiece.support = X.residue := by
  rw [residuePiece, Piece.support_diffIntervals]
  congr 1
  ext x
  simp only [allocated, Piece.support, List.mem_flatMap, List.mem_finRange, true_and,
    Set.mem_ofPred_eq, Set.mem_iUnion]
  grind

end Allocation
end CakeCuttingPsomas
