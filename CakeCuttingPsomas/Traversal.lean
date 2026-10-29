module

public import CakeCuttingPsomas.Recorded

set_option linter.style.header false

/-! # Traversal-preserving refinement

Section 1.3 and Section 4, `line:rep:cells`: subdivision changes interval
representations, but must not change the common traversal used for marks.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas

attribute [local instance] Classical.propDecidable

namespace Piece

private theorem prefixIntervals_append (Is Js : List CakeInterval) (t : ℝ) :
    prefixIntervals (Is ++ Js) t = prefixIntervals Is t ++
      prefixIntervals Js (t - (Is.map CakeInterval.length).sum) := by
  induction Is generalizing t with
  | nil => simp [prefixIntervals]
  | cons I Is ih =>
    simp only [List.cons_append, prefixIntervals, ih, List.map_cons, List.sum_cons,
      List.append_assoc]
    congr 2
    congr 1
    ring

@[simp] theorem length_append (P Q : Piece) (h : Disjoint P.support Q.support) :
    (P.append Q h).length = P.length + Q.length := by
  simp [length, append]

theorem support_prefix_append (P Q : Piece) (h : Disjoint P.support Q.support) (t : ℝ) :
    ((P.append Q h).prefixAt t).support =
      (P.prefixAt t).support ∪ (Q.prefixAt (t - P.length)).support := by
  ext x
  simp only [prefixAt, append, prefixIntervals_append, support, Set.mem_ofPred_eq,
    List.mem_append, Set.mem_union, length]
  grind

/-- Distinct traversal positions leave a nonempty intervening piece, even
when its value is zero to every participating agent (Section 1.3). -/
theorem exists_mem_prefix_diff (P : Piece) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ P.length) :
    ∃ y, y ∈ (P.prefixAt b).support ∧ y ∉ (P.prefixAt a).support := by
  obtain ⟨Is, hd⟩ := P
  induction Is generalizing a b with
  | nil => simp [length] at hb; linarith
  | cons I Is ih =>
    let T : Piece := ⟨Is, (List.pairwise_cons.mp hd).2⟩
    by_cases haI : a < I.length
    · let y := I.left + a
      have hyI : y ∈ I.support := by
        have hyl : I.left ≤ y := by dsimp [y]; linarith
        have hyr : y < I.right := by dsimp [y, CakeInterval.length] at *; linarith
        simp only [CakeInterval.support]
        split_ifs <;> exact ⟨hyl, by first | exact hyr.le | exact hyr⟩
      have hyb : y ∈ (I.before (I.left + b)).support := by
        rw [CakeInterval.support_before]
        split_ifs
        · exact hyI
        · exact ⟨hyI, by simpa only [y, Set.mem_Iio, add_comm] using add_lt_add_left hab I.left⟩
      have hya : y ∉ (I.before (I.left + a)).support := by
        rw [CakeInterval.support_before,
          ite_eq_right (by dsimp [CakeInterval.length] at haI; linarith)]
        exact fun h ↦ (lt_irrefl y) h.2
      have htail : T.prefixAt (a - I.length) = Piece.empty :=
        T.prefix_nonpos (by linarith)
      refine ⟨y, ?_, ?_⟩
      · rw [support_prefixAt_cons]
        exact Or.inl hyb
      · rw [support_prefixAt_cons]
        change y ∉ (I.before (I.left + a)).support ∪ (T.prefixAt (a - I.length)).support
        simp only [htail, support_empty, Set.union_empty]
        exact hya
    · have hlen : (⟨I :: Is, hd⟩ : Piece).length = I.length + T.length := by
        simp [length, T]
      obtain ⟨y, hyb, hya⟩ := ih (by linarith : 0 ≤ a - I.length)
        (by linarith : a - I.length < b - I.length) T.disjoint (by rw [hlen] at hb; linarith)
      have heA : I.before (I.left + a) = Piece.ofInterval I :=
        dite_eq_left (by dsimp [CakeInterval.length] at haI; linarith)
      refine ⟨y, ?_, ?_⟩
      · rw [support_prefixAt_cons]
        exact Or.inr hyb
      · rw [support_prefixAt_cons, heA, support_ofInterval]
        rintro (hyI | hyT)
        · obtain ⟨J, hJ, hyJ⟩ := T.prefix_subset _ hyb
          exact Set.disjoint_left.mp ((List.pairwise_cons.mp hd).1 J hJ) hyI hyJ
        · exact hya hyT

/-- Two interval representations describe the same geometric traversal. -/
def SameTraversal (P Q : Piece) : Prop :=
  P.length = Q.length ∧ ∀ t, (P.prefixAt t).support = (Q.prefixAt t).support

namespace SameTraversal

theorem refl (P : Piece) : SameTraversal P P := ⟨rfl, fun _ ↦ rfl⟩

theorem symm {P Q : Piece} (h : SameTraversal P Q) : SameTraversal Q P :=
  ⟨h.1.symm, fun t ↦ (h.2 t).symm⟩

theorem trans {P Q R : Piece} (h : SameTraversal P Q) (h' : SameTraversal Q R) :
    SameTraversal P R := ⟨h.1.trans h'.1, fun t ↦ (h.2 t).trans (h'.2 t)⟩

theorem support_eq {P Q : Piece} (h : SameTraversal P Q) : P.support = Q.support := by
  have ht := h.2 P.length
  rw [Piece.prefix_length, h.1, Piece.prefix_length] at ht
  exact ht

theorem append {P P' Q Q' : Piece} (hP : SameTraversal P P')
    (hQ : SameTraversal Q Q') (hd : Disjoint P.support Q.support)
    (hd' : Disjoint P'.support Q'.support) :
    SameTraversal (P.append Q hd) (P'.append Q' hd') := by
  refine ⟨by simp [hP.1, hQ.1], fun t ↦ ?_⟩
  simp only [support_prefix_append, hP.2, hQ.2, hP.1]

end SameTraversal

end Piece

/-- Splitting an interval preserves every traversal prefix, including endpoint 1. -/
theorem CakeInterval.sameTraversal_split (I : CakeInterval) (x : ℝ) :
    Piece.SameTraversal (Piece.ofInterval I) (I.splitCell x) := by
  by_cases hr : I.right ≤ x
  · simpa only [splitCell, before, after, dite_eq_left hr, Piece.append, Piece.empty,
      List.append_nil] using Piece.SameTraversal.refl (Piece.ofInterval I)
  by_cases hl : I.left < x
  · let L := I.leftCell x hl (lt_of_not_ge hr)
    let R := I.rightCell x hl (lt_of_not_ge hr)
    have he : (I.splitCell x).intervals = [L, R] := I.intervals_splitCell x hl _
    have hlen : (Piece.ofInterval I).length = (I.splitCell x).length := by
      simp [Piece.length, Piece.ofInterval, he, L, R, CakeInterval.length,
        leftCell, rightCell]
    refine ⟨hlen, fun t ↦ ?_⟩
    have hp : (Piece.ofInterval I).prefixAt t = I.before (I.left + t) := by
      cases hb : I.before (I.left + t)
      simp [Piece.prefixAt, Piece.prefixIntervals, Piece.ofInterval, hb]
    rw [hp]
    have hsp : ((I.splitCell x).prefixAt t).support =
        (L.before (L.left + t)).support ∪
          (R.before (R.left + (t - L.length))).support := by
      ext y
      simp [Piece.prefixAt, he, Piece.prefixIntervals, Piece.support]
      grind
    rw [hsp, I.support_before, L.support_before, R.support_before]
    have hi := I.ordered
    have hir := I.right_le_one
    have hx : x < I.right := lt_of_not_ge hr
    dsimp [L, R, leftCell, rightCell, CakeInterval.length]
    ext y
    simp only [CakeInterval.support, Set.mem_union]
    split_ifs <;> simp_all only [Set.mem_Icc, Set.mem_Ico, Set.mem_inter_iff, Set.mem_Iio] <;> grind
  · have hx : x ≤ I.left := le_of_not_gt hl
    simpa only [splitCell, before, after, dite_eq_right hr, dite_eq_right hl,
      dite_eq_left hx, Piece.append, Piece.empty, List.nil_append] using
      Piece.SameTraversal.refl (Piece.ofInterval I)

/-- Ordered subdivision of a component preserves the whole piece's traversal. -/
theorem RecordedState.sameTraversal_refinePiece (P : Piece) (I : CakeInterval) (x : ℝ) :
    P.SameTraversal (RecordedState.refinePiece P I x) := by
  classical
  obtain ⟨Is, hd⟩ := P
  induction Is with
  | nil => exact Piece.SameTraversal.refl _
  | cons J Js ih =>
    let T : Piece := ⟨Js, (List.pairwise_cons.mp hd).2⟩
    have hJT : Disjoint (Piece.ofInterval J).support T.support := by
      rw [Piece.support_ofInterval]
      exact Set.disjoint_left.mpr fun y hy ⟨K, hK, hyK⟩ ↦
        Set.disjoint_left.mp ((List.pairwise_cons.mp hd).1 K hK) hy hyK
    have ht := ih T.disjoint
    by_cases hJI : J = I
    · subst J
      have hd' : Disjoint (I.splitCell x).support
          (RecordedState.refinePiece T I x).support := by
        simpa using hJT
      have h := (I.sameTraversal_split x).append ht hJT hd'
      simpa [RecordedState.refinePiece, Piece.replaceInterval, Piece.append,
        Piece.ofInterval, T] using h
    · have hd' : Disjoint (Piece.ofInterval J).support
          (RecordedState.refinePiece T I x).support := by simpa using hJT
      have h := (Piece.SameTraversal.refl (Piece.ofInterval J)).append ht hJT hd'
      simpa [RecordedState.refinePiece, Piece.replaceInterval, Piece.append,
        Piece.ofInterval, hJI, T] using h

namespace RecordedState

/-- Old pieces admit current representations with exactly the same traversal. -/
def TraversalRefines {n : ℕ} (s s' : RecordedState n) : Prop :=
  ∀ P, s.Compatible P → ∃ Q, s'.Compatible Q ∧ P.SameTraversal Q

theorem traversalRefines_refl {n : ℕ} (s : RecordedState n) : s.TraversalRefines s :=
  fun P hP ↦ ⟨P, hP, Piece.SameTraversal.refl P⟩

theorem TraversalRefines.refines {n : ℕ} {s s' : RecordedState n}
    (h : s.TraversalRefines s') : s.Refines s' := by
  intro P hP
  obtain ⟨Q, hQ, he⟩ := h P hP
  exact ⟨Q, hQ, he.support_eq.symm⟩

theorem TraversalRefines.trans {n : ℕ} {s s' s'' : RecordedState n}
    (h : s.TraversalRefines s') (h' : s'.TraversalRefines s'') : s.TraversalRefines s'' := by
  intro P hP
  obtain ⟨Q, hQ, he⟩ := h P hP
  obtain ⟨R, hR, he'⟩ := h' Q hQ
  exact ⟨R, hR, he.trans he'⟩

theorem traversalRefines_split {n : ℕ} (s : RecordedState n) (I : CakeInterval) (x : ℝ)
    (hl : I.left < x) (hr : x < I.right) (a : Fin n → ℝ) :
    s.TraversalRefines (s.split I x hl hr a) := by
  intro P hP
  exact ⟨refinePiece P I x, compatible_split s hP I x hl hr a,
    sameTraversal_refinePiece P I x⟩

/-- Select a current representation without changing the specified traversal.
The fallback makes this internal operation total on arbitrary answer branches. -/
def representAlong {n : ℕ} (s : RecordedState n) (P : Piece) : Piece :=
  if h : ∃ Q, s.Compatible Q ∧ P.SameTraversal Q then h.choose else Piece.empty

theorem representAlong_spec {n : ℕ} {s : RecordedState n} {P : Piece}
    (h : ∃ Q, s.Compatible Q ∧ P.SameTraversal Q) :
    s.Compatible (s.representAlong P) ∧ P.SameTraversal (s.representAlong P) := by
  simp only [representAlong, dite_eq_left h]
  exact h.choose_spec

end RecordedState
end CakeCuttingPsomas
