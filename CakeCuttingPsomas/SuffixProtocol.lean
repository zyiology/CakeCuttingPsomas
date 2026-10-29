module

public import CakeCuttingPsomas.PrefixProtocol

set_option linter.style.header false

/-! # Recorded suffix trims

Section 5, `permute:trim`: use current cells internally, retaining the original
piece's traversal positions and exact `IsSuffix` representation externally.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.RecordedState

/-- Section 5, `permute:trim`: the target is computed entirely from records.
The returned position refers to the original piece, even after subdivision. -/
def capTrim {n : ℕ} (s : RecordedState n) (i : Fin n) (P : Piece) (cap : ℝ) :
    RWProtocol n (ℝ × RecordedState n) :=
  let Q := s.representAlong P
  s.prefixCut i Q (max 0 (s.pieceValue i Q - cap))

/-- Section 5, the guard at `permute:trim`: a satisfied cap makes no queries,
including on empty pieces and pieces of value zero. -/
theorem capTrim_of_value_le {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) (i : Fin n) (P : Piece)
    (hP : ∃ Q, s.Compatible Q ∧ P.SameTraversal Q) (cap : ℝ)
    (hc : (v i).value P.support ≤ cap) : s.capTrim i P cap = .done (0, s) := by
  obtain ⟨hQ, he⟩ := representAlong_spec hP
  have ht : max 0 (s.pieceValue i (s.representAlong P) - cap) = 0 := by
    rw [pieceValue_eq hs hQ, ← he.support_eq]
    exact max_eq_left (sub_nonpos.mpr hc)
  change s.prefixCut i (s.representAlong P)
    (max 0 (s.pieceValue i (s.representAlong P) - cap)) = _
  rw [ht]
  unfold prefixCut
  cases (s.representAlong P).intervals <;> simp [prefixCutAux]

/-- Section 5, `permute:trim` and `eq:permute-caps`: a recorded trim costs at
most n+1 queries and returns an exact suffix of the original piece. Its remaining
traversal is represented in the new records, so this guarantee can be iterated.
The traversal hypothesis is explicit; support representability alone is weaker. -/
theorem capTrim_runs {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) (i : Fin n) (P : Piece)
    (hP : ∃ Q, s.Compatible Q ∧ P.SameTraversal Q) (cap : ℝ) (hc : 0 ≤ cap) :
    ∃ a s' count, (s.capTrim i P cap).Runs v (a, s') count ∧ count ≤ n + 1 ∧
      s'.Correct v ∧ s.TraversalRefines s' ∧ a ∈ Set.Icc 0 P.length ∧
      (v i).IsCapTrim P cap (P.suffixAt a) ∧
      (P.suffixAt a).IsSuffix P ∧
      s'.Represents (P.prefixAt a).support ∧
      (∃ Q, s'.Compatible Q ∧ (P.suffixAt a).SameTraversal Q) := by
  obtain ⟨hQ, he⟩ := representAlong_spec hP
  let Q := s.representAlong P
  change P.SameTraversal Q at he
  have hv : s.pieceValue i Q = (v i).value P.support := by
    rw [pieceValue_eq hs hQ, ← he.support_eq]
  have hn := (v i).value_nonneg P.measurableSet_support P.support_subset_unit
  obtain ⟨a, s', count, hr, hcount, hs', href, ha, hval, hmin, hp, hq, _hpre⟩ :=
    prefixCut_runs_spec hs i Q hQ (max 0 (s.pieceValue i Q - cap))
      (le_max_left _ _) (by rw [hv, ← he.support_eq]; exact max_le hn (by linarith))
  have haP : a ∈ Set.Icc 0 P.length := he.1.symm ▸ ha
  have htrim : (v i).IsCapTrim P cap (P.suffixAt a) := by
    refine ⟨hc, a, haP, rfl, ?_, ?_⟩
    · simpa only [hv, ← he.2 a] using hval
    · intro b hb hvalue
      apply hmin b (he.1 ▸ hb)
      simpa only [← he.2 b, hv] using hvalue
  refine ⟨a, s', count, hr, hcount, hs', href, haP, htrim,
    P.suffix_isSuffix haP, ?_, Q.suffixAt a, hq, he.suffixAt haP⟩
  simpa only [← he.2 a] using hp

end CakeCuttingPsomas.RecordedState
