module

public import CakeCuttingPsomas.Traversal

-- This project does not prescribe mathlib's copyright/license header format.
set_option linter.style.header false

/-! # Protocols that maintain recorded values

The Eval-and-subtraction implementation of Section 1.3's recorded-value convention.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas

namespace RWProtocol

/-- Query an interval's value for a list of agents. Unrequested entries are zero. -/
def evalAgents {n : ℕ} (a b : ℝ) : List (Fin n) → RWProtocol n (Fin n → ℝ)
  | [] => .done (fun _ ↦ 0)
  | i :: is => .ask (.eval i a b) (fun answer ↦
      (evalAgents a b is).map (fun values ↦ Function.update values i answer))

/-- Interval evaluations cost exactly one query per listed agent. -/
theorem evalAgents_runs {n : ℕ} (v : Fin n → Valuation) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (is : List (Fin n)) :
    ∃ values, (evalAgents a b is).Runs v values is.length ∧
      ∀ i ∈ is, values i = (v i).value (Set.Icc a b) := by
  induction is with
  | nil => exact ⟨_, .done _, by simp⟩
  | cons i is ih =>
    obtain ⟨values, hrun, hvalues⟩ := ih
    refine ⟨Function.update values i ((v i).value (Set.Icc a b)),
      .ask ⟨ha, hab, hb, rfl⟩ (hrun.map _), ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · simp
    · by_cases hji : j = i
      · subst j; simp
      · simpa [hji] using hvalues j hj

end RWProtocol

namespace RecordedState

/-- Insert a cut into a recorded cell. A boundary or an out-of-cell coordinate
leaves the records unchanged. Only an interior point triggers Eval queries. -/
def recordCut {n : ℕ} (s : RecordedState n) (I : CakeInterval) (x : ℝ) :
    RWProtocol n (RecordedState n) :=
  if h : I.left < x ∧ x < I.right then
    (RWProtocol.evalAgents I.left x (List.finRange n)).map
      (fun a ↦ s.split I x h.1 h.2 a)
  else .done s

/-- Interior recording additionally preserves representations of all old pieces. -/
theorem recordCut_runs_interior {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) (I : CakeInterval) (hI : I ∈ s.partition.intervals) (x : ℝ)
    (hl : I.left < x) (hr : x < I.right) :
    ∃ s', (s.recordCut I x).Runs v s' n ∧ s'.Correct v ∧
      ∀ P, s.Compatible P → s'.Compatible (refinePiece P I x) := by
  obtain ⟨a, ha, hva⟩ := RWProtocol.evalAgents_runs v I.left x I.left_nonneg hl.le
    (hr.le.trans I.right_le_one) (List.finRange n)
  refine ⟨s.split I x hl hr a, ?_, correct_split hs I hI x hl hr a ?_, ?_⟩
  · simpa [recordCut, hl, hr] using ha.map (fun a ↦ s.split I x hl hr a)
  · intro i
    exact hva i (List.mem_finRange i)
  · intro P hP
    exact compatible_split s hP I x hl hr a

/-- Section 1.3's recording convention carries the representation invariant
needed by subroutine and recursive calls: old pieces survive, and both new
fragments use recorded cells. -/
theorem recordCut_runs_spec {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) (I : CakeInterval) (hI : I ∈ s.partition.intervals) (x : ℝ) :
    ∃ s' count, (s.recordCut I x).Runs v s' count ∧ s'.Correct v ∧ count ≤ n ∧
      s.Refines s' ∧ s'.Compatible (I.before x) ∧ s'.Compatible (I.after x) ∧
      (∀ J ∈ s.partition.intervals, J ≠ I → J ∈ s'.partition.intervals) ∧
      s.TraversalRefines s' := by
  by_cases h : I.left < x ∧ x < I.right
  · obtain ⟨a, ha, hva⟩ := RWProtocol.evalAgents_runs v I.left x I.left_nonneg h.1.le
      (h.2.le.trans I.right_le_one) (List.finRange n)
    have hfrag := compatible_split_fragments s I hI x h.1 h.2 a
    refine ⟨s.split I x h.1 h.2 a, n, ?_, correct_split hs I hI x h.1 h.2 a ?_,
      le_rfl, refines_split s I x h.1 h.2 a, hfrag.1, hfrag.2, ?_,
      traversalRefines_split s I x h.1 h.2 a⟩
    · simpa [recordCut, h] using ha.map (fun a ↦ s.split I x h.1 h.2 a)
    · intro i
      exact hva i (List.mem_finRange i)
    · intro J hJ hne
      exact mem_split_of_ne s I J hJ hne x h.1 h.2 a
  · have hwhole : s.Compatible (Piece.ofInterval I) := by
      intro J hJ
      have heq : J = I := List.mem_singleton.mp hJ
      subst J
      exact hI
    have hempty : s.Compatible Piece.empty := by intro J hJ; cases hJ
    have hfrag : s.Compatible (I.before x) ∧ s.Compatible (I.after x) := by
      by_cases hr : I.right ≤ x
      · simpa only [CakeInterval.before, CakeInterval.after, dite_eq_left hr] using
          And.intro hwhole hempty
      · have hl : x ≤ I.left := by
          by_contra hle
          exact h ⟨lt_of_not_ge hle, lt_of_not_ge hr⟩
        simpa only [CakeInterval.before, CakeInterval.after, dite_eq_right hr,
          dite_eq_right (not_lt.mpr hl), dite_eq_left hl] using And.intro hempty hwhole
    refine ⟨s, 0, ?_, hs, Nat.zero_le _, refines_refl s, hfrag.1, hfrag.2,
      (fun _ h _ ↦ h), traversalRefines_refl s⟩
    simp only [recordCut, dite_eq_right h]
    exact .done s

/-- Recording a new cut preserves soundness and costs at most one Eval per
participating agent, as asserted in Section 1.3. No positivity is assumed. -/
theorem recordCut_runs {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) (I : CakeInterval) (hI : I ∈ s.partition.intervals) (x : ℝ) :
    ∃ s' count, (s.recordCut I x).Runs v s' count ∧ s'.Correct v ∧ count ≤ n := by
  obtain ⟨s', count, hrun, hs', hc, _⟩ := recordCut_runs_spec hs I hI x
  exact ⟨s', count, hrun, hs', hc⟩

end RecordedState
end CakeCuttingPsomas
