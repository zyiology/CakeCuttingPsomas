module

public import CakeCuttingPsomas.RecordedPreparation
public import CakeCuttingPsomas.DominateChoice
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Powerset

set_option linter.style.header false

/-! # Recorded-value searches for Dominate

Section 3, `alg:dominate`, group test and choice step. These finite searches use
only geometry and the recorded table. Real comparisons are free internal
computation in the abstract Robertson–Webb model.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.DominateSearch

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Scan a finite enumeration for the first satisfying candidate. Only the
enumeration order and exact real comparisons are noncomputable. -/
def select {α : Type} (candidates : Finset α) (p : α → Prop) : Option α :=
  candidates.toList.find? (fun x ↦ decide (p x))

theorem select_some {α : Type} {candidates : Finset α} {p : α → Prop} {x : α}
    (h : select candidates p = some x) : x ∈ candidates ∧ p x := by
  have hp : decide (p x) = true :=
    List.find?_some (p := fun y ↦ decide (p y)) h
  exact ⟨Finset.mem_toList.mp (List.mem_of_find?_eq_some h), of_decide_eq_true hp⟩

theorem select_none {α : Type} {candidates : Finset α} {p : α → Prop}
    (h : select candidates p = none) : ∀ x ∈ candidates, ¬ p x := by
  intro x hx hp
  exact (List.find?_eq_none.mp h) x (Finset.mem_toList.mpr hx)
    (by simpa only [decide_eq_true_eq] using hp)

/-- The domination inequality evaluated from current records. -/
def dominates {n : ℕ} {C : Piece} (s : RecordedState n) (X : Allocation n C)
    (i j : Fin n) : Prop :=
  s.supportValue i (X.bundle j).support + s.supportValue i X.residue ≤
    s.supportValue i (X.bundle i).support

theorem dominates_iff {n : ℕ} {C : Piece} {s : RecordedState n}
    {X : Allocation n C} {v : Fin n → Valuation} (hs : s.Correct v)
    (hX : ∀ j, s.Represents (X.bundle j).support) (hR : s.Represents X.residue)
    (i j : Fin n) : dominates s X i j ↔ X.Dominates v i j := by
  simp only [dominates, Allocation.Dominates, s.supportValue_eq hs (hX j),
    s.supportValue_eq hs hR, s.supportValue_eq hs (hX i)]

/-- All nonempty proper groups are considered; every outsider must dominate
every member, exactly as in the paper's definition. -/
def groupTest {n : ℕ} {C : Piece} (s : RecordedState n) (X : Allocation n C)
    (E : Finset (Fin n)) : Prop :=
  E.Nonempty ∧ E ≠ Finset.univ ∧ ∀ i, i ∉ E → ∀ j ∈ E, dominates s X i j

theorem groupTest_iff {n : ℕ} {C : Piece} {s : RecordedState n}
    {X : Allocation n C} {v : Fin n → Valuation} (hs : s.Correct v)
    (hX : ∀ j, s.Represents (X.bundle j).support) (hR : s.Represents X.residue)
    (E : Finset (Fin n)) : groupTest s X E ↔ X.DominatedGroup v (↑E) := by
  classical
  simp only [groupTest, Allocation.DominatedGroup, Finset.coe_nonempty,
    Finset.mem_coe, dominates_iff hs hX hR]
  have heq : (↑E : Set (Fin n)) = Set.univ ↔ E = Finset.univ := by
    exact_mod_cast (Iff.rfl : E = Finset.univ ↔ E = Finset.univ)
  simp only [ne_eq, heq]

/-- Section 3, `alg:dominate`, Line `dominate:line:test`: a zero-query search. -/
def group {n : ℕ} {C : Piece} (s : RecordedState n) (X : Allocation n C) :
    Option (Finset (Fin n)) := select Finset.univ (groupTest s X)

theorem group_some {n : ℕ} {C : Piece} {s : RecordedState n}
    {X : Allocation n C} {v : Fin n → Valuation} (hs : s.Correct v)
    (hX : ∀ j, s.Represents (X.bundle j).support) (hR : s.Represents X.residue)
    {E : Finset (Fin n)} (h : group s X = some E) : X.DominatedGroup v (↑E) :=
  (groupTest_iff hs hX hR E).mp (select_some h).2

/-- Section 3's group test is complete also for the set-valued statement used
by the choice lemma. -/
theorem group_none {n : ℕ} {C : Piece} {s : RecordedState n}
    {X : Allocation n C} {v : Fin n → Valuation} (hs : s.Correct v)
    (hX : ∀ j, s.Represents (X.bundle j).support) (hR : s.Represents X.residue)
    (h : group s X = none) : ∀ E : Set (Fin n), ¬ X.DominatedGroup v E := by
  classical
  intro E hE
  have ht : groupTest s X E.toFinset :=
    (groupTest_iff hs hX hR E.toFinset).mpr (by simpa using hE)
  exact select_none h E.toFinset (Finset.mem_univ _) ht

/-- The choice space is finite, including the exponent. -/
abbrev Candidate (n : ℕ) := Fin (n + 2) × Fin n × Fin n × Equiv.Perm (Fin n)

/-- (S1)--(S3) read solely from the inherited record table. -/
def choiceTest {n : ℕ} {C R : Piece} (s : RecordedState n)
    (X : Allocation n C) (Y : Allocation n R) (q : Candidate n) : Prop :=
  2 ≤ q.1.val ∧ q.1.val ≤ n + 1 ∧ q.2.1 ≠ q.2.2.1 ∧
    ¬ dominates s X q.2.1 q.2.2.1 ∧
    (∀ k, s.supportValue k (Y.bundle k).support -
      DominateChoice.scale n q.1.val * s.supportValue k Y.residue ≤
        s.supportValue k (Y.bundle (q.2.2.2 k)).support) ∧
    s.supportValue q.2.1 (Y.bundle (q.2.2.2 q.2.2.1)).support ≤
      s.supportValue q.2.1 (Y.bundle q.2.1).support -
        4 * (n : ℝ) ^ 2 * DominateChoice.scale n q.1.val *
          s.supportValue q.2.1 Y.residue

theorem choiceTest_iff {n : ℕ} {C R : Piece} {s : RecordedState n}
    {X : Allocation n C} {Y : Allocation n R} {v : Fin n → Valuation}
    (hs : s.Correct v) (hX : ∀ j, s.Represents (X.bundle j).support)
    (hXR : s.Represents X.residue) (hY : ∀ j, s.Represents (Y.bundle j).support)
    (hYR : s.Represents Y.residue) (q : Candidate n) :
    choiceTest s X Y q ↔ DominateChoice.Spec X Y v q.1.val q.2.1 q.2.2.1 q.2.2.2 := by
  simp only [choiceTest, dominates_iff hs hX hXR,
    s.supportValue_eq hs (hY _), s.supportValue_eq hs hYR]
  exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
    fun h ↦ ⟨h.exponent_lower, h.exponent_upper, h.distinct, h.not_dominates,
      h.small_loss, h.large_gap⟩⟩

/-- Section 3, `alg:dominate`, Line `dominate:line:choose`: a zero-query search
over all allowed scales, agents, and permutations. -/
def choice {n : ℕ} {C R : Piece} (s : RecordedState n)
    (X : Allocation n C) (Y : Allocation n R) : Option (Candidate n) :=
  select Finset.univ (choiceTest s X Y)

/-- Section 3's `lem:alpha pi exist for dominate`: any mathematical choice has
a candidate in the finite recorded search, with exactly the same specification. -/
theorem choice_available {n : ℕ} {C R : Piece} {s : RecordedState n}
    {X : Allocation n C} {Y : Allocation n R} {v : Fin n → Valuation}
    (hs : s.Correct v) (hX : ∀ j, s.Represents (X.bundle j).support)
    (hXR : s.Represents X.residue) (hY : ∀ j, s.Represents (Y.bundle j).support)
    (hYR : s.Represents Y.residue)
    (hex : ∃ t i j π, DominateChoice.Spec X Y v t i j π) :
    ∃ q, choice s X Y = some q ∧
      DominateChoice.Spec X Y v q.1.val q.2.1 q.2.2.1 q.2.2.2 := by
  classical
  have hsome : choice s X Y ≠ none := by
    intro hnone
    obtain ⟨t, i, j, π, ht⟩ := hex
    let q : Candidate n := (⟨t, by have := ht.exponent_upper; omega⟩, i, j, π)
    exact select_none hnone q (Finset.mem_univ _)
      ((choiceTest_iff hs hX hXR hY hYR q).mpr ht)
  cases h : choice s X Y with
  | none => exact False.elim (hsome h)
  | some q => exact ⟨q, rfl, (choiceTest_iff hs hX hXR hY hYR q).mp (select_some h).2⟩

end CakeCuttingPsomas.DominateSearch
