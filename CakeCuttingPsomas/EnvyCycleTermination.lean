module

public import CakeCuttingPsomas.EnvyCycle
public import Mathlib.Order.WellFounded

set_option linter.style.header false

/-! # Finite termination of the proof-only envy-cycle process

Section 5, proof of `lem:permute`: finitely many cells can be added, and between
additions there are only finitely many assignments of the fixed labelled suffixes.
The real-valued potential is used only to rank this finite set of assignments.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.EnvyCycle.State

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {P : Fin n → Piece} {d : (j : Fin n) → CellPartition (P j)}

/-- The cells preceding a label's current suffix have not yet been allocated. -/
def remaining (X : State d) : ℕ :=
  ∑ j, ((d j).boundaries.filter (· < X.cut j)).card

/-- The paper's potential, evaluated at every possible assignment of fixed suffixes. -/
def assignmentPotential (v : Fin n → Valuation) (cut : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, (v i).value ((P (σ i)).suffixAt (cut (σ i))).support

/-- Number of assignments strictly better than the current one, with ties retained.
This is a natural-number rank on a finite set, rather than a real-valued measure. -/
def rank (v : Fin n → Valuation) (X : State d) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) ↦
    assignmentPotential (P := P) v X.cut X.assignment < assignmentPotential (P := P) v X.cut σ).card

/-- At fixed boundaries there are only n! assignments, even when values coincide. -/
theorem rank_le_factorial (v : Fin n → Valuation) (X : State d) :
    rank v X ≤ Nat.factorial n := by
  calc
    rank v X ≤ (Finset.univ : Finset (Equiv.Perm (Fin n))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Nat.factorial n := by simp [Fintype.card_perm]

/-- Section 5, `lem:permute`: a rotation strictly improves the sum of own values. -/
theorem rotate_potential_lt (v : Fin n → Valuation) (X : State d) (c : X.Cycle v) :
    assignmentPotential (P := P) v X.cut X.assignment <
      assignmentPotential (P := P) v (X.rotate c).cut (X.rotate c).assignment := by
  apply Finset.sum_lt_sum
  · intro i _
    exact X.rotate_own_le c i
  · obtain ⟨i, hi⟩ := c.improves
    exact ⟨i, Finset.mem_univ _, hi⟩

/-- Section 5, `lem:permute`: at fixed boundaries, a rotation decreases finite rank. -/
theorem rotate_rank_lt (v : Fin n → Valuation) (X : State d) (c : X.Cycle v) :
    rank v (X.rotate c) < rank v X := by
  have hp := rotate_potential_lt v X c
  unfold rank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact hp.trans hσ
  · intro he
    have hm : (X.rotate c).assignment ∈
        Finset.univ.filter (fun σ ↦ assignmentPotential (P := P) v X.cut X.assignment <
          assignmentPotential (P := P) v X.cut σ) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
    rw [← he] at hm
    exact (lt_irrefl _ (Finset.mem_filter.mp hm).2)

/-- A preceding-cell enlargement strictly reduces the number of unallocated cells. -/
theorem enlarge_remaining_lt (X : State d) (i : Fin n)
    (a : (d (X.assignment i)).Index) (ha : (d _).finish a = X.cut (X.assignment i)) :
    (X.enlarge i a).remaining < X.remaining := by
  have hp : a.val < X.cut (X.assignment i) := ha ▸ (d _).finish_spec a |>.1
  apply Finset.sum_lt_sum
  · intro j _
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hx, hlt⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr ⟨hx, ?_⟩
    by_cases hj : j = X.assignment i
    · subst j
      simp only [enlarge, Function.update_self] at hlt
      exact hlt.trans hp
    · simpa only [enlarge, Function.update_of_ne hj] using hlt
  · refine ⟨X.assignment i, Finset.mem_univ _, ?_⟩
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro x hx
      obtain ⟨hx, hlt⟩ := Finset.mem_filter.mp hx
      simp only [enlarge, Function.update_self] at hlt
      exact Finset.mem_filter.mpr ⟨hx, hlt.trans hp⟩
    · intro he
      have hm : a.val ∈ (d (X.assignment i)).boundaries.filter (· < X.cut (X.assignment i)) :=
        Finset.mem_filter.mpr ⟨a.property, hp⟩
      rw [← he] at hm
      have := (Finset.mem_filter.mp hm).2
      simp only [enlarge, Function.update_self] at this
      exact lt_irrefl _ this

/-- Section 5, `lem:permute`: every step decreases the lexicographic pair of
unallocated-cell count and finite assignment rank. -/
theorem step_decreases {v : Fin n → Valuation} {X Y : State d} (h : Step v X Y) :
    Prod.Lex (· < ·) (· < ·) (Y.remaining, rank v Y) (X.remaining, rank v X) := by
  cases h with
  | rotate c => exact Prod.Lex.right _ (rotate_rank_lt v _ c)
  | enlarge _ i _ a ha => exact Prod.Lex.left _ _ (enlarge_remaining_lt _ i a ha)

/-- Section 5, `lem:permute`: the process terminates; strict real-potential
increase alone is not used as a well-foundedness argument. -/
theorem wellFounded (v : Fin n → Valuation) :
    WellFounded (fun Y X : State d ↦ Step v X Y) := by
  have hw : WellFounded (Prod.Lex (α := ℕ) (β := ℕ) (· < ·) (· < ·)) :=
    (Prod.lex (measure id) (measure id)).wf
  exact Subrelation.wf (fun h ↦ step_decreases h)
    (hw.onFun (f := fun X : State d ↦ (X.remaining, rank v X)))

/-- δ-envy-freeness is preserved along every finite execution of the process. -/
theorem reachable_deltaEnvyFree {v : Fin n → Valuation} {δ : ℝ}
    (hf : ∀ j i (a : (d j).Index), (v i).value ((d j).piece a).support ≤ δ)
    {X Y : State d} (hX : X.DeltaEnvyFree v δ)
    (h : Relation.ReflTransGen (Step v) X Y) : Y.DeltaEnvyFree v δ := by
  induction h with
  | refl => exact hX
  | tail _ hs ih =>
    cases hs with
    | rotate c => exact rotate_deltaEnvyFree _ ih c
    | enlarge _ i hu a ha => exact enlarge_deltaEnvyFree _ ih hf i hu a ha

/-- Section 5, `lem:permute`: every state reaches a terminal state in finitely
many priority-respecting rotations and enlargements. -/
theorem exists_terminal_reachable (v : Fin n → Valuation) (X : State d) :
    ∃ Y, Relation.ReflTransGen (Step v) X Y ∧ Y.Terminal v := by
  induction X using (wellFounded (d := d) v).induction with
  | h X ih =>
    by_cases ht : X.Terminal v
    · exact ⟨X, .refl, ht⟩
    · have hs : ∃ Y, Step v X Y := not_not.mp (mt (X.terminal_iff_no_step v).mpr ht)
      obtain ⟨Y, hY⟩ := hs
      obtain ⟨Z, hZ, htZ⟩ := ih Y hY
      exact ⟨Z, Relation.ReflTransGen.head hY hZ, htZ⟩

/-- Section 5, `lem:permute`, “Creating a δ-envy-free suffix allocation”:
fine labelled cells yield a reachable terminal δ-envy-free suffix state. -/
theorem exists_terminal (v : Fin n → Valuation) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : ∀ j i (a : (d j).Index), (v i).value ((d j).piece a).support ≤ δ) :
    ∃ X : State d, Relation.ReflTransGen (Step v) (initial (d := d)) X ∧
      X.DeltaEnvyFree v δ ∧ X.Terminal v := by
  obtain ⟨X, hX, ht⟩ := exists_terminal_reachable v (initial (d := d))
  exact ⟨X, hX, reachable_deltaEnvyFree hf (initial_deltaEnvyFree hδ) hX, ht⟩

/-- Section 5, `lem:permute`: a terminal state on a nonempty agent set has a
whole-piece recipient, since an acyclic finite envy graph has a source. -/
theorem Terminal.exists_whole {v : Fin n → Valuation} {X : State d}
    (h : X.Terminal v) (hn : 0 < n) :
    ∃ i, (X.bundle i).support = (P (X.assignment i)).support := by
  let : Std.Irrefl (Relation.TransGen (X.Edge v)) := ⟨h.1⟩
  have hw := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen (X.Edge v))
  obtain ⟨i, _, hi⟩ := hw.has_min Set.univ ⟨⟨0, hn⟩, Set.mem_univ _⟩
  refine ⟨i, ?_⟩
  by_contra hnw
  obtain ⟨j, hj⟩ := h.2 i hnw
  exact hi j (Set.mem_univ _) (Relation.TransGen.single hj)

end CakeCuttingPsomas.EnvyCycle.State
