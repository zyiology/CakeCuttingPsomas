module

public import CakeCuttingPsomas.Candidate
public import CakeCuttingPsomas.ApproximateSuffix
public import Mathlib.Order.Extension.Well
public import Mathlib.Data.Fintype.Sort

set_option linter.style.header false

/-! # Terminal suffix allocations contain candidates

Section 5, proof of `lem:permute`, “X contains a candidate”. A topological
agent order and its induced input-label order identify a candidate contained
in the terminal allocation. This construction is proof-only and uses no queries.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas

/-- Section 5, `lem:permute`, “X contains a candidate”: an acyclic finite
relation admits an order in which every edge goes from earlier to later. -/
theorem exists_topological_order {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, ¬ Relation.TransGen R i i) :
    ∃ agents : Equiv.Perm (Fin n), ∀ s r, R (agents s) (agents r) → s < r := by
  let : Std.Irrefl (Relation.TransGen R) := ⟨hR⟩
  have hw := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen R)
  let order := @WellFounded.wellOrderExtension (Fin n) (Relation.TransGen R) hw
  let e := @monoEquivOfFin (Fin n) _ order n (by simp)
  refine ⟨e.toEquiv, fun s r h ↦ ?_⟩
  apply (@OrderIso.lt_iff_lt (Fin n) (Fin n) _ order.toPreorder e s r).mp
  exact Prod.Lex.left _ _ (WellFounded.rank_lt_of_rel (Relation.TransGen.single h))

namespace EnvyCycle.State

variable {n : ℕ} {P : Fin n → Piece} {d : (j : Fin n) → CellPartition (P j)}
    {v : Fin n → Valuation} {X : State d}

/-- Section 5, `lem:permute`, “X contains a candidate”: for a topological
agent order and the induced label order, every candidate lies in the terminal
suffix allocation, bundle by bundle. -/
theorem Terminal.contains_candidate (ht : X.Terminal v)
    (agents : Equiv.Perm (Fin n))
    (ho : ∀ s r, X.Edge v (agents s) (agents r) → s < r)
    {Y : Fin n → Piece}
    (hY : IsCandidate (v ∘ agents) (fun r ↦ P (X.assignment (agents r))) Y) :
    ∀ r, (Y r).support ⊆ (X.bundle (agents r)).support := by
  have hall : ∀ k : ℕ, ∀ r : Fin n, r.val < k →
      (Y r).support ⊆ (X.bundle (agents r)).support := by
    intro k
    induction k with
    | zero => intro r hr; omega
    | succ k ih =>
      intro r hr
      by_cases hw : (X.bundle (agents r)).support = (P (X.assignment (agents r))).support
      · rw [hw]
        obtain ⟨a, _, he⟩ := hY.suffix r
        rw [he]
        exact Piece.suffix_subset _ _
      · obtain ⟨i, hi⟩ := ht.2 (agents r) hw
        let s := agents.symm i
        have hs : agents s = i := agents.apply_symm_apply i
        have hsr : s < r := ho s r (hs ▸ hi)
        have hind := ih s (by simp only [Fin.lt_def] at hsr; omega)
        have hv : (v (agents s)).value (Y r).support <
            (v (agents s)).value (X.bundle (agents r)).support := by
          calc
            _ ≤ (v (agents s)).value (Y s).support := hY.caps s r hsr
            _ ≤ (v (agents s)).value (X.bundle (agents s)).support :=
              (v (agents s)).value_mono (Y s).measurableSet_support
                (X.bundle (agents s)).measurableSet_support hind
                (X.bundle (agents s)).support_subset_unit
            _ < _ := by simpa only [Edge, hs] using hi
        rcases (hY.suffix r).support_comparable (X.suffix (agents r)) with h | h
        · exact h
        · exact False.elim (not_le_of_gt hv
            ((v (agents s)).value_mono (X.bundle (agents r)).measurableSet_support
              (Y r).measurableSet_support h (Y r).support_subset_unit))
  exact fun r ↦ hall n r r.isLt

end EnvyCycle.State

namespace EnvyCycle

/-- Section 5, `lem:permute`, “X contains a candidate”: for every positive δ,
some fixed-order candidate has a δ-envy-free suffix extension with the same
input-label assignment. The orders and candidate may depend on δ. -/
theorem exists_candidate_delta_extension {n : ℕ} (v : Fin n → Valuation) (C : Piece)
    (P : Fin n → Piece)
    (hdis : ∀ j k, j ≠ k → Disjoint (P j).support (P k).support)
    (hcover : (⋃ j, (P j).support) = C.support) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (agents pieces : Equiv.Perm (Fin n)) (Y : Fin n → Piece) (A : Allocation n C),
      IsCandidate (v ∘ agents) (P ∘ pieces) Y ∧
      (∀ r, (A.bundle (agents r)).IsSuffix (P (pieces r))) ∧
      (∀ r, (Y r).support ⊆ (A.bundle (agents r)).support) ∧
      (∀ i j, (v i).value (A.bundle j).support ≤ (v i).value (A.bundle i).support + δ) := by
  obtain ⟨d, X, _, he, ht⟩ := exists_terminal_state v P δ hδ
  obtain ⟨agents, ho⟩ := exists_topological_order (X.Edge v) ht.1
  let pieces := agents.trans X.assignment
  let Y := CandidateConstruction.candidate (v ∘ agents) (P ∘ pieces)
  have hY := CandidateConstruction.candidate_spec (v ∘ agents) (P ∘ pieces)
  have hc (j : Fin n) : (P j).support ⊆ C.support := by
    rw [← hcover]
    exact Set.subset_iUnion (fun k ↦ (P k).support) j
  exact ⟨agents, pieces, Y, X.allocation C hc hdis, hY,
    fun r ↦ X.suffix (agents r), ht.contains_candidate agents ho hY, he⟩

end EnvyCycle
end CakeCuttingPsomas
