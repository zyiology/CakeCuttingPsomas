module

public import CakeCuttingPsomas.EnvyCycleTermination

set_option linter.style.header false

/-! # Terminal approximate envy-free suffix allocations

Section 5, proof of `lem:permute`, “Creating a δ-envy-free suffix allocation”.
Fine cells and the terminating envy-cycle process are used only in the proof;
no recorded state or Robertson–Webb queries are involved.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.EnvyCycle

/-- Section 5, `lem:permute`: for every positive δ, the empty labelled suffix
state reaches a terminal δ-envy-free state. No normalization, positive-value,
nonempty-piece, or nonempty-agent assumptions are needed. -/
theorem exists_terminal_state {n : ℕ} (v : Fin n → Valuation) (P : Fin n → Piece)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (d : (j : Fin n) → CellPartition (P j)) (X : State d),
      Relation.ReflTransGen (State.Step v) (State.initial (d := d)) X ∧
      X.DeltaEnvyFree v δ ∧ X.Terminal v := by
  obtain ⟨d, hd⟩ := FineCells.exists_partitions v P δ hδ
  obtain ⟨X, hr, he, ht⟩ := State.exists_terminal v hδ.le hd
  exact ⟨d, X, hr, he, ht⟩

/-- Section 5, `lem:permute`, “Creating a δ-envy-free suffix allocation”:
disjoint labelled inputs admit a terminal δ-envy-free partial suffix allocation.
Its envy graph is acyclic, and each proper suffix has an incoming strict envy
edge. Empty input labels remain distinct through the assignment permutation. -/
theorem exists_terminal_allocation {n : ℕ} (v : Fin n → Valuation) (C : Piece)
    (P : Fin n → Piece)
    (hdis : ∀ j k, j ≠ k → Disjoint (P j).support (P k).support)
    (hcover : (⋃ j, (P j).support) = C.support) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (A : Allocation n C) (σ : Equiv.Perm (Fin n)),
      (∀ i, (A.bundle i).IsSuffix (P (σ i))) ∧
      (∀ i j, (v i).value (A.bundle j).support ≤ (v i).value (A.bundle i).support + δ) ∧
      (∀ i, ¬ Relation.TransGen
        (fun j k ↦ (v j).value (A.bundle j).support < (v j).value (A.bundle k).support) i i) ∧
      (∀ i, (A.bundle i).support ≠ (P (σ i)).support →
        ∃ j, (v j).value (A.bundle j).support < (v j).value (A.bundle i).support) := by
  obtain ⟨d, X, _, he, ht⟩ := exists_terminal_state v P δ hδ
  have hc (j : Fin n) : (P j).support ⊆ C.support := by
    rw [← hcover]
    exact Set.subset_iUnion (fun k ↦ (P k).support) j
  exact ⟨X.allocation C hc hdis, X.assignment, X.suffix, he, ht⟩

end CakeCuttingPsomas.EnvyCycle
