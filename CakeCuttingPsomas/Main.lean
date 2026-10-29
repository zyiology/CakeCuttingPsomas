module

public import CakeCuttingPsomas.Divide

-- This project does not prescribe mathlib's copyright/license header format.
set_option linter.style.header false

/-! # Target theorem

The initial, normalized unit-cake instance of the main theorem in Section 2.
The unconditional proof is intentionally unfinished. The conditional theorem
constructs the paper's `Divide` from a correct domination protocol.
-/

@[expose] public section

namespace CakeCuttingPsomas

/-- The normalized unit-cake instance of Section 2's main theorem
(`thm: main theorem`), conditional on a protocol satisfying `lem: dominate`
and the inherited-record convention of Section 1.3. The resulting uniform
protocol is the paper's `Divide`, chosen before the valuations. -/
theorem exists_bounded_envy_free_protocol_of_dominate
    (D : DominateProtocol) (hD : D.Correct) (n : ℕ) (hn : 0 < n) :
    ∃ protocol : RWProtocol n (Allocation n unitCake),
      ∀ v : Fin n → Valuation, (∀ i, (v i).Normalized) →
        ∃ (A : Allocation n unitCake) (count : ℕ),
          protocol.Runs v A count ∧ A.Complete ∧ A.EnvyFree v ∧ count ≤ queryBound n := by
  refine ⟨RWProtocol.divide D n hn (RecordedState.initial n) unitCake, ?_⟩
  intro v hv
  exact RWProtocol.divide_runs_bounded D hD n hn (RecordedState.initial n) unitCake v
    (RecordedState.correct_initial v hv) (fun _ h ↦ h)

/-- For every positive number of agents, one protocol works for every profile
of normalized nonnegative integrable densities. It returns a complete envy-free
allocation using at most the paper's explicit number of Robertson–Webb queries.

The protocol is chosen BEFORE the valuations, so it cannot inspect densities
directly. Its only access to them is through the queries checked by `Runs`.

UNPROVED: `sorry` is a placeholder, not a verified mathematical proof. -/
theorem exists_bounded_envy_free_protocol (n : ℕ) (hn : 0 < n) :
    ∃ protocol : RWProtocol n (Allocation n unitCake),
      ∀ v : Fin n → Valuation, (∀ i, (v i).Normalized) →
        ∃ (A : Allocation n unitCake) (count : ℕ),
          protocol.Runs v A count ∧ A.Complete ∧ A.EnvyFree v ∧ count ≤ queryBound n := by
  sorry

end CakeCuttingPsomas
