module

public import CakeCuttingPsomas.Divide
public import CakeCuttingPsomas.DominateProtocol
public import CakeCuttingPsomas.CoreProtocol
public import CakeCuttingPsomas.RepairProtocol
public import CakeCuttingPsomas.PermuteProtocol
public import CakeCuttingPsomas.Asymptotics

-- This project does not prescribe mathlib's copyright/license header format.
set_option linter.style.header false

/-! # Target theorem

The initial, normalized unit-cake instance of the main theorem in Section 2.
The conditional theorems construct Divide from Dominate, Dominate from Core and
Repair, and both Core and Repair from Permute. Section 5's assembled Permute
closes the unconditional theorem.
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

/-- Sections 2--3 (`thm: main theorem` and `lem: dominate`): correct Core and
Repair implementations suffice for the normalized unit-cake theorem. The
protocol is chosen uniformly before the valuations, with the same query bound. -/
theorem exists_bounded_envy_free_protocol_of_core_repair
    (K : CoreProtocol) (hK : K.Correct) (P : RepairProtocol) (hP : P.Correct)
    (n : ℕ) (hn : 0 < n) :
    ∃ protocol : RWProtocol n (Allocation n unitCake),
      ∀ v : Fin n → Valuation, (∀ i, (v i).Normalized) →
        ∃ (A : Allocation n unitCake) (count : ℕ),
          protocol.Runs v A count ∧ A.Complete ∧ A.EnvyFree v ∧ count ≤ queryBound n :=
  exists_bounded_envy_free_protocol_of_dominate (DominateAssembly.protocol K P)
    (DominateAssembly.protocol_correct K hK P hP) n hn

/-- Sections 2--4 (`thm: main theorem`, `lem:core main`, and `lem:permute`):
the equal-partition Core construction reduces the target to correct Permute and
Repair protocols, preserving the paper's explicit bound. -/
theorem exists_bounded_envy_free_protocol_of_permute_repair
    (P : PermuteProtocol) (hP : P.Correct) (R : RepairProtocol) (hR : R.Correct)
    (n : ℕ) (hn : 0 < n) :
    ∃ protocol : RWProtocol n (Allocation n unitCake),
      ∀ v : Fin n → Valuation, (∀ i, (v i).Normalized) →
        ∃ (A : Allocation n unitCake) (count : ℕ),
          protocol.Runs v A count ∧ A.Complete ∧ A.EnvyFree v ∧ count ≤ queryBound n :=
  exists_bounded_envy_free_protocol_of_core_repair (CoreAssembly.protocol P)
    (CoreAssembly.protocol_correct P hP) R hR n hn

/-- Sections 2--4 (`thm: main theorem`, `lem:core main`, `lem:repair main`,
and `lem:permute`): the constructed Core and Repair reduce the normalized
unit-cake theorem to a correct Permute protocol alone, with the explicit bound. -/
theorem exists_bounded_envy_free_protocol_of_permute
    (P : PermuteProtocol) (hP : P.Correct) (n : ℕ) (hn : 0 < n) :
    ∃ protocol : RWProtocol n (Allocation n unitCake),
      ∀ v : Fin n → Valuation, (∀ i, (v i).Normalized) →
        ∃ (A : Allocation n unitCake) (count : ℕ),
          protocol.Runs v A count ∧ A.Complete ∧ A.EnvyFree v ∧ count ≤ queryBound n :=
  exists_bounded_envy_free_protocol_of_permute_repair P hP (RepairAssembly.protocol P)
    (RepairAssembly.protocol_correct P hP) n hn

/-- Section 2's main theorem (`thm: main theorem`), using Section 5's
`alg:permute` and `lem:permute`: for every positive number of agents, one protocol
works for every profile of normalized nonnegative integrable densities.
It returns a complete envy-free allocation using at most the paper's explicit
number of Robertson–Webb queries.

The protocol is chosen BEFORE the valuations, so it cannot inspect densities
directly. Its only access to them is through the queries checked by `Runs`. -/
theorem exists_bounded_envy_free_protocol (n : ℕ) (hn : 0 < n) :
    ∃ protocol : RWProtocol n (Allocation n unitCake),
      ∀ v : Fin n → Valuation, (∀ i, (v i).Normalized) →
        ∃ (A : Allocation n unitCake) (count : ℕ),
          protocol.Runs v A count ∧ A.Complete ∧ A.EnvyFree v ∧ count ≤ queryBound n :=
  exists_bounded_envy_free_protocol_of_permute PermuteAssembly.protocol
    PermuteAssembly.protocol_correct n hn

/-- Section 2's main theorem (`thm: main theorem`), asymptotic corollary:
uniform protocols use `2^{O(n log n)}` queries. The constant and threshold are
independent of the agent count and valuations, and each protocol is chosen
before the normalized valuation profile. -/
theorem exists_asymptotically_bounded_envy_free_protocol :
    ∃ (c : ℝ), 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ protocol : RWProtocol n (Allocation n unitCake),
        ∀ v : Fin n → Valuation, (∀ i, (v i).Normalized) →
          ∃ (A : Allocation n unitCake) (count : ℕ),
            protocol.Runs v A count ∧ A.Complete ∧ A.EnvyFree v ∧
              (count : ℝ) ≤ (2 : ℝ) ^ (c * (n : ℝ) * Real.log (n : ℝ)) := by
  refine ⟨11 / Real.log 2, div_pos (by norm_num) (Real.log_pos (by norm_num)),
    2, ?_⟩
  intro n hn
  obtain ⟨protocol, hprotocol⟩ := exists_bounded_envy_free_protocol n (by omega)
  refine ⟨protocol, ?_⟩
  intro v hv
  obtain ⟨A, count, hruns, hcomplete, henvy, hcount⟩ := hprotocol v hv
  exact ⟨A, count, hruns, hcomplete, henvy,
    (Nat.cast_le.mpr hcount).trans (queryBound_le_two_rpow hn)⟩

end CakeCuttingPsomas
