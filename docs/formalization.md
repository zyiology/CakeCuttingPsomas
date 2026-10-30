# Formalization guide

The main theorem of [the paper](../paper/main.tex), its subroutines, and its
asymptotic query bound are proved. Import `CakeCuttingPsomas` for the complete
development. All declaration names below are in the `CakeCuttingPsomas` namespace.

## Final statements

For every positive number `n` of agents, one Robertson–Webb protocol works for
all profiles of normalized, nonnegative integrable densities on `[0,1]`. It
returns a complete envy-free allocation into pairwise disjoint finite unions
of intervals, using at most `2 * 32^n * n^7 * (n!)^2` queries. The protocol is
chosen before the valuation profile.

`exists_bounded_envy_free_protocol_on_piece` gives the same bound for any ordered
cake compatible with supplied correct inherited records, including empty cakes
and unnormalized or zero valuations. Preparing records for an arbitrary starting
cake is outside that query budget. The normalized unit-cake instance starts with
correct records for free, as in Section 1.3 of the paper.

## Paper-to-Lean theorem map

The assembly follows `Divide → Dominate → Core / Repair → Permute`. Intermediate
correctness theorems take explicit subroutine contracts; the final theorems in
`Main.lean` discharge all of them using the constructed implementations.

| Paper result or argument | Lean declaration(s) | Source |
| --- | --- | --- |
| §1.3: smallest Cut answers and prefix cuts | `RWQuery.existsUnique_cut_answer`; `RecordedState.prefixCut_runs` | [Cut](../CakeCuttingPsomas/Cut.lean), [PrefixProtocol](../CakeCuttingPsomas/PrefixProtocol.lean) |
| §2: dominated-group completion | `Allocation.complete_envyFree_combineRecursive` | [Allocation](../CakeCuttingPsomas/Allocation.lean) |
| §2: Divide correctness and explicit query bound | `RWProtocol.divide_runs_bounded` | [Divide](../CakeCuttingPsomas/Divide.lean) |
| §2: main theorem, arbitrary compatible cake | `exists_bounded_envy_free_protocol_on_piece` | [Main](../CakeCuttingPsomas/Main.lean) |
| §2: main theorem, normalized unit cake | `exists_bounded_envy_free_protocol` | [Main](../CakeCuttingPsomas/Main.lean) |
| §2: `2^{O(n log n)}` bound | `log_queryBound_isBigO`; `exists_asymptotically_bounded_envy_free_protocol` | [Asymptotics](../CakeCuttingPsomas/Asymptotics.lean), [Main](../CakeCuttingPsomas/Main.lean) |
| §3: choice of scale, agents, and permutation | `DominateChoice.exists_choice` | [DominateChoice](../CakeCuttingPsomas/DominateChoice.lean) |
| §3: domination-count progress and termination | `DominateTermination.Iteration.progress`; `DominateTermination.trace_bound` | [DominateTermination](../CakeCuttingPsomas/DominateTermination.lean) |
| §3: Dominate lemma, including query bound | `DominateAssembly.protocol_correct`; `DominateCost.totalBudget_le` | [DominateProtocol](../CakeCuttingPsomas/DominateProtocol.lean), [DominateCost](../CakeCuttingPsomas/DominateCost.lean) |
| §4: Core lemma | `CoreAssembly.protocol_correct` | [CoreProtocol](../CakeCuttingPsomas/CoreProtocol.lean) |
| §4: Repair lemma | `RepairAssembly.protocol_correct` | [RepairProtocol](../CakeCuttingPsomas/RepairProtocol.lean) |
| §5: candidate construction and containment claim | `CandidateConstruction.runs_spec`; `IsCandidate.containment` | [CandidateProtocol](../CakeCuttingPsomas/CandidateProtocol.lean), [Candidate](../CakeCuttingPsomas/Candidate.lean) |
| §5: approximate suffix allocation by envy-cycle elimination | `EnvyCycle.exists_terminal_allocation` | [ApproximateSuffix](../CakeCuttingPsomas/ApproximateSuffix.lean) |
| §5: terminal allocation contains a candidate | `EnvyCycle.State.Terminal.contains_candidate` | [CandidateExtension](../CakeCuttingPsomas/CandidateExtension.lean) |
| §5: some candidate is envy-free, by compactness | `CandidateConstruction.exists_envyFree_guess` | [CandidateCompactness](../CakeCuttingPsomas/CandidateCompactness.lean) |
| §5: Permute lemma, both additional guarantees and query bound | `PermuteAssembly.protocol_correct` | [PermuteProtocol](../CakeCuttingPsomas/PermuteProtocol.lean) |

## Modeling conventions

- **Pieces and endpoints.** A `Piece` stores an ordered list of disjoint intervals;
  traversal order need not be spatial order. Intervals have positive length and
  are half-open, except those ending at `1`, which include that endpoint. Empty
  pieces use the empty list; `{1}` is not a standalone component. Endpoint splits
  give empty/whole or whole/empty pieces. Completeness is exact set equality,
  including endpoints.
- **Valuations.** Values are Lebesgue integrals of nonnegative integrable densities.
  Normalization is a separate predicate. Positive length need not mean positive
  value. Recursive calls allow unnormalized and zero valuations; Repair retains
  the paper's positive-residue and epsilon hypotheses.
- **Inherited records.** `RecordedState` stores cell geometry and values, with
  correctness relative to a valuation profile stated separately. Refinements
  preserve representations of earlier pieces, sometimes by subdividing their
  interval lists. A prefix cut costs at most `n + 1` queries, including record
  updates. Bundle and residue values are computed from records.
- **Query model.** `RWProtocol` branches only on query answers; it cannot inspect
  densities. `Runs` checks query legality and answer correctness, counting each
  Eval or Cut once. Cuts return the smallest valid point, including in flat
  regions. Internal computation on exact real answers is free; the development
  proves an abstract query protocol and does not provide an executable program.
  Fine partitions, envy-cycle elimination, and compactness in Section 5 are used
  only to prove that Permute's finite search succeeds and incur no protocol queries.

## Verification

Run `lake build` from the repository root. The Lean version is pinned in
[lean-toolchain](../lean-toolchain), and the mathlib revision in
[lakefile.toml](../lakefile.toml).

To audit dependencies, save the following as `/tmp/cake-cutting-audit.lean` and
run `lake env lean /tmp/cake-cutting-audit.lean` from the repository root:

```lean
import CakeCuttingPsomas

#print axioms CakeCuttingPsomas.PermuteAssembly.protocol_correct
#print axioms CakeCuttingPsomas.CoreAssembly.protocol_correct
#print axioms CakeCuttingPsomas.RepairAssembly.protocol_correct
#print axioms CakeCuttingPsomas.DominateAssembly.protocol_correct
#print axioms CakeCuttingPsomas.exists_bounded_envy_free_protocol_on_piece
#print axioms CakeCuttingPsomas.exists_bounded_envy_free_protocol
#print axioms CakeCuttingPsomas.exists_asymptotically_bounded_envy_free_protocol
```

These declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The development has no `sorry` placeholders or project-specific axioms.

The [archived progress guide](archive/formalization-progress.md) preserves the
former detailed file map and milestone notes for historical reference.
