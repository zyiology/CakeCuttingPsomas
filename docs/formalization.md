# Formalization guide

## Target statement

For each positive number `n` of agents, there exists one Robertson–Webb protocol
that works for every profile of normalized, nonnegative integrable densities on
`[0,1]`. It returns pairwise disjoint finite unions of intervals whose union is
the whole cake and which form an envy-free allocation. It uses at most
`2 * 32^n * n^7 * (n!)^2` queries.

This is the initial normalized unit-cake instance of the main theorem in Section 2.
The unconditional target's proof is a single `sorry` placeholder.
`exists_bounded_envy_free_protocol_of_dominate` proves the same conclusion from
an explicit `DominateProtocol.Correct` hypothesis, using the paper's `Divide`.
Section 3's `DominateAssembly.protocol_correct` constructs a correct `Dominate`
from correct Core and Repair protocols. The resulting
`exists_bounded_envy_free_protocol_of_core_repair` has the same conclusion and
query bound. Section 4's Core construction satisfies its contract conditional
on correct Permute. `exists_bounded_envy_free_protocol_of_permute_repair` reduces
the same target to correct Permute and Repair implementations, which remain to
be constructed.

## Files and definitions

- `CakeCuttingPsomas/Basic.lean`: ordered interval pieces, density-based
  valuations, partial allocations, residue, completeness, envy-freeness,
  domination, and dominated groups; support measurability and containment,
  disjoint piece concatenation, and basic residue properties.
- `CakeCuttingPsomas/Piece.lean`: exact interval splitting, ordered piece
  subtraction, and construction of residue pieces.
- `CakeCuttingPsomas/Cut.lean`: continuity of cumulative interval value,
  endpoint-equivalent values, smallest interval cuts, unique legal Cut answers,
  and their connection to geometric interval prefixes.
- `CakeCuttingPsomas/Prefix.lean`: ordered prefixes and suffixes parameterized
  by traversal length, exact partition and nesting, continuity of values,
  and existence of smallest prefixes.
- `CakeCuttingPsomas/Valuation.lean`: integrability on subsets of the unit cake,
  nonnegativity, monotonicity, and disjoint-union additivity of values.
- `CakeCuttingPsomas/Allocation.lean`: combination with an allocation from the
  residue, its exact residue formula, and preservation of envy-freeness and
  domination; dominated-group completion and extension of recursive allocations
  to the original agents.
- `CakeCuttingPsomas/Protocol.lean`: legal Eval/Cut answers, query protocols,
  sequencing, result mapping, agent relabeling, and execution lemmas with exact
  additive query counts.
- `CakeCuttingPsomas/Recorded.lean`: shared cell partitions, recorded values,
  their correctness and piece compatibility, refinement, restriction to
  participating agents, and cell-based residue construction.
- `CakeCuttingPsomas/Traversal.lean`: traversal-preserving subdivision, inherited
  ordered representations, and nonempty bands between distinct prefix positions.
- `CakeCuttingPsomas/RecordedProtocol.lean`: Eval protocols and the
  Eval-and-subtraction update after a cut, costing at most one Eval per agent.
- `CakeCuttingPsomas/PrefixProtocol.lean`: smallest-prefix cuts using recorded
  values, with correctness, inherited representations, and the `n + 1` query bound;
  terminal prefix cuts with the chooser's prefix value in at most two queries.
- `CakeCuttingPsomas/BaseCases.lean`: the one- and two-agent branches of `Divide`,
  complete and envy-free on arbitrary input pieces, using zero and at most two queries.
- `CakeCuttingPsomas/QueryBound.lean`: the domination cost, cumulative recursive
  cost, and the paper's explicit bound.
- `CakeCuttingPsomas/Dominate.lean`: the domination protocol interface and its
  correctness specification, including records for the recursive residue.
- `CakeCuttingPsomas/RecordedAllocation.lean`: shared partial-allocation outputs
  and inherited-record guarantees for Section 3's subroutines.
- `CakeCuttingPsomas/RecordedPreparation.lean`: current-cell representations and
  recorded support values, allocation transport, and preparation of Repair inputs
  after refinement, with unchanged query counts.
- `CakeCuttingPsomas/Core.lean`: the Core protocol contract and the cutter's
  residue contraction lemma.
- `CakeCuttingPsomas/Permute.lean`: the Permute contract, including suffix
  assignment, a whole-piece recipient, the indifference property, and query cost.
- `CakeCuttingPsomas/EqualPartition.lean`: recorded equal partitioning with
  exact coverage, disjointness, equal cutter values, and at most `n-1` prefix cuts.
- `CakeCuttingPsomas/CoreProtocol.lean`: Section 4's Core construction and its
  full correctness contract, conditional only on correct Permute.
- `CakeCuttingPsomas/RepairPartition.lean`: Repair’s common residue partition,
  pooled equal-value marks on one traversal, exact coverage and disjointness,
  cell counts and value bounds, and recorded-query accounting.
- `CakeCuttingPsomas/Repair.lean`: the Repair protocol contract, additions and
  bundle permutation, old-bundle containment, and exact residue formula.
- `CakeCuttingPsomas/DominateChoice.lean`: Section 3's choice lemma for the
  geometric scale, two agents, and bundle permutation.
- `CakeCuttingPsomas/DominateRepair.lean`: Section 3's post-Repair advantage
  for the distinguished agent over the reassigned distinguished bundle.
- `CakeCuttingPsomas/DominateProgress.lean`: inheritance of dominations after
  shrinking, strict domination-count progress, and the `n²` bound on the total.
- `CakeCuttingPsomas/DominateShrinking.lean`: recorded shrinking loop, preservation
  of bundle advantages and containments, geometric contraction, logarithmic
  stopping bound, and integration with domination-count progress.
- `CakeCuttingPsomas/DominateTermination.lean`: completed outer-iteration relation,
  preserved loop invariants, well-founded termination, and the `n²` bound on
  non-returning iterations, conditional on branch availability.
- `CakeCuttingPsomas/DominateSearch.lean`: finite recorded-value searches for a
  dominated group and the geometric scale, agents, and permutation.
- `CakeCuttingPsomas/DominateCost.lean`: total Section 3 query accounting,
  including the final returning Core call, and the explicit Dominate bound.
- `CakeCuttingPsomas/DominateProtocol.lean`: the assembled outer query protocol,
  branch availability, and correctness conditional only on Core and Repair.
- `CakeCuttingPsomas/Divide.lean`: the recursive protocol, termination, correctness,
  and query bound, conditional on a correct domination protocol.
- `CakeCuttingPsomas/Main.lean`: normalized unit-cake theorems conditional on
  Dominate, Core and Repair, or Permute and Repair, and the unproved target.
- `CakeCuttingPsomas.lean`: imports the complete development.

`Fin n` represents the agents using indices from zero through `n - 1`.
An allocation includes proofs that its bundles lie in the input cake and are
pairwise disjoint. Completeness and envy-freeness are separate predicates.
Piece lists preserve the interval order needed for later prefix/suffix operations.
Stored intervals have strictly positive length. Intervals ending at 1 include
that endpoint; other intervals are half-open. Empty pieces use an empty list,
so `{1}` is not a standalone component. Splitting at either endpoint produces
empty/whole or whole/empty, including at 1. This makes the paper's degenerate
endpoint convention explicit and keeps pieces closed under subtraction.
Positive length does not require positive value. Completeness uses exact sets,
rather than equality up to measure zero.

Values are Lebesgue integrals of the given densities. Integrability and
nonnegativity are assumptions; additivity and monotonicity are proved from them.
Query values use closed intervals. `Valuation.value_Icc_eq_Ico` proves that
these have the same values as half-open intervals for density valuations.
`Valuation.exists_smallest_cut` proves interval-cut existence, including flat
regions, and `RWQuery.existsUnique_cut_answer` proves that every legal Cut query
has a unique valid answer. `RWQuery.cut_answer_before` connects such answers
to the corresponding geometric interval prefixes.

The theorem chooses the protocol before quantifying over valuations. A protocol
can branch on query answers, but cannot inspect the densities directly. `Runs`
requires each query to be legal and each answer to be correct; Cut answers must
be the smallest valid cut point. Thus the query bound counts actual requests,
rather than an arbitrary number attached to an allocation. The model permits
arbitrary internal computation on exact real answers, as an abstract query model;
it does not provide an executable implementation.

## Next proof work

Basic support measurability and valuation properties are established.
`Allocation.combine X Y hY` appends each agent's interval lists, where
`hY : Y.allocated ⊆ X.residue`. Both allocations have the same input cake and
agent type. The new residue is exactly `X.residue \ Y.allocated`.
`envyFree_combine` requires both allocations to be envy-free;
`dominates_combine` preserves each old domination without that requirement.

Section 2's dominated-group completion argument is proved:
`envyFree_combine_dominatedGroup` only requires the added allocation to be
envy-free within the dominated group and empty outside it. This works even for
partial allocations of the residue. `complete_combine` gives completeness when
the added allocation fills exactly the residue; the combined result is
`complete_envyFree_combine_dominatedGroup`.

For a recursive result `Y : Allocation m R`, `Y.extendTo e hRC` relabels agents
using `e : Fin m ≃ E`, gives `Piece.empty` to outsiders, and regards the bundles
as subsets of the original cake via `hRC : R.support ⊆ C.support`. It preserves
allocated support and envy-freeness within `E`.
`X.combineRecursive Y e hR` combines this extension with `X`, given
`hR : R.support = X.residue`. The theorem
`complete_envyFree_combineRecursive` proves completeness and envy-freeness from
the corresponding recursive guarantees, envy-freeness of `X`, and domination
of `E`. These results do not require normalized or strictly positive values.

`CakeInterval.before` and `after` split an interval with exact disjointness
and coverage. `CakeInterval.diff` leaves at most two components.
`Piece.diff P Q` represents exactly `P.support \ Q.support`, preserving the
order of `P`'s components and the left-to-right order of surviving fragments
within each component. It does not globally sort or merge components.

`X.residuePiece` constructs a `Piece` with support exactly `X.residue` by
subtracting the bundle intervals from the input cake. No valuation queries are
needed. `X.combineResidue Y e` and `complete_envyFree_combineResidue` specialize
the recursive adapter to this constructed residue, removing the separate
representation obligation. The set-valued residue remains the interface for
valuation and domination statements.

`P.prefixAt s` traverses the specified interval list by geometric length,
independently of spatial order; `P.suffixAt s` is its exact remainder.
Positions zero and `P.length` give empty/whole and whole/empty. Prefixes are
nested, suffixes are nested in reverse, and their values are continuous.
`Valuation.exists_smallest_prefix` gives the first position attaining every
legal target; `exists_least_prefix` gives containment in every prefix with the
same value. A target of zero selects the empty prefix, and a full-value target
may leave a zero-valued suffix. No normalization or positive-value assumption
is used. These mathematical existence results are complemented by the recorded-value
query protocol described below.

`RWProtocol.bind` sequences protocols; `runs_bind_iff` splits executions with
additive counts. Result mapping and agent relabeling preserve counts. To embed a
recursive protocol on `Fin m` into the original agents, use the map
`fun i ↦ (e i).val` induced by `e : Fin m ≃ E`, and restrict the recorded state
along the same map.

`RecordedState` stores a shared partition of the unit cake and a table of real
cell values. `Correct` relates that table to valuations; valuations are absent
from the protocol data. `Compatible` pieces list cells in their own traversal
order. `pieceValue_eq` proves that their values are sums of records. The initial
normalized state costs no queries. Restriction to participating agents retains
correctness and compatible pieces, without normalization assumptions.

`recordCut` refines an interior cell using one Eval per participating agent and
subtraction for the other fragment; boundary points leave records unchanged.
`refinePiece` subdivides old representations while preserving their support and
interval order. `Refines` states that old pieces remain representable by new
cells; `Represents` records existence of a compatible representation of a set.
After a split, old interval lists may require subdivision before reuse.
`allocationResidue` filters out allocated cells from a compatible input cake,
preserving its traversal order. Its support is exactly the allocation's residue,
and `allocationResidue_value` recovers its value from existing records.

`prefixCut` scans recorded values, makes at most one Cut query, and updates the
records. `prefixCut_runs` proves smallest-prefix correctness, correct updated
records, preservation of old represented pieces, representability of both output
pieces, and at most `n + 1` queries. It handles empty input, zero targets, zero-valued
components, and flat regions without extra assumptions.

The one- and two-agent cases of Section 2 are proved. `RWProtocol.divideOne`
gives the whole input cake to its sole agent; `divideOne_runs` proves completeness,
envy-freeness, and exactly zero queries, without needing records.
`RWProtocol.divideTwo` implements cut-and-choose on an arbitrary compatible
ordered piece; `divideTwo_runs` proves completeness, envy-freeness, and at most
two queries from correct inherited records. Neither requires normalization,
positive values, or a nonempty cake.

`RecordedState.terminalPrefix` locates the smallest prefix from the cutter's
records, using at most one Cut and one Eval of the chooser's split fragment.
Whole preceding components use recorded values; subtraction gives the chooser's
suffix value. A zero target returns the empty prefix without queries, including
when the input cake is empty or has zero value to the cutter. The terminal
protocol returns only the allocation, so records need not be refreshed.

Section 2's full reduction is proved conditional on `Dominate`.
`DominateResult` contains a partial allocation, a group, updated records, and an
exact residue piece. `DominateProtocol.Correct` requires a legal execution with
an envy-free allocation, a nonempty proper dominated group, correct output
records, a compatible residue, and at most `dominateQueryBound n` queries.
The protocol family is chosen independently of valuations. Its existence is
not postulated as an axiom.

`RWProtocol.divide` branches to the proved base cases or calls `Dominate`,
restricts records and relabels agents for recursion, then combines allocations.
A group-size guard ensures that recursion decreases even on arbitrary answer
branches; the domination guarantee supplies the size bounds in valid executions.
`divide_runs` proves completeness and envy-freeness using strong induction and
`complete_envyFree_combineRecursive`, with cost at most `divideQueryCost n`.
For `n ≥ 2` this is `2 + ∑ m ∈ Finset.Icc 3 n, dominateQueryBound m`; for zero
or one agent it is zero. `divideQueryCost_le_queryBound` bounds the sum using
geometric growth of domination costs. `divide_runs_bounded` gives the explicit
bound for arbitrary compatible cakes and unnormalized or zero valuations.
The conditional theorem in `Main.lean` specializes this protocol to the free
initial normalized records and the unit cake.

Section 3's subroutine interfaces are specified by `CoreProtocol.Correct` and
`RepairProtocol.Correct`; neither asserts that an implementation exists.
`RecordedAllocationResult` packages an allocation, updated records, and an exact
residue piece. Its `Inherits` guarantee preserves representations of earlier
pieces through `RecordedState.Refines`, records all output bundles, and makes
the residue compatible for the next call. Earlier interval lists may need
subdivision after refinement.

Core's contract includes envy-freeness, the cutter's exact `1/n` share, and the
`coreQueryBound n = n^3 (n!)^2` cost. `cutter_residue_le` derives the cutter's
`(n-1)/n` residue contraction from the share equality, including zero-valued and
empty inputs. Repair's contract retains the paper's epsilon, positive-residue,
and almost-envy-free hypotheses. It returns a permutation `σ` and disjoint
additions `Z_j` from the old residue, with output bundle `σ(j)` equal in support
to `D_j ∪ Z_j`. The contract bounds each addition's value and requires the query
count to be at most `n/ε + coreQueryBound n`, expressed over the reals.
`old_bundle_subset` and `residue_removed` prove the corresponding containment
and exact residue identities from the output data.

Section 3's choice lemma (`lem:alpha pi exist for dominate`) is proved as
`DominateChoice.exists_choice`. Its hypotheses are an envy-free old allocation,
an envy-free allocation of its represented residue with Core's exact cutter
share, and absence of a dominated group after combining them. It concludes
positive new residue value for every agent and witnesses satisfying (S1)--(S3),
with `α = DominateChoice.scale n t` and `2 ≤ t ≤ n+1`. The proof establishes
strong connectivity of the old non-domination graph using reachable sets,
the cutter's normalized gap sum and `1/(n-1)` average bound, and the paper's
two cases. The small-edge case uses finite counting to find an empty geometric
band and `List.formPerm` to cycle a simple directed path. This is a mathematical
existence theorem; `DominateSearch.choice_available` connects its witnesses to
the finite search over inherited records.

The Repair call's mathematical preconditions in Section 3's proof of
`lem: dominate` are proved by `DominateChoice.Spec.repair_preconditions`.
`permutedCombined` constructs the allocation with bundles `X_i ∪ Y_{π(i)}`
using the existing allocation adapters, with exact residue `Y.residue`.
Envy-freeness of `X` and `Y` and (S2) give almost envy-freeness; the scale's
exponent lower bound gives `0 < α ≤ (4n²)⁻² < 1/(6n³)`. Positive residue
values are inherited from the choice lemma. `RepairProtocol.onRepresented`
prepares a compatible representation of the ambient cake, invokes Repair, and
transports its output back to the original cake representation at no query cost.

Section 3's immediate post-Repair advantage is proved by
`DominateChoice.Spec.postRepair_advantage`: Repair's envy-free output and
addition bounds, together with (S2)--(S3) and envy-freeness of `X`, give
`Vᵢ(Wᵢ) - Vᵢ(W_{σ(j)}) ≥ (n² - 1) α Vᵢ(U)` for the distinguished agents.
`RepairResult.value_bundle` gives exact value additivity for each reassigned
bundle. `Spec.postRepair_strict_advantage` proves positivity and `i ≠ σ(j)`
when `n ≥ 3` and `Vᵢ(U) > 0`.

`Allocation.advantage_le_combine` proves that each envy-free addition preserves
bundle advantages. `DominateChoice.Spec.progress_after_shrinking` proves progress
for a final envy-free extension satisfying the paper's bundle containments,
preservation of the post-Repair advantage, and final residue bound. Old
dominations transfer through `σ`; every domination count is nondecreasing,
and the distinguished count and their sum increase by at least one.
`Allocation.dominatedAgents`, `dominationCount`, and `totalDominationCount`
include self-indices exactly when the paper's domination inequality holds.
`totalDominationCount_le_sq` bounds the total by `n²`.

`DominateShrinking.run` implements the inner shrinking loop with bounded fuel,
using recorded residue values for its stopping checks. Conditional on
`CoreProtocol.Correct`, `run_correct` proves envy-freeness, preservation of all
bundle advantages and bundle containments, inherited records, and contraction
by `(1 - 1/n)^k` in the actual number `k` of Core calls. `shrink_correct` proves
the stopping threshold within `⌈n log(1/α)⌉₊` calls and at most that many times
`coreQueryBound n` queries. These results allow empty and zero-valued residues.
`budget_scale_le` supplies the paper's uniform bound
`⌈n(n+1) log(4n²)⌉₊`. `Spec.shrinking_progress` starts from Repair's output and
supplies all extension hypotheses of `progress_after_shrinking`, proving strict
domination-count progress for the resulting legal execution.

`DominateTermination.PreparedIteration` packages an actual initial Core execution,
the failed dominated-group test, a valid choice, and an actual Repair execution
with their correctness guarantees. `PreparedIteration.complete` finishes shrinking
conditional on Core's contract. `Iteration` retains that shrinking execution and
its extension guarantees; `Iteration.progress` derives the strict measure increase
and preserves the loop invariants. No progress inequality is assumed as a field.

For a trace of `k` completed non-returning iterations, `trace_progress` and
`trace_bound` prove `μ(X₀) + k ≤ μ(Xₖ)` and `k ≤ n² - μ(X₀) ≤ n²`.
Here `μ` is `totalDominationCount`; its initial value is not assumed to be zero.
The remaining-capacity measure `n² - μ(X)` strictly decreases, yielding
`wellFounded` and `no_infinite_continuations`. `terminates_of_prepared` proves a
return within that bound when each reachable iteration can return or prepare
Core, choice, and Repair. This theorem keeps branch availability explicit;
`DominateAssembly.step_correct` discharges it in the actual query protocol.
`reachable_invariants` and `Returns.output` give correct inherited records,
envy-freeness, and a dominated group for the returning allocation.
`outer_iteration_bound` allows the final returning iteration, giving at most
`n² + 1` outer iterations (and initial Core calls), and at most `n²` Repair calls.
Shrinking Core calls are counted separately.

Section 3's protocol construction is complete conditional on Core and Repair.
`RecordedState.represent` selects current cells contained in an old support;
`support_represent` proves exact coverage whenever that support is represented.
`supportValue_eq` recovers its value from the table. This handles old bundles
whose interval lists are no longer compatible after refinement. Rebuilding the
ambient cake for Repair does not change the bundles' traversal orders.

`DominateSearch.group` searches all finite agent subsets and
`DominateSearch.choice` searches bounded exponents, agent pairs, and permutations.
Their predicates contain no valuations. Soundness identifies their recorded tests
with the paper's domination inequality and (S1)--(S3); completeness connects failed
group tests to `exists_choice`. Both searches are free internal computation.

`DominateAssembly.step_correct` retains actual Core, prepared Repair, and
shrinking executions in `DominateTermination.Iteration`. The shrinking threshold
uses the recorded value of the initial Core residue, saved before Repair.
`run_correct` uses `n² + 1` outer-loop fuel and the existing remaining-capacity
measure to exclude exhaustion on legal executions. Arbitrary answer branches
have total fallback behavior; no correctness guarantees are claimed for them.
`protocol_correct` proves `DominateProtocol.Correct` from `CoreProtocol.Correct`
and `RepairProtocol.Correct`, without a separate branch-availability assumption.

`DominateCost.totalBudget` counts one final Core call plus at most `n²`
continuations, each consisting of Core, Repair, and bounded shrinking.
`totalBudget_le` proves the paper's explicit bound `32^n n^7 (n!)²`, using
Mathlib's Stirling lower bound and a loose polynomial estimate for the logarithm.
Repair's real-valued query inequality is bounded by an integer budget without
adding a rounding cost.

Section 4's Core reduction is proved. `PermuteProtocol.Correct` specifies all of
`lem:permute`, including its indifference property (ii), without asserting an
implementation exists. Input labels are retained even for empty pieces. The
prefix-cut bound is converted to Robertson--Webb queries using the `n+1` cost.

`EqualPartition.run` makes `n-1` prefix cuts with a fixed target computed from
the cutter's inherited records, leaving the last piece whole. Its correctness
theorem proves exact coverage, disjointness, equal cutter values, inherited
representations, and at most `(n-1)(n+1)` queries. Current-cell representations
of the remaining support supply compatible inputs after each refinement.
Zero targets and empty cakes need no separate value assumptions.

`CoreAssembly.protocol` follows equal partitioning with Permute.
`protocol_correct` proves `CoreProtocol.Correct`: the cutter cannot value her
suffix above an equal input piece, and envy-freeness prevents her from valuing
it below the whole piece given to some agent. `query_cost_le` proves
`(n+1)(n-1 + (n.choose 2)(n!)²) ≤ n³(n!)²` for `n ≥ 2`.

Section 4's common residue partition for Repair is proved.
`RepairPartition.run` collects each agent's `M-1` cumulative equal-value marks,
where `M = ⌈1/(3nε)⌉₊`, on the input residue's fixed interval-list traversal.
`TraversalRefines` and `representAlong` preserve every geometric prefix through
record refinement. Pooled marks define consecutive paper cells, each potentially
containing several inherited intervals. `run_correct` proves nonempty cells,
exact coverage, pairwise disjointness, correct inherited records,
`M ≤ cellCount ≤ n(M-1)+1 < 1/(2ε)`, value at most `Vᵢ(R)/M ≤ 3nεVᵢ(R)`,
and at most `n(M-1)(n+1)` queries. `size_bounds` also gives `2n² ≤ M`.
Cell supports are represented in the final state; use its recorded representation
to read cell values without queries. Positivity and epsilon assumptions are
exactly the relevant hypotheses of Repair; almost envy-freeness is not needed.

The next work is Repair's recorded round-robin selection, followed by the levels
argument showing that Permute preserves all old bundles and the assembly of
Repair. Section 5's Permute construction and correctness proof follow. These
remain necessary for the unconditional theorem. The asymptotic bound `2^{O(n log n)}` also remains to be
derived from the explicit bound.

## Checking

Run `lake build`. A warning that the target uses `sorry` is expected at this
stage. The conditional reduction and supporting results are proved; successful
compilation does not establish the unconditional target while its placeholder remains.
