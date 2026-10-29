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
The conditional theorem is proved; a correct `Dominate` implementation is still
needed to establish the unconditional target.

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
- `CakeCuttingPsomas/Divide.lean`: the recursive protocol, termination, correctness,
  and query bound, conditional on a correct domination protocol.
- `CakeCuttingPsomas/Main.lean`: the conditional normalized unit-cake theorem and
  the unproved unconditional `exists_bounded_envy_free_protocol`.
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

The full development still needs implementations of `Permute`, `Core`, `Repair`,
and `Dominate`, with their correctness, termination, and query accounting proofs.
Proving the `DominateProtocol.Correct` contract will discharge the hypothesis
of the conditional main theorem. The asymptotic bound `2^{O(n log n)}` also
remains to be derived from the explicit bound.

## Checking

Run `lake build`. A warning that the target uses `sorry` is expected at this
stage. The conditional reduction and supporting results are proved; successful
compilation does not establish the unconditional target while its placeholder remains.
