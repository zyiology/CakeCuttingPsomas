module

public import CakeCuttingPsomas.DominateShrinking
public import CakeCuttingPsomas.RecordedPreparation
public import Mathlib.Logic.Relation

set_option linter.style.header false

/-! # Termination of Dominate's outer loop

Section 3, proof of `lem: dominate` in `paper/main.tex`, paragraphs on increasing
counts and termination. This is mathematical termination of the completed stages;
recorded-value searches and the outer query protocol are in `DominateProtocol`.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.DominateTermination

/-- Section 3, `alg:dominate`: the mathematical data of a non-returning iteration.
The protocol executions are retained, rather than assuming progress as a field.
Correctness facts are the guarantees of Core, Repair, and the shrinking loop. -/
structure PreparedIteration {n : ℕ} {C : Piece} (K : CoreProtocol) (P : RepairProtocol)
    (v : Fin n → Valuation) (w : RecordedAllocationResult n C) where
  agents_lower : 3 ≤ n
  core : RecordedAllocationResult n w.residue
  cutter : Fin n
  coreCount : ℕ
  coreRuns : (K n (by omega) w.state w.residue cutter).Runs v core coreCount
  old_envyFree : w.allocation.EnvyFree v
  core_correct : core.state.Correct v
  core_envyFree : core.allocation.EnvyFree v
  core_share : (v cutter).value (core.allocation.bundle cutter).support =
    (v cutter).value w.residue.support / n
  core_inherits : core.Inherits w.state
  no_group : ∀ E : Set (Fin n),
    ¬ (DominateChoice.combined w.allocation core.allocation w.residue_eq).DominatedGroup v E
  exponent : ℕ
  distinguished : Fin n
  other : Fin n
  permutation : Equiv.Perm (Fin n)
  choice : DominateChoice.Spec w.allocation core.allocation v exponent
    distinguished other permutation
  repair : RepairResult n C
    (DominateChoice.permutedCombined w.allocation core.allocation w.residue_eq permutation)
  repairCount : ℕ
  repairRuns : (P.onRepresented n (by omega) core.state C
    (DominateChoice.permutedCombined w.allocation core.allocation w.residue_eq permutation)
    (DominateChoice.scale n exponent)).Runs v repair repairCount
  repair_correct : repair.state.Correct v
  repair_envyFree : repair.allocation.EnvyFree v
  repair_inherits : repair.toRecordedAllocationResult.Inherits core.state
  additions : ∀ i j, (v i).value (repair.addition j).support ≤
    3 * (n : ℝ) ^ 2 * DominateChoice.scale n exponent *
      (v i).value
        (DominateChoice.permutedCombined w.allocation core.allocation w.residue_eq
          permutation).residue

/-- Section 3, `alg:dominate`: a prepared iteration followed by a completed
shrinking execution and its correctness guarantees. -/
structure Iteration {n : ℕ} {C : Piece} (K : CoreProtocol) (P : RepairProtocol)
    (v : Fin n → Valuation) (w z : RecordedAllocationResult n C)
    extends PreparedIteration K P v w where
  shrinkCalls : ℕ
  shrinkCount : ℕ
  shrinkRuns : (DominateShrinking.run K n (by omega) distinguished
    (DominateChoice.scale n exponent * (v distinguished).value core.allocation.residue)
    (DominateShrinking.budget n (DominateChoice.scale n exponent))
    repair.toRecordedAllocationResult).Runs v (z, shrinkCalls) shrinkCount
  extension : DominateShrinking.Extension repair.toRecordedAllocationResult z v
  stopped : (v distinguished).value z.residue.support ≤
    DominateChoice.scale n exponent * (v distinguished).value core.allocation.residue
  correct : z.state.Correct v
  inherits : z.Inherits repair.state

/-- Section 3, proof of `lem: dominate`: a prepared Core-choice-Repair branch
can always finish its shrinking phase, conditional on Core's contract. -/
theorem PreparedIteration.complete {n : ℕ} {C : Piece}
    {K : CoreProtocol} {P : RepairProtocol} {v : Fin n → Valuation}
    {w : RecordedAllocationResult n C} (h : PreparedIteration K P v w)
    (hK : K.Correct) : ∃ z, Nonempty (Iteration K P v w z) := by
  have hi : h.repair.toRecordedAllocationResult.Inherits h.repair.state :=
    ⟨RecordedState.refines_refl _, h.repair_inherits.2⟩
  have hinit : (v h.distinguished).value h.repair.residue.support ≤
      (v h.distinguished).value h.core.allocation.residue := by
    apply (v h.distinguished).value_mono h.repair.residue.measurableSet_support
      h.core.allocation.measurableSet_residue _ h.core.allocation.residue_subset_unit
    rw [h.repair.residue_removed, DominateChoice.permutedCombined_residue]
    exact Set.sdiff_subset
  obtain ⟨z, k, count, hz, hs, hi', he, _hk, _hc, _hg, hres⟩ :=
    DominateShrinking.shrink_correct K hK (by have := h.agents_lower; omega)
      h.distinguished
      (DominateChoice.scale_repair_bounds h.agents_lower h.choice.exponent_lower).1
      ((v h.distinguished).value_nonneg h.core.allocation.measurableSet_residue
        h.core.allocation.residue_subset_unit)
      h.repair.toRecordedAllocationResult v h.repair_correct hi h.repair_envyFree hinit
  refine ⟨z, ⟨?_⟩⟩
  exact { toPreparedIteration := h
          shrinkCalls := k
          shrinkCount := count
          shrinkRuns := hz
          extension := he
          stopped := hres
          correct := hs
          inherits := hi' }

/-- A completed non-returning iteration of Section 3's outer loop. -/
def Continues {n : ℕ} {C : Piece} (K : CoreProtocol) (P : RepairProtocol)
    (v : Fin n → Valuation) (w z : RecordedAllocationResult n C) : Prop :=
  Nonempty (Iteration K P v w z)

/-- Section 3, proof of `lem: dominate`: a completed continuation preserves the
loop invariants and increases the sum of domination counts by at least one. -/
theorem Iteration.progress {n : ℕ} {C : Piece} {K : CoreProtocol} {P : RepairProtocol}
    {v : Fin n → Valuation} {w z : RecordedAllocationResult n C}
    (h : Iteration K P v w z) :
    z.state.Correct v ∧ z.Inherits w.state ∧ z.allocation.EnvyFree v ∧
      (∀ i, w.allocation.dominationCount v i ≤ z.allocation.dominationCount v i) ∧
      w.allocation.totalDominationCount v + 1 ≤ z.allocation.totalDominationCount v := by
  have hp := h.choice.progress_of_extension h.agents_lower w.residue_eq h.repair z
    h.old_envyFree h.repair_envyFree h.additions h.extension h.stopped
  exact ⟨h.correct,
    ⟨h.core_inherits.1.trans (h.repair_inherits.1.trans h.inherits.1), h.inherits.2⟩,
    h.extension.envyFree, hp.2.1, hp.2.2.2⟩

/-- Section 3, proof of `lem: dominate`: all reachable outer-loop states retain
envy-freeness, correct records, and inherited representations of the initial state. -/
theorem reachable_invariants {n : ℕ} {C : Piece}
    {K : CoreProtocol} {P : RepairProtocol} {v : Fin n → Valuation}
    {w z : RecordedAllocationResult n C} {s : RecordedState n}
    (hs : w.state.Correct v) (hi : w.Inherits s) (hw : w.allocation.EnvyFree v)
    (h : Relation.ReflTransGen (Continues K P v) w z) :
    z.state.Correct v ∧ z.Inherits s ∧ z.allocation.EnvyFree v := by
  induction h with
  | refl => exact ⟨hs, hi, hw⟩
  | tail _ hstep ih =>
    obtain ⟨hstep⟩ := hstep
    have hp := hstep.progress
    exact ⟨hp.1, ⟨ih.2.1.1.trans hp.2.1.1, hp.2.1.2⟩, hp.2.2.1⟩

/-- Remaining capacity in Section 3's bounded domination-count measure. -/
def remaining {n : ℕ} {C : Piece} (v : Fin n → Valuation)
    (w : RecordedAllocationResult n C) : ℕ :=
  n ^ 2 - w.allocation.totalDominationCount v

/-- Section 3, proof of `lem: dominate`: remaining capacity strictly decreases
on every non-returning iteration. -/
theorem remaining_lt {n : ℕ} {C : Piece} {K : CoreProtocol} {P : RepairProtocol}
    {v : Fin n → Valuation} {w z : RecordedAllocationResult n C}
    (h : Continues K P v w z) : remaining v z < remaining v w := by
  obtain ⟨h⟩ := h
  have hp := h.progress.2.2.2.2
  have hw := w.allocation.totalDominationCount_le_sq v
  have hz := z.allocation.totalDominationCount_le_sq v
  unfold remaining
  omega

/-- Section 3, proof of `lem: dominate`: the continuation relation is
well-founded when oriented from the next state to the previous state. -/
theorem wellFounded {n : ℕ} {C : Piece} (K : CoreProtocol) (P : RepairProtocol)
    (v : Fin n → Valuation) :
    WellFounded (fun z w : RecordedAllocationResult n C ↦ Continues K P v w z) := by
  exact Subrelation.wf (fun h ↦ remaining_lt h) (measure (remaining v)).wf

/-- A finite prefix of completed outer iterations gives ordinary reachability. -/
theorem trace_reachable {n : ℕ} {C : Piece} {K : CoreProtocol} {P : RepairProtocol}
    {v : Fin n → Valuation} (states : ℕ → RecordedAllocationResult n C) (k : ℕ)
    (h : ∀ j < k, Continues K P v (states j) (states (j + 1))) :
    Relation.ReflTransGen (Continues K P v) (states 0) (states k) := by
  induction k with
  | zero => exact .refl
  | succ k ih => exact (ih (fun j hj ↦ h j (by omega))).tail (h k (by omega))

/-- Section 3, proof of `lem: dominate`: after `k` non-returning iterations,
the total count has increased by at least `k`. Only a finite prefix is used. -/
theorem trace_progress {n : ℕ} {C : Piece} {K : CoreProtocol} {P : RepairProtocol}
    {v : Fin n → Valuation} (states : ℕ → RecordedAllocationResult n C) (k : ℕ)
    (h : ∀ j < k, Continues K P v (states j) (states (j + 1))) :
    (states 0).allocation.totalDominationCount v + k ≤
      (states k).allocation.totalDominationCount v := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hi := ih (fun j hj ↦ h j (by omega))
    obtain ⟨hs⟩ := h k (by omega)
    have hp := hs.progress.2.2.2.2
    omega

/-- Section 3, proof of `lem: dominate`: there are at most `n² - μ(X₀)`
non-returning iterations, hence at most `n²`, including zero-valued inputs. -/
theorem trace_bound {n : ℕ} {C : Piece} {K : CoreProtocol} {P : RepairProtocol}
    {v : Fin n → Valuation} (states : ℕ → RecordedAllocationResult n C) (k : ℕ)
    (h : ∀ j < k, Continues K P v (states j) (states (j + 1))) :
    k ≤ remaining v (states 0) ∧ k ≤ n ^ 2 := by
  have hp := trace_progress states k h
  have hb := (states k).allocation.totalDominationCount_le_sq v
  unfold remaining
  omega

/-- Section 3, proof of `lem: dominate`: an infinite sequence of completed
non-returning iterations would exceed the `n²` bound on domination counts. -/
theorem no_infinite_continuations {n : ℕ} {C : Piece}
    {K : CoreProtocol} {P : RepairProtocol} {v : Fin n → Valuation}
    (states : ℕ → RecordedAllocationResult n C) :
    ¬ (∀ j, Continues K P v (states j) (states (j + 1))) := by
  intro h
  have := (trace_bound states (n ^ 2 + 1) (fun j _ ↦ h j)).2
  omega

/-- Section 3, proof of `lem: dominate`: no completed continuation is possible
once the domination-count capacity is exhausted. -/
theorem no_continuation_at_capacity {n : ℕ} {C : Piece}
    {K : CoreProtocol} {P : RepairProtocol} {v : Fin n → Valuation}
    {w : RecordedAllocationResult n C} (hw : remaining v w = 0) :
    ∀ z, ¬ Continues K P v w z := by
  intro z hz
  have := remaining_lt hz
  omega

/-- Section 3, `alg:dominate`, returning branch: an actual Core execution whose
combined allocation has a nonempty proper dominated group. -/
def Returns {n : ℕ} {C : Piece} (K : CoreProtocol) (v : Fin n → Valuation)
    (w : RecordedAllocationResult n C) : Prop :=
  ∃ (hn : 3 ≤ n) (cutter : Fin n) (f : RecordedAllocationResult n w.residue)
    (count : ℕ) (group : Finset (Fin n)),
    (K n (by omega) w.state w.residue cutter).Runs v f count ∧
    f.state.Correct v ∧ f.Inherits w.state ∧ f.allocation.EnvyFree v ∧
    (w.appendCore f).allocation.DominatedGroup v (↑group)

/-- Section 3, proof of `lem: dominate`: the returning Core branch yields an
envy-free allocation with a valid dominated group and correct inherited records. -/
theorem Returns.output {n : ℕ} {C : Piece} {K : CoreProtocol}
    {v : Fin n → Valuation} {w : RecordedAllocationResult n C}
    {s : RecordedState n} (h : Returns K v w)
    (hi : w.Inherits s) (hw : w.allocation.EnvyFree v) :
    ∃ (z : RecordedAllocationResult n C) (group : Finset (Fin n)),
      z.state.Correct v ∧ z.Inherits s ∧ z.allocation.EnvyFree v ∧
      z.allocation.DominatedGroup v (↑group) := by
  obtain ⟨hn, cutter, f, count, group, _hrun, hs, hf, hef, hgroup⟩ := h
  exact ⟨w.appendCore f, group, hs, w.appendCore_inherits f hi hf,
    (w.appendCore_envyFree_advantage f v hw hef).1, hgroup⟩

/-- Section 3, proof of `lem: dominate`: if an iteration's two branches are
available, exhausted capacity forces the returning branch. `DominateAssembly.step_correct`
discharges branch availability using the recorded-value searches. -/
theorem returns_at_capacity {n : ℕ} {C : Piece} {K : CoreProtocol}
    {P : RepairProtocol} {v : Fin n → Valuation} {w : RecordedAllocationResult n C}
    (hw : remaining v w = 0)
    (hbranch : Returns K v w ∨ ∃ z, Continues K P v w z) : Returns K v w := by
  rcases hbranch with h | ⟨z, hz⟩
  · exact h
  · exact False.elim (no_continuation_at_capacity hw z hz)

/-- Section 3, proof of `lem: dominate`: branch availability on reachable states
implies a return after at most `n² - μ(X₀)` continuations. This is mathematical
termination, not an implementation of the outer query protocol. -/
theorem terminates {n : ℕ} {C : Piece} (K : CoreProtocol) (P : RepairProtocol)
    (v : Fin n → Valuation) (w : RecordedAllocationResult n C)
    (hbranch : ∀ z, Relation.ReflTransGen (Continues K P v) w z →
      Returns K v z ∨ ∃ u, Continues K P v z u) :
    ∃ (k : ℕ) (states : ℕ → RecordedAllocationResult n C),
      states 0 = w ∧ k ≤ remaining v w ∧
      (∀ j < k, Continues K P v (states j) (states (j + 1))) ∧
      Returns K v (states k) := by
  have go : ∀ z, Relation.ReflTransGen (Continues K P v) w z →
      ∃ (k : ℕ) (states : ℕ → RecordedAllocationResult n C),
        states 0 = z ∧ k ≤ remaining v z ∧
        (∀ j < k, Continues K P v (states j) (states (j + 1))) ∧
        Returns K v (states k) := by
    intro z
    induction z using (wellFounded K P v).induction with
    | h z ih =>
      intro hreach
      rcases hbranch z hreach with hreturn | ⟨u, hstep⟩
      · exact ⟨0, fun _ ↦ z, rfl, Nat.zero_le _, by simp, hreturn⟩
      · obtain ⟨k, states, hzero, hk, htrace, hreturn⟩ :=
          ih u hstep (hreach.tail hstep)
        let next : ℕ → RecordedAllocationResult n C
          | 0 => z
          | j + 1 => states j
        refine ⟨k + 1, next, rfl, ?_, ?_, hreturn⟩
        · have := remaining_lt hstep
          omega
        · intro j hj
          cases j with
          | zero => simpa only [next, hzero] using hstep
          | succ j => exact htrace j (by omega)
  exact go w .refl

/-- Section 3, proof of `lem: dominate`: it suffices that each reachable
iteration can return or prepare Core, choice, and Repair. Core's contract then
finishes shrinking, so preparation never adds a separate termination assumption. -/
theorem terminates_of_prepared {n : ℕ} {C : Piece}
    (K : CoreProtocol) (hK : K.Correct) (P : RepairProtocol)
    (v : Fin n → Valuation) (w : RecordedAllocationResult n C)
    (hbranch : ∀ z, Relation.ReflTransGen (Continues K P v) w z →
      Returns K v z ∨ Nonempty (PreparedIteration K P v z)) :
    ∃ (k : ℕ) (states : ℕ → RecordedAllocationResult n C),
      states 0 = w ∧ k ≤ remaining v w ∧
      (∀ j < k, Continues K P v (states j) (states (j + 1))) ∧
      Returns K v (states k) := by
  apply terminates K P v w
  intro z hz
  rcases hbranch z hz with hr | hp
  · exact Or.inl hr
  · obtain ⟨hp⟩ := hp
    exact Or.inr (hp.complete hK)

/-- Section 3, proof of `lem: dominate`: counting the final returning iteration
adds one initial Core call, but no further Repair call. Shrinking Core calls are
counted separately by `DominateShrinking`. -/
theorem outer_iteration_bound {n : ℕ} {C : Piece} {K : CoreProtocol}
    {P : RepairProtocol} {v : Fin n → Valuation}
    (states : ℕ → RecordedAllocationResult n C) (k : ℕ)
    (h : ∀ j < k, Continues K P v (states j) (states (j + 1))) :
    k ≤ n ^ 2 ∧ k + 1 ≤ remaining v (states 0) + 1 ∧ k + 1 ≤ n ^ 2 + 1 := by
  have := trace_bound states k h
  omega

end CakeCuttingPsomas.DominateTermination

