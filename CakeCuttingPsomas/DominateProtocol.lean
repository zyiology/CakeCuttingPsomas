module

public import CakeCuttingPsomas.Dominate
public import CakeCuttingPsomas.DominateSearch
public import CakeCuttingPsomas.DominateTermination
public import CakeCuttingPsomas.DominateCost

set_option linter.style.header false

/-! # Assembly of Section 3's Dominate protocol

Algorithm `alg:dominate` of `paper/main.tex`, conditional on the implementations
of Core and Repair. Searches inspect inherited records only. Bounded fuel makes
the query tree total even on answers outside legal executions.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.DominateAssembly

/-- Package a returning allocation with its dominated-group candidate. -/
def output {n : ℕ} {C : Piece} (w : RecordedAllocationResult n C)
    (E : Finset (Fin n)) : DominateResult n C :=
  ⟨w.allocation, E, w.state, w.residue, w.residue_eq⟩

/-- The returning guarantees, including inherited representations for composition. -/
def OutputCorrect {n : ℕ} {C : Piece} (s : RecordedState n) (v : Fin n → Valuation)
    (r : DominateResult n C) : Prop :=
  r.state.Correct v ∧
    (RecordedAllocationResult.mk r.allocation r.state r.residue r.residue_eq).Inherits s ∧
    r.allocation.EnvyFree v ∧ r.allocation.DominatedGroup v (↑r.group)

/-- Section 3, `alg:dominate`: one initial Core call, the two recorded searches,
and, when required, Repair followed by shrinking. Failed searches on arbitrary
answers return a candidate; correctness proves those branches unreachable. -/
def step (K : CoreProtocol) (P : RepairProtocol) (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n) {C : Piece} (w : RecordedAllocationResult n C) :
    RWProtocol n (DominateResult n C ⊕ RecordedAllocationResult n C) :=
  (K n (by omega) w.state w.residue c).bind fun f ↦
    match DominateSearch.group f.state (w.appendCore f).allocation with
    | some E => .done (.inl (output (w.appendCore f) E))
    | none =>
      match DominateSearch.choice f.state w.allocation f.allocation with
      | none => .done (.inl (output (w.appendCore f) ∅))
      | some q =>
        let D := DominateChoice.permutedCombined w.allocation f.allocation w.residue_eq q.2.2.2
        let α := DominateChoice.scale n q.1.val
        let threshold := α * f.state.supportValue q.2.1 f.allocation.residue
        (P.onRepresented n (by omega) f.state C D α).bind fun r ↦
          (DominateShrinking.run K n (by omega) q.2.1 threshold
            (DominateShrinking.budget n α) r.toRecordedAllocationResult).map
              (fun z ↦ .inr z.1)

/-- Section 3, proof of `lem: dominate`: the recorded searches discharge branch
availability and produce either a correct return or an actual completed iteration.
All constituent executions and their query counts are retained. -/
theorem step_correct (K : CoreProtocol) (hK : K.Correct)
    (P : RepairProtocol) (hP : P.Correct) {n : ℕ} (hn : 3 ≤ n) (c : Fin n)
    {C : Piece} (w : RecordedAllocationResult n C) {s : RecordedState n}
    (v : Fin n → Valuation) (hs : w.state.Correct v) (hi : w.Inherits s)
    (hC : w.state.Represents C.support) (hw : w.allocation.EnvyFree v) :
    ∃ out count, (step K P n hn c w).Runs v out count ∧
      match out with
      | .inl r => DominateTermination.Returns K v w ∧
          OutputCorrect s v r ∧ count ≤ coreQueryBound n
      | .inr z => Nonempty (DominateTermination.Iteration K P v w z) ∧
          count ≤ DominateCost.continuationBudget n := by
  classical
  obtain ⟨f, cf, hf, hfs, hfi, hfef, hshare, hcf⟩ :=
    hK n (by omega) w.state w.residue c v hs hi.2.2
  have hai := w.appendCore_inherits f hi hfi
  have haef := (w.appendCore_envyFree_advantage f v hw hfef).1
  have haR : f.state.Represents (w.appendCore f).allocation.residue :=
    ⟨f.residue, hai.2.2, (w.appendCore f).residue_eq⟩
  cases hg : DominateSearch.group f.state (w.appendCore f).allocation with
  | some E =>
    have hgroup := DominateSearch.group_some hfs hai.2.1 haR hg
    refine ⟨.inl (output (w.appendCore f) E), cf, ?_,
      ⟨hn, c, f, cf, E, hf, hfs, hfi, hfef, hgroup⟩,
      ⟨hfs, hai, haef, hgroup⟩, hcf⟩
    unfold step
    apply RWProtocol.Runs.bind (d := 0) hf
    simp only [hg]
    exact .done _
  | none =>
    have hno := DominateSearch.group_none hfs hai.2.1 haR hg
    have hno' : ∀ E : Set (Fin n),
        ¬ (DominateChoice.combined w.allocation f.allocation w.residue_eq).DominatedGroup v E :=
      hno
    obtain ⟨hpos, hex⟩ := DominateChoice.exists_choice w.allocation f.allocation hn
      w.residue_eq v c hw hfef hshare hno'
    have hx : ∀ j, f.state.Represents (w.allocation.bundle j).support :=
      fun j ↦ hfi.1.represents (hi.2.1 j)
    have hxr : f.state.Represents w.allocation.residue := by
      rw [← w.residue_eq]
      exact hfi.1 w.residue hi.2.2
    have hyr : f.state.Represents f.allocation.residue :=
      ⟨f.residue, hfi.2.2, f.residue_eq⟩
    obtain ⟨q, hq, hspec⟩ :=
      DominateSearch.choice_available hfs hx hxr hfi.2.1 hyr hex
    let D := DominateChoice.permutedCombined w.allocation f.allocation w.residue_eq q.2.2.2
    have hd : ∀ j, f.state.Represents (D.bundle j).support := by
      intro j
      rw [DominateChoice.permutedCombined_bundle_support]
      exact (hx j).union (hfi.2.1 (q.2.2.2 j))
        ((w.allocation.disjoint_bundle_residue j).mono_right
          ((f.allocation.contained _).trans w.residue_eq.subset))
    obtain ⟨hα, hα', hpositive, halmost⟩ :=
      hspec.repair_preconditions hn w.residue_eq hw hfef hpos
    obtain ⟨r, cr, hr, hrs, hri, href, hadd, hcr⟩ :=
      P.onRepresented_correct hP (by omega) f.state C D (DominateChoice.scale n q.1.val)
        v hfs (hfi.1.represents hC) hd hα hα' hpositive halmost
    have hinit : (v q.2.1).value r.residue.support ≤ (v q.2.1).value f.allocation.residue := by
      apply (v q.2.1).value_mono r.residue.measurableSet_support
        f.allocation.measurableSet_residue _ f.allocation.residue_subset_unit
      rw [r.residue_removed, DominateChoice.permutedCombined_residue]
      exact Set.sdiff_subset
    have hriSelf : r.toRecordedAllocationResult.Inherits r.state :=
      ⟨RecordedState.refines_refl _, hri.2⟩
    obtain ⟨z, k, cz, hz, hzs, hzi, he, hk, hcz, _hgeom, hstop⟩ :=
      DominateShrinking.shrink_correct K hK (by omega) q.2.1 hα
        ((v q.2.1).value_nonneg f.allocation.measurableSet_residue
          f.allocation.residue_subset_unit)
        r.toRecordedAllocationResult v hrs hriSelf href hinit
    have hit : DominateTermination.Iteration K P v w z := {
      agents_lower := hn
      core := f
      cutter := c
      coreCount := cf
      coreRuns := hf
      old_envyFree := hw
      core_correct := hfs
      core_envyFree := hfef
      core_share := hshare
      core_inherits := hfi
      no_group := hno'
      exponent := q.1.val
      distinguished := q.2.1
      other := q.2.2.1
      permutation := q.2.2.2
      choice := hspec
      repair := r
      repairCount := cr
      repairRuns := hr
      repair_correct := hrs
      repair_envyFree := href
      repair_inherits := hri
      additions := hadd
      shrinkCalls := k
      shrinkCount := cz
      shrinkRuns := hz
      extension := he
      stopped := hstop
      correct := hzs
      inherits := hzi }
    refine ⟨.inr z, cf + (cr + cz), ?_, ⟨hit⟩, ?_⟩
    · have hz' := hz.map (fun out ↦ Sum.inr (α := DominateResult n C) out.1)
      rw [← f.state.supportValue_eq hfs hyr q.2.1] at hz'
      unfold step
      exact hf.bind (by simpa only [hg, hq] using hr.bind hz')
    · have hcr' := DominateCost.repair_count_le hn hspec.exponent_upper hcr
      have hk' := hk.trans (DominateShrinking.budget_scale_le hn hspec.exponent_upper)
      have hcz' := hcz.trans (Nat.mul_le_mul_right (coreQueryBound n) hk')
      change cz ≤ DominateCost.shrinkBudget n * coreQueryBound n at hcz'
      unfold DominateCost.continuationBudget
      omega

/-- Section 3, proof of `lem: dominate`: the recorded implementation supplies
the explicit branch-availability hypothesis of `terminates_of_prepared`. -/
theorem branches_available (K : CoreProtocol) (hK : K.Correct)
    (P : RepairProtocol) (hP : P.Correct) {n : ℕ} (hn : 3 ≤ n) (c : Fin n)
    {C : Piece} (w : RecordedAllocationResult n C) {s : RecordedState n}
    (v : Fin n → Valuation) (hs : w.state.Correct v) (hi : w.Inherits s)
    (hC : w.state.Represents C.support) (hw : w.allocation.EnvyFree v) :
    DominateTermination.Returns K v w ∨
      Nonempty (DominateTermination.PreparedIteration K P v w) := by
  obtain ⟨out, _count, _hrun, hcorrect⟩ := step_correct K hK P hP hn c w v hs hi hC hw
  cases out with
  | inl r => exact Or.inl hcorrect.1
  | inr z =>
    obtain ⟨hit⟩ := hcorrect.1
    exact Or.inr ⟨hit.toPreparedIteration⟩

/-- Section 3, `alg:dominate`: a bounded outer loop. The fuel-zero branch is
defined for arbitrary answers, and is unreachable on the legal initial run. -/
def run (K : CoreProtocol) (P : RepairProtocol) (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n) {C : Piece} : ℕ → RecordedAllocationResult n C →
      RWProtocol n (DominateResult n C)
  | 0, w => .done (output w ∅)
  | fuel + 1, w => (step K P n hn c w).bind fun out ↦
      match out with
      | .inl r => .done r
      | .inr z => run K P n hn c fuel z

/-- Section 3, proof of `lem: dominate`: the domination-count measure ensures
a return with the supplied fuel. The protocol itself never inspects valuations
or the measure, and query counts add along its actual execution. -/
theorem run_correct (K : CoreProtocol) (hK : K.Correct)
    (P : RepairProtocol) (hP : P.Correct) {n : ℕ} (hn : 3 ≤ n) (c : Fin n)
    (fuel : ℕ) {C : Piece} (w : RecordedAllocationResult n C) {s : RecordedState n}
    (v : Fin n → Valuation) (hs : w.state.Correct v) (hi : w.Inherits s)
    (hC : w.state.Represents C.support) (hw : w.allocation.EnvyFree v)
    (hcapacity : DominateTermination.remaining v w < fuel) :
    ∃ r count, (run K P n hn c fuel w).Runs v r count ∧ OutputCorrect s v r ∧
      count ≤ (fuel - 1) * DominateCost.continuationBudget n + coreQueryBound n := by
  induction fuel generalizing w with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨out, count, hout, hcorrect⟩ := step_correct K hK P hP hn c w v hs hi hC hw
    cases out with
    | inl r =>
      refine ⟨r, count, ?_, hcorrect.2.1, ?_⟩
      · unfold run
        apply RWProtocol.Runs.bind (d := 0) hout
        exact .done r
      · simpa only [Nat.add_sub_cancel] using
          hcorrect.2.2.trans (Nat.le_add_left (coreQueryBound n)
            (fuel * DominateCost.continuationBudget n))
    | inr z =>
      obtain ⟨hit⟩ := hcorrect.1
      have hp := hit.progress
      have hlt := DominateTermination.remaining_lt (show
        DominateTermination.Continues K P v w z from ⟨hit⟩)
      have hfuel : 0 < fuel := by omega
      obtain ⟨r, count', hr, hrc, hc⟩ := ih z hp.1
        ⟨hi.1.trans hp.2.1.1, hp.2.1.2⟩ (hp.2.1.1.represents hC) hp.2.2.1 (by omega)
      refine ⟨r, count + count', ?_, hrc, ?_⟩
      · unfold run
        exact hout.bind hr
      · simp only [Nat.add_sub_cancel]
        calc
          count + count' ≤ DominateCost.continuationBudget n +
              ((fuel - 1) * DominateCost.continuationBudget n + coreQueryBound n) :=
            Nat.add_le_add hcorrect.2 hc
          _ = fuel * DominateCost.continuationBudget n + coreQueryBound n := by
            have hf : fuel - 1 + 1 = fuel := Nat.sub_add_cancel hfuel
            nlinarith

/-- The initial empty allocation and unchanged records of `alg:dominate`. -/
def initial {n : ℕ} (s : RecordedState n) (C : Piece) : RecordedAllocationResult n C where
  allocation := {
    bundle := fun _ ↦ Piece.empty
    contained := by simp
    disjoint := by simp }
  state := s
  residue := C
  residue_eq := by simp [Allocation.residue, Allocation.allocated]

/-- Section 3's `alg:dominate`, chosen independently of valuations. The initial
cutter is fixed throughout the outer loop, as in the paper. -/
def protocol (K : CoreProtocol) (P : RepairProtocol) : DominateProtocol :=
  fun n hn s C ↦ run K P n hn ⟨0, by omega⟩ (n ^ 2 + 1) (initial s C)

/-- Section 3, proof of `lem: dominate`: conditional on Core and Repair, the
assembled protocol returns a dominated group with correct inherited records
within the full call-count budget, with no branch-availability assumption. -/
theorem protocol_runs (K : CoreProtocol) (hK : K.Correct)
    (P : RepairProtocol) (hP : P.Correct) (n : ℕ) (hn : 3 ≤ n)
    (s : RecordedState n) (C : Piece) (v : Fin n → Valuation)
    (hs : s.Correct v) (hC : s.Compatible C) :
    ∃ r count, (protocol K P n hn s C).Runs v r count ∧ OutputCorrect s v r ∧
      count ≤ DominateCost.totalBudget n := by
  have hi : (initial s C).Inherits s :=
    ⟨RecordedState.refines_refl s, fun _ ↦ by simpa only [initial, Piece.support_empty]
      using s.represents_empty, hC⟩
  have hef : (initial s C).allocation.EnvyFree v := fun _ _ ↦ le_rfl
  obtain ⟨r, count, hr, hrc, hc⟩ := run_correct K hK P hP hn ⟨0, by omega⟩
    (n ^ 2 + 1) (initial s C) v hs hi ⟨C, hC, rfl⟩ hef (by
      unfold DominateTermination.remaining
      omega)
  exact ⟨r, count, hr, hrc, by
    simpa only [Nat.add_sub_cancel, DominateCost.totalBudget] using hc⟩

/-- Section 3's `lem: dominate`: Core and Repair satisfying their paper
contracts yield a correct Dominate protocol with the full explicit query bound.
No normalization, positive-value, or nonempty-cake assumptions are added. -/
theorem protocol_correct (K : CoreProtocol) (hK : K.Correct)
    (P : RepairProtocol) (hP : P.Correct) : (protocol K P).Correct := by
  intro n hn s C v hs hC
  obtain ⟨r, count, hr, ⟨hrs, hri, href, hgroup⟩, hc⟩ :=
    protocol_runs K hK P hP n hn s C v hs hC
  exact ⟨r, count, hr, hrs, hri.2.2, href, hgroup,
    hc.trans (DominateCost.totalBudget_le hn)⟩

end CakeCuttingPsomas.DominateAssembly
