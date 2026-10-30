module

public import CakeCuttingPsomas.Permute
public import CakeCuttingPsomas.CandidateProtocol
public import CakeCuttingPsomas.CandidateCompactness
public import Mathlib.Data.Fintype.Perm

set_option linter.style.header false

/-! # Section 5's complete Permute search

Algorithm `alg:permute` enumerates the two orders and tests candidates using
inherited records. The proof-only compactness construction guarantees success.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas

namespace PermuteAssembly

open CandidateConstruction
attribute [local instance] Classical.propDecidable

abbrev Guess (n : ℕ) := Equiv.Perm (Fin n) × Equiv.Perm (Fin n)

/-- Algorithm `alg:permute`: every agent order and every input-label order. -/
def guesses (n : ℕ) : List (Guess n) := (Finset.univ : Finset (Guess n)).toList

@[simp] theorem mem_guesses {n : ℕ} (g : Guess n) : g ∈ guesses n := by
  simp [guesses]

/-- Section 5, `lem:permute`: there are exactly `(n!)²` guesses. -/
theorem guesses_length (n : ℕ) : (guesses n).length = (Nat.factorial n) ^ 2 := by
  simp [guesses, Fintype.card_prod, Fintype.card_perm, pow_two]

/-- A candidate together with the orders used to construct it. -/
structure Output (n : ℕ) where
  guess : Guess n
  result : Result n

/-- Algorithm `alg:permute`: all envy comparisons use the inherited cell table. -/
def passes {n : ℕ} (g : Guess n) (r : Result n) : Prop :=
  ∀ i j, r.state.supportValue (g.1 i) (r.bundles j).support ≤
    r.state.supportValue (g.1 i) (r.bundles i).support

/-- The recorded comparison is exactly envy-freeness on valid candidate outputs. -/
theorem passes_iff {n : ℕ} (g : Guess n) (r : Result n) (v : Fin n → Valuation)
    (hs : r.state.Correct v) (hB : ∀ j, r.state.Represents (r.bundles j).support) :
    passes g r ↔ ∀ i j, (v (g.1 i)).value (r.bundles j).support ≤
      (v (g.1 i)).value (r.bundles i).support := by
  unfold passes
  simp_rw [r.state.supportValue_eq hs (hB _)]

/-- Algorithm `alg:permute`: restart each guess from the original pieces, keeping
all record refinements from failed guesses. The empty branch is unreachable on
valid inputs when the list contains a successful guess. -/
def search {n : ℕ} (inputs : Fin n → Piece) : List (Guess n) → RecordedState n →
    RWProtocol n (Output n)
  | [], s => .done ⟨(Equiv.refl _, Equiv.refl _), ⟨s, fun _ ↦ Piece.empty⟩⟩
  | g :: gs, s => (run g.1 g.2 inputs s).bind fun r ↦
      if passes g r then .done ⟨g, r⟩ else search inputs gs r.state

/-- Guarantees of a successful search, expressed in the guessed position order. -/
structure Valid {n : ℕ} (v : Fin n → Valuation) (inputs : Fin n → Piece)
    (o : Output n) : Prop where
  correct : o.result.state.Correct v
  aligned : ∀ j, ∃ Q, o.result.state.Compatible Q ∧ (o.result.bundles j).SameTraversal Q
  candidate : IsCandidate (v ∘ o.guess.1) (inputs ∘ o.guess.2) o.result.bundles
  envyFree : ∀ i j, (v (o.guess.1 i)).value (o.result.bundles j).support ≤
    (v (o.guess.1 i)).value (o.result.bundles i).support
  last_trim : ∀ j, (o.result.bundles j).support ≠ (inputs (o.guess.2 j)).support →
    ∃ i : Fin n, i < j ∧ (v (o.guess.1 i)).value (o.result.bundles j).support =
      (v (o.guess.1 i)).value (o.result.bundles i).support

/-- Section 5, `lem:permute`: a finite search containing a successful mathematical
candidate returns a successful recorded candidate, with additive query accounting. -/
theorem search_correct {n : ℕ} (inputs : Fin n → Piece) (gs : List (Guess n))
    (s : RecordedState n) (v : Fin n → Valuation) (hs : s.Correct v)
    (hinputs : ∀ j, ∃ Q, s.Compatible Q ∧ (inputs j).SameTraversal Q)
    (hsuccess : ∃ g ∈ gs, ∀ i j,
      (v (g.1 i)).value (candidate (v ∘ g.1) (inputs ∘ g.2) j).support ≤
      (v (g.1 i)).value (candidate (v ∘ g.1) (inputs ∘ g.2) i).support) :
    ∃ o count, (search inputs gs s).Runs v o count ∧
      count ≤ gs.length * ((n + 1) * n.choose 2) ∧
      s.TraversalRefines o.result.state ∧ Valid v inputs o := by
  induction gs generalizing s with
  | nil => obtain ⟨g, hg, _⟩ := hsuccess; simp at hg
  | cons g gs ih =>
    obtain ⟨r, a, ha, hca, hrs, href, halign, hcand⟩ :=
      run_correct g.1 g.2 inputs s v hs hinputs
    have hB : ∀ j, r.state.Represents (r.bundles j).support := by
      intro j
      obtain ⟨Q, hQ, he⟩ := halign j
      exact ⟨Q, hQ, he.support_eq.symm⟩
    by_cases hp : passes g r
    · refine ⟨⟨g, r⟩, a, ?_, ?_, href, ?_⟩
      · change ((run g.1 g.2 inputs s).bind _).Runs v _ _
        have hb : (if passes g r then RWProtocol.done (⟨g, r⟩ : Output n)
            else search inputs gs r.state).Runs v ⟨g, r⟩ 0 := by
          rw [ite_eq_left hp]
          exact .done _
        simpa only [Nat.add_zero] using ha.bind
          (f := fun r ↦ if passes g r then .done ⟨g, r⟩ else search inputs gs r.state) hb
      · simp only [List.length_cons]
        nlinarith
      · exact ⟨hrs, halign, hcand, (passes_iff g r v hrs hB).mp hp,
          runs_last_trim g.1 g.2 inputs hs hinputs ha⟩
    · have htail : ∃ g ∈ gs, ∀ i j,
          (v (g.1 i)).value (candidate (v ∘ g.1) (inputs ∘ g.2) j).support ≤
          (v (g.1 i)).value (candidate (v ∘ g.1) (inputs ∘ g.2) i).support := by
        obtain ⟨g', hg', hef⟩ := hsuccess
        rcases List.mem_cons.mp hg' with he | he
        · subst g'
          have heq := hcand.support_unique (candidate_spec _ _)
            (fun _ ↦ Piece.SameTraversal.refl _)
          exact (hp ((passes_iff g r v hrs hB).mpr (by simp_rw [heq]; exact hef))).elim
        · exact ⟨g', he, hef⟩
      obtain ⟨o, b, hb, hcb, href', hv⟩ :=
        ih r.state hrs (fun j ↦ href.preserves_along (hinputs j)) htail
      refine ⟨o, a + b, ?_, ?_, href.trans href', hv⟩
      · change ((run g.1 g.2 inputs s).bind _).Runs v _ _
        apply ha.bind
        simpa only [ite_eq_right hp] using hb
      · simp only [List.length_cons]
        nlinarith

/-- Total output on malformed inputs or invalid answer branches. -/
def emptyResult {n : ℕ} (s : RecordedState n) (C : Piece) : PermuteResult n C where
  allocation := {
    bundle := fun _ ↦ Piece.empty
    contained := by simp [Piece.support_empty]
    disjoint := by simp [Piece.support_empty] }
  state := s
  residue := C
  residue_eq := by simp [Allocation.residue, Allocation.allocated, Piece.support_empty]
  assignment := Equiv.refl _

/-- Algorithm `alg:permute`: package the original suffix traversals and exact
recorded residue. The guards inspect only geometry and inherited records. -/
def finish {n : ℕ} (C : Piece) (inputs : Fin n → Piece) (o : Output n) :
    PermuteResult n C :=
  if hS : ∀ j, (o.result.bundles j).IsSuffix (inputs (o.guess.2 j)) then
    if hd : ∀ i j, i ≠ j → Disjoint (inputs i).support (inputs j).support then
      if hcover : (⋃ j, (inputs j).support) = C.support then
        let A := o.result.allocation o.guess.1 o.guess.2 inputs hS hd hcover
        if hres : o.result.state.Represents A.residue then
          { allocation := A
            state := o.result.state
            residue := o.result.state.represent A.residue
            residue_eq := o.result.state.support_represent hres
            assignment := o.guess.2 * o.guess.1.symm }
        else emptyResult o.result.state C
      else emptyResult o.result.state C
    else emptyResult o.result.state C
  else emptyResult o.result.state C

/-- Section 5, `alg:permute`: try the finitely many order pairs, using only
recorded values for tests and retaining refinements between failed guesses. -/
def protocol : PermuteProtocol := fun n _ s C inputs ↦
  (search inputs (guesses n) s).map (finish C inputs)

/-- Section 5, proof of `lem:permute` (ii): the earliest member of any nonempty
set of proper-suffix recipients has an indifferent observer outside that set. -/
theorem Valid.indifference {n : ℕ} {v : Fin n → Valuation} {inputs : Fin n → Piece}
    {o : Output n} (hv : Valid v inputs o)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (hproper : ∀ i ∈ S,
      (o.result.bundles (o.guess.1.symm i)).support ≠
        (inputs (o.guess.2 (o.guess.1.symm i))).support) :
    ∃ i ∈ S, ∃ j ∉ S,
      (v j).value (o.result.bundles (o.guess.1.symm i)).support =
        (v j).value (o.result.bundles (o.guess.1.symm j)).support := by
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image (fun i ↦ o.guess.1.symm i) hS
  obtain ⟨j, hj, he⟩ := hv.last_trim (o.guess.1.symm i) (hproper i hi)
  refine ⟨i, hi, o.guess.1 j, ?_, ?_⟩
  · intro hmem
    have hle := hmin _ hmem
    simp only [Equiv.symm_apply_apply] at hle
    exact (not_lt_of_ge hle) hj
  · simpa only [Equiv.symm_apply_apply] using he

/-- Section 5, `lem:permute`: finite search succeeds, returns suffixes with both
additional guarantees, inherits exact records, and uses at most
`(n+1) * n.choose 2 * (n!)²` Robertson--Webb queries. -/
theorem protocol_correct : protocol.Correct := by
  intro n hn s C inputs v hs hinputs hd hcover
  obtain ⟨agents, pieces, hef⟩ := exists_envyFree_guess v C inputs hd hcover
  obtain ⟨o, count, hr, hcount, href, hv⟩ :=
    search_correct inputs (guesses n) s v hs hinputs
      ⟨(agents, pieces), mem_guesses _, hef⟩
  have hS : ∀ j, (o.result.bundles j).IsSuffix (inputs (o.guess.2 j)) :=
    hv.candidate.suffix
  let A := o.result.allocation o.guess.1 o.guess.2 inputs hS hd hcover
  have hB : ∀ j, o.result.state.Represents (A.bundle j).support := by
    intro j
    obtain ⟨Q, hQ, he⟩ := hv.aligned (o.guess.1.symm j)
    exact ⟨Q, hQ, he.support_eq.symm⟩
  have hC : o.result.state.Represents C.support := by
    rw [← hcover]
    apply RecordedState.represents_iUnion inputs _ hd
    intro j
    obtain ⟨Q, hQ, he⟩ := href.preserves_along (hinputs j)
    exact ⟨Q, hQ, he.support_eq.symm⟩
  have hres : o.result.state.Represents A.residue :=
    hC.diff (RecordedState.represents_iUnion A.bundle hB A.disjoint)
  let out : PermuteResult n C := {
    allocation := A
    state := o.result.state
    residue := o.result.state.represent A.residue
    residue_eq := o.result.state.support_represent hres
    assignment := o.guess.2 * o.guess.1.symm }
  have hfinish : finish C inputs o = out := by
    simp only [finish, dite_eq_left hS, dite_eq_left hd, dite_eq_left hcover,
      dite_eq_left hres, out, A]
  refine ⟨out, count, ?_, hv.correct, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((search inputs (guesses n) s).map (finish C inputs)).Runs v out count
    rw [← hfinish]
    exact hr.map _
  · exact ⟨href.refines, hB, o.result.state.compatible_represent _⟩
  · intro i j
    simpa only [out, A, Result.allocation, Equiv.apply_symm_apply] using
      hv.envyFree (o.guess.1.symm i) (o.guess.1.symm j)
  · intro i
    exact hS (o.guess.1.symm i)
  · refine ⟨o.guess.1 ⟨0, hn⟩, ?_⟩
    simpa only [out, A, Result.allocation, Equiv.Perm.mul_apply,
      Equiv.symm_apply_apply, Function.comp_apply] using hv.candidate.first_support hn
  · intro S hnonempty hproper
    exact hv.indifference S hnonempty hproper
  · calc
      count ≤ (guesses n).length * ((n + 1) * n.choose 2) := hcount
      _ = permuteQueryBound n := by rw [guesses_length]; unfold permuteQueryBound; ring

end PermuteAssembly
end CakeCuttingPsomas
