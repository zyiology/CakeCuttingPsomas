module

public import CakeCuttingPsomas.BaseCases
public import CakeCuttingPsomas.Dominate

set_option linter.style.header false

/-! # Divide, conditional on Dominate

The protocol and strong-induction argument of Section 2 (`algo:divide` and
`thm: main theorem` in `paper/main.tex`). `DominateProtocol.Correct` is an
explicit hypothesis; the domination subroutine remains to be implemented.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas.RWProtocol

/-- Section 2's `Divide`, parameterized by a domination protocol. Recursion
strictly decreases the number of agents. The group-size guard makes the protocol
well-founded on arbitrary answer branches; `DominateProtocol.Correct` guarantees
that every legal execution takes the recursive branch. -/
def divide (D : DominateProtocol) (n : ℕ) (hn : 0 < n)
    (s : RecordedState n) (C : Piece) : RWProtocol n (Allocation n C) := by
  classical
  by_cases h1 : n = 1
  · subst n
    exact divideOne C
  · by_cases h2 : n = 2
    · subst n
      exact divideTwo s C
    · exact (D n (by omega) s C).bind (fun r ↦
        if hm : 0 < r.group.card ∧ r.group.card < n then
          ((divide D r.group.card hm.1 (r.state.restrict r.inclusion) r.residue).relabel
            r.inclusion).map (fun Y ↦ r.allocation.combineRecursive Y r.agents r.residue_eq)
        else .done r.allocation)
termination_by n

/-- Section 2's main theorem (`thm: main theorem`), conditional on `lem: dominate`:
`Divide` returns a complete envy-free allocation on any compatible ordered cake
with correct inherited records. Its count is at most the paper's sum of one
possible domination call per remaining size and the terminal base-case cost. -/
theorem divide_runs (D : DominateProtocol) (hD : D.Correct) :
    ∀ (n : ℕ) (hn : 0 < n) (s : RecordedState n) (C : Piece) (v : Fin n → Valuation),
      s.Correct v → s.Compatible C →
      ∃ A count, (divide D n hn s C).Runs v A count ∧
        A.Complete ∧ A.EnvyFree v ∧ count ≤ divideQueryCost n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn s C v hs hC
    by_cases h1 : n = 1
    · subst n
      obtain ⟨hrun, hcomplete, hef⟩ := divideOne_runs C v
      refine ⟨Allocation.single C, 0, ?_, hcomplete, hef, by simp⟩
      rw [divide]
      exact hrun
    · by_cases h2 : n = 2
      · subst n
        obtain ⟨A, count, hrun, hcomplete, hef, hc⟩ := divideTwo_runs hs C hC
        refine ⟨A, count, ?_, hcomplete, hef, by simpa using hc⟩
        rw [divide]
        exact hrun
      · have h3 : 3 ≤ n := by omega
        obtain ⟨r, cD, hrunD, hs', hR, hXef, hE, hcD⟩ := hD n h3 s C v hs hC
        have hm := r.group_size v hE
        obtain ⟨Y, cY, hrunY, hYcomplete, hYef, hcY⟩ :=
          ih r.group.card hm.2 hm.1 (r.state.restrict r.inclusion) r.residue
            (v ∘ r.inclusion) (RecordedState.correct_restrict hs' r.inclusion) hR
        have hcombine := Allocation.complete_envyFree_combineRecursive r.allocation Y
          v r.agents r.residue_eq hXef hE hYcomplete hYef
        refine ⟨r.allocation.combineRecursive Y r.agents r.residue_eq, cD + cY,
          ?_, hcombine.1, hcombine.2, ?_⟩
        · rw [divide]
          simp only [dite_eq_right h1, dite_eq_right h2]
          apply hrunD.bind
          simp only [dite_eq_left hm]
          exact hrunY.relabel.map _
        · exact (Nat.add_le_add hcD hcY).trans (divideQueryCost_step h3 hm.2)

/-- Section 2's explicit query bound (`thm: main theorem`), conditional on
`Dominate`. This recursive statement includes empty cakes and arbitrary
unnormalized or zero valuations, provided their inherited records are correct. -/
theorem divide_runs_bounded (D : DominateProtocol) (hD : D.Correct)
    (n : ℕ) (hn : 0 < n) (s : RecordedState n) (C : Piece) (v : Fin n → Valuation)
    (hs : s.Correct v) (hC : s.Compatible C) :
    ∃ A count, (divide D n hn s C).Runs v A count ∧
      A.Complete ∧ A.EnvyFree v ∧ count ≤ queryBound n := by
  obtain ⟨A, count, hrun, hcomplete, hef, hc⟩ := divide_runs D hD n hn s C v hs hC
  exact ⟨A, count, hrun, hcomplete, hef, hc.trans (divideQueryCost_le_queryBound n)⟩

end CakeCuttingPsomas.RWProtocol
