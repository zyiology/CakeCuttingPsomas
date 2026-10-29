module

public import CakeCuttingPsomas.PrefixProtocol

set_option linter.style.header false

/-! # The terminal cases of Divide

The one- and two-agent branches of Section 2's `Divide` (`algo:divide` and
`thm: main theorem` in `paper/main.tex`). Input pieces may be empty, their
intervals may have any traversal order, and valuations need not be normalized.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas

namespace Allocation

/-- Section 2's one-agent branch gives the whole input cake to its sole agent. -/
def single (C : Piece) : Allocation 1 C where
  bundle _ := C
  contained _ := Set.Subset.rfl
  disjoint i j hij := (hij (Subsingleton.elim i j)).elim

/-- Completeness of the one-agent branch of `Divide` (`algo:divide`, Section 2). -/
theorem complete_single (C : Piece) : (single C).Complete := by
  ext x
  simp [allocated, single]

/-- Envy-freeness of the one-agent branch of `Divide` (`thm: main theorem`, Section 2). -/
theorem envyFree_single (C : Piece) (v : Fin 1 → Valuation) : (single C).EnvyFree v :=
  fun _ _ ↦ le_rfl

/-- Give the two sides of an ordered split to the two agents. When `choosePrefix`
is true, agent 1 (the chooser) receives the prefix; otherwise she receives the suffix.
Ties will be resolved in favor of the prefix by the protocol. -/
def cutAndChooseAllocation (C : Piece) (r : ℝ) (choosePrefix : Bool) : Allocation 2 C where
  bundle i := if i = 1 then
    (if choosePrefix then C.prefixAt r else C.suffixAt r)
    else (if choosePrefix then C.suffixAt r else C.prefixAt r)
  contained i := by
    split_ifs <;> first | exact C.prefix_subset r | exact C.suffix_subset r
  disjoint i j hij := by
    fin_cases i <;> fin_cases j <;> cases choosePrefix <;>
      simp_all only [ne_eq, not_true_eq_false, Fin.zero_eta, Fin.isValue, zero_ne_one,
        ↓reduceIte, Bool.false_eq_true, Fin.mk_one, Piece.support_suffix] <;>
      first | exact Set.disjoint_sdiff_right | exact Set.disjoint_sdiff_right.symm

/-- Exact completeness of the two-agent branch of `Divide` (`algo:divide`, Section 2). -/
theorem complete_cutAndChooseAllocation (C : Piece) (r : ℝ) (b : Bool) :
    (cutAndChooseAllocation C r b).Complete := by
  have h : (cutAndChooseAllocation C r b).allocated =
      (C.prefixAt r).support ∪ (C.suffixAt r).support := by
    ext x
    simp only [allocated, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> cases b <;> simp_all [cutAndChooseAllocation]
    · intro hx
      cases b <;> rcases hx with hp | hs
      · exact ⟨0, by simpa [cutAndChooseAllocation] using hp⟩
      · exact ⟨1, by simpa [cutAndChooseAllocation] using hs⟩
      · exact ⟨1, by simpa [cutAndChooseAllocation] using hp⟩
      · exact ⟨0, by simpa [cutAndChooseAllocation] using hs⟩
  rw [Complete, h, C.prefix_union_suffix]

/-- Correctness of cut-and-choose in Section 2 (`algo:divide`, `thm: main theorem`):
the cutter values both sides equally, and the chooser gets a weakly preferred side. -/
theorem envyFree_cutAndChooseAllocation (C : Piece) (r : ℝ) (b : Bool)
    (v : Fin 2 → Valuation)
    (hcut : (v 0).value (C.prefixAt r).support = (v 0).value (C.suffixAt r).support)
    (hchoose : b = true ↔
      (v 1).value (C.suffixAt r).support ≤ (v 1).value (C.prefixAt r).support) :
    (cutAndChooseAllocation C r b).EnvyFree v := by
  have hweak : b = false →
      (v 1).value (C.prefixAt r).support ≤ (v 1).value (C.suffixAt r).support := by
    intro hb
    subst b
    have hnot : ¬(v 1).value (C.suffixAt r).support ≤
        (v 1).value (C.prefixAt r).support := by simpa using hchoose
    exact (lt_of_not_ge hnot).le
  intro i j
  fin_cases i <;> fin_cases j <;> cases b <;>
    simp_all [cutAndChooseAllocation]

end Allocation

namespace RWProtocol

/-- The one-agent terminal branch of `Divide` (Section 2). -/
def divideOne (C : Piece) : RWProtocol 1 (Allocation 1 C) := .done (Allocation.single C)

/-- Section 2 (`thm: main theorem`): one agent receives the whole cake, completely
and envy-freely, using exactly zero queries. No records or normalization are needed. -/
theorem divideOne_runs (C : Piece) (v : Fin 1 → Valuation) :
    (divideOne C).Runs v (Allocation.single C) 0 ∧
      (Allocation.single C).Complete ∧ (Allocation.single C).EnvyFree v :=
  ⟨.done _, Allocation.complete_single C, Allocation.envyFree_single C v⟩

/-- The two-agent terminal branch of `Divide` (Section 2). Agent 0 cuts at half
her recorded total; agent 1 chooses, with ties going to the prefix. All totals
and the chooser's suffix value use inherited records and subtraction. -/
def divideTwo (s : RecordedState 2) (C : Piece) : RWProtocol 2 (Allocation 2 C) :=
  (s.terminalPrefix 0 1 C (s.pieceValue 0 C / 2)).map (fun result ↦
    Allocation.cutAndChooseAllocation C result.1
      (decide (s.pieceValue 1 C - result.2 ≤ result.2)))

/-- Section 2's base case and query accounting (`algo:divide`, `thm: main theorem`):
cut-and-choose on any compatible ordered piece returns a complete envy-free
allocation using at most two queries. Correct inherited records suffice; no
normalization, positive value, or nonempty cake assumption is required. -/
theorem divideTwo_runs {s : RecordedState 2} {v : Fin 2 → Valuation}
    (hs : s.Correct v) (C : Piece) (hC : s.Compatible C) :
    ∃ A count, (divideTwo s C).Runs v A count ∧ A.Complete ∧ A.EnvyFree v ∧ count ≤ 2 := by
  have htotal := RecordedState.pieceValue_eq hs hC (0 : Fin 2)
  have hnonneg := (v 0).value_nonneg C.measurableSet_support C.support_subset_unit
  obtain ⟨r, a, count, hrun, hc, _, hhalf, ha, _⟩ :=
    RecordedState.terminalPrefix_runs hs 0 1 C hC (s.pieceValue 0 C / 2)
      (by rw [htotal]; positivity) (by rw [htotal]; linarith)
  let b := decide (s.pieceValue 1 C - a ≤ a)
  refine ⟨Allocation.cutAndChooseAllocation C r b, count, hrun.map _,
    Allocation.complete_cutAndChooseAllocation C r b, ?_, hc⟩
  apply Allocation.envyFree_cutAndChooseAllocation
  · have hsum := (v 0).value_prefix_add_suffix C r
    rw [htotal] at hhalf
    linarith
  · have hsum := (v 1).value_prefix_add_suffix C r
    have htotal' := RecordedState.pieceValue_eq hs hC (1 : Fin 2)
    simp only [b, decide_eq_true_eq, htotal', ha]
    constructor <;> intro h <;> linarith

end RWProtocol
end CakeCuttingPsomas
