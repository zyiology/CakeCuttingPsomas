module

public import CakeCuttingPsomas.Suffix

set_option linter.style.header false

/-! # Candidates for fixed agent and input-piece orders

Section 5, `eq:permute-caps` and `claim:containment`. Families are indexed by
positions in the two orders; labels and record states are absent from this
mathematical characterization.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas

/-- Section 5, `eq:permute-caps`: at each position the candidate is the greatest
suffix satisfying all earlier agents' caps, retaining zero-valued cake. -/
structure IsCandidate {n : ℕ} (v : Fin n → Valuation) (P Y : Fin n → Piece) : Prop where
  suffix : ∀ r, (Y r).IsSuffix (P r)
  caps : ∀ s r, s < r → (v s).value (Y r).support ≤ (v s).value (Y s).support
  greatest : ∀ r (T : Piece), T.IsSuffix (P r) →
    (∀ s, s < r → (v s).value T.support ≤ (v s).value (Y s).support) →
    T.support ⊆ (Y r).support

namespace IsCandidate

variable {n : ℕ} {v : Fin n → Valuation} {P Y : Fin n → Piece}

/-- Section 5, `eq:permute-caps`: membership below a candidate is equivalent to
satisfying its earlier-agent caps, for suffixes of the assigned input piece. -/
theorem subset_iff (h : IsCandidate v P Y) (r : Fin n) {T : Piece}
    (hT : T.IsSuffix (P r)) :
    T.support ⊆ (Y r).support ↔
      ∀ s, s < r → (v s).value T.support ≤ (v s).value (Y s).support := by
  constructor
  · intro hsub s hsr
    exact ((v s).value_mono T.measurableSet_support (Y r).measurableSet_support
      hsub (Y r).support_subset_unit).trans (h.caps s r hsr)
  · exact h.greatest r T hT

/-- Section 5, `lem:permute` (i): the first agent receives her input whole. -/
theorem first_support (h : IsCandidate v P Y) (hn : 0 < n) :
    (Y ⟨0, hn⟩).support = (P ⟨0, hn⟩).support := by
  apply Set.Subset.antisymm
  · obtain ⟨a, _, he⟩ := h.suffix ⟨0, hn⟩
    rw [he]
    exact Piece.suffix_subset _ _
  · exact h.greatest _ _ (Piece.whole_isSuffix _) (fun s hs ↦ by
      have := s.isLt
      simp only [Fin.lt_def] at hs
      omega)

/-- Section 5, `claim:containment`: every envy-free suffix family for the same
orders lies inside its candidate. No completeness or normalization is required. -/
theorem containment (h : IsCandidate v P Y) {Z : Fin n → Piece}
    (hZ : ∀ r, (Z r).IsSuffix (P r))
    (hEF : ∀ s r, (v s).value (Z r).support ≤ (v s).value (Z s).support) :
    ∀ r, (Z r).support ⊆ (Y r).support := by
  have hall : ∀ k : ℕ, ∀ r : Fin n, r.val < k → (Z r).support ⊆ (Y r).support := by
    intro k
    induction k with
    | zero => intro r hr; omega
    | succ k ih =>
      intro r hr
      apply h.greatest r (Z r) (hZ r)
      intro s hsr
      exact (hEF s r).trans ((v s).value_mono (Z s).measurableSet_support
        (Y s).measurableSet_support (ih s (by
          simp only [Fin.lt_def] at hsr
          omega)) (Y s).support_subset_unit)
  exact fun r ↦ hall n r r.isLt

/-- Section 5's candidates depend only on valuations, traversals, and orders.
Subdivision of input interval lists cannot change their bundle supports. -/
theorem support_unique (h : IsCandidate v P Y) {P' Z : Fin n → Piece}
    (hZ : IsCandidate v P' Z) (hP : ∀ r, (P r).SameTraversal (P' r)) :
    ∀ r, (Y r).support = (Z r).support := by
  have hall : ∀ k : ℕ, ∀ r : Fin n, r.val < k → (Y r).support = (Z r).support := by
    intro k
    induction k with
    | zero => intro r hr; omega
    | succ k ih =>
      intro r hr
      have he : ∀ s, s < r → (Y s).support = (Z s).support := by
        intro s hs
        exact ih s (by simp only [Fin.lt_def] at hs; omega)
      obtain ⟨a, ha, hya⟩ := h.suffix r
      obtain ⟨b, hb, hzb⟩ := hZ.suffix r
      have ha' : a ∈ Set.Icc 0 (P' r).length := (hP r).1 ▸ ha
      have hb' : b ∈ Set.Icc 0 (P r).length := (hP r).1.symm ▸ hb
      apply Set.Subset.antisymm
      · have hs := hZ.greatest r ((P' r).suffixAt a) ((P' r).suffix_isSuffix ha')
        rw [← (hP r).support_suffix_eq, ← hya] at hs
        exact hs (fun s hsr ↦ by rw [← he s hsr]; exact h.caps s r hsr)
      · have hs := h.greatest r ((P r).suffixAt b) ((P r).suffix_isSuffix hb')
        rw [(hP r).support_suffix_eq, ← hzb] at hs
        exact hs (fun s hsr ↦ by rw [he s hsr]; exact hZ.caps s r hsr)
  exact fun r ↦ hall n r r.isLt

/-- Section 5, “Some candidate is envy-free”: an envy-free extension agrees
with the candidate in every bundle support. -/
theorem extension_eq (h : IsCandidate v P Y) {Z : Fin n → Piece}
    (hZ : ∀ r, (Z r).IsSuffix (P r))
    (hext : ∀ r, (Y r).support ⊆ (Z r).support)
    (hEF : ∀ s r, (v s).value (Z r).support ≤ (v s).value (Z s).support) :
    ∀ r, (Z r).support = (Y r).support :=
  fun r ↦ Set.Subset.antisymm (h.containment hZ hEF r) (hext r)

end IsCandidate

/-- Section 5, `claim:containment`, with the paper's original agent and piece
labels: every envy-free suffix allocation is contained bundle by bundle. -/
theorem candidate_contains_envyFree_allocation {n : ℕ} {C : Piece}
    (v : Fin n → Valuation) (P Y : Fin n → Piece)
    (agents pieces : Equiv.Perm (Fin n))
    (hY : IsCandidate (v ∘ agents) (P ∘ pieces) Y) (Z : Allocation n C)
    (hEF : Z.EnvyFree v)
    (hZ : ∀ r, (Z.bundle (agents r)).IsSuffix (P (pieces r))) :
    ∀ i, (Z.bundle i).support ⊆ (Y (agents.symm i)).support := by
  have h := hY.containment hZ (fun s r ↦ hEF (agents s) (agents r))
  intro i
  simpa only [Equiv.apply_symm_apply] using h (agents.symm i)

namespace CandidateConstruction

/-- The cap data used in the mathematical construction, without any records. -/
def caps {n : ℕ} (v : Fin n → Valuation) (Y : Fin n → Piece) (k : ℕ) :
    List (Valuation × ℝ) :=
  ((List.finRange n).take k).map fun r ↦ (v r, (v r).value (Y r).support)

/-- Section 5, `eq:permute-caps`: a cap sequence gives all three parts of the
candidate characterization at its position. -/
theorem sequence_characterization {n : ℕ} {v : Fin n → Valuation}
    {P Y : Fin n → Piece} (r : Fin n)
    (h : CapTrimSequence (P r) (caps v Y r.val) (Y r)) :
    (Y r).IsSuffix (P r) ∧
    (∀ s, s < r → (v s).value (Y r).support ≤ (v s).value (Y s).support) ∧
    (∀ T : Piece, T.IsSuffix (P r) →
      (∀ s, s < r → (v s).value T.support ≤ (v s).value (Y s).support) →
      T.support ⊆ (Y r).support) := by
  have hm (s : Fin n) (hs : s < r) :
      (v s, (v s).value (Y s).support) ∈ caps v Y r.val := by
    apply List.mem_map.mpr
    refine ⟨s, ?_, rfl⟩
    rw [List.mem_take_iff_getElem]
    exact ⟨s.val, by simpa using lt_min (show s.val < r.val from hs) s.isLt, by simp⟩
  refine ⟨h.isSuffix, fun s hs ↦ h.values_le _ (hm s hs), ?_⟩
  intro T hT hcap
  apply h.preserves hT
  intro c hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  rw [List.mem_take_iff_getElem] at hs
  obtain ⟨i, hi, he⟩ := hs
  have hsr : s < r := by
    simp only [List.getElem_finRange] at he
    subst s
    change i < r.val
    exact lt_of_lt_of_le hi (min_le_left _ _)
  exact hcap s hsr

theorem mem_positions {n : ℕ} (k : ℕ) (r : Fin n) :
    r ∈ (List.finRange n).take k ↔ r.val < k := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, hi, he⟩
    simp only [List.getElem_finRange] at he
    subst r
    exact lt_of_lt_of_le hi (min_le_left _ _)
  · intro hr
    exact ⟨r.val, by simpa using lt_min hr r.isLt, by simp⟩

theorem caps_congr {n : ℕ} (v : Fin n → Valuation) (Y Z : Fin n → Piece)
    (k : ℕ) (h : ∀ r : Fin n, r.val < k → (Y r).support = (Z r).support) :
    caps v Y k = caps v Z k := by
  apply List.map_congr_left
  intro r hr
  rw [h r ((mem_positions k r).mp hr)]

/-- Section 5, `eq:permute-caps`: every fixed pair of orders has a candidate,
independently of recorded states or a protocol execution. -/
theorem exists_candidate {n : ℕ} (v : Fin n → Valuation) (P : Fin n → Piece) :
    ∃ Y, IsCandidate v P Y := by
  classical
  have hall : ∀ k : ℕ, k ≤ n → ∃ Y : Fin n → Piece,
      ∀ r : Fin n, r.val < k → CapTrimSequence (P r) (caps v Y r.val) (Y r) := by
    intro k
    induction k with
    | zero => exact fun _ ↦ ⟨fun _ ↦ Piece.empty, fun r hr ↦ by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨Y, hY⟩ := ih (by omega)
      let t : Fin n := ⟨k, by omega⟩
      have hn : ∀ c ∈ caps v Y k, 0 ≤ c.2 := by
        intro c hc
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc
        exact (v r).value_nonneg (Y r).measurableSet_support (Y r).support_subset_unit
      obtain ⟨Q, hQ⟩ := CapTrimSequence.exists_sequence (P t) (caps v Y k) hn
      let Z := Function.update Y t Q
      have hsame (r : Fin n) (hr : r.val < k) : Z r = Y r := by
        apply Function.update_of_ne
        intro he
        have := congrArg Fin.val he
        change r.val = k at this
        omega
      have hcaps (m : ℕ) (hm : m ≤ k) : caps v Z m = caps v Y m :=
        caps_congr _ _ _ _ (fun r hr ↦ congrArg Piece.support (hsame r (by omega)))
      refine ⟨Z, ?_⟩
      intro r hr
      by_cases he : r = t
      · subst r
        change CapTrimSequence (P t) (caps v Z k) (Z t)
        rw [hcaps k le_rfl]
        simpa only [Z, Function.update_self] using hQ
      · have hrk : r.val < k := by
          have hne : r.val ≠ k := fun h ↦ he (Fin.ext h)
          omega
        rw [hcaps r.val hrk.le, hsame r hrk]
        exact hY r hrk
  obtain ⟨Y, hY⟩ := hall n le_rfl
  exact ⟨Y, fun r ↦ (sequence_characterization r (hY r r.isLt)).1,
    fun s r hsr ↦ (sequence_characterization r (hY r r.isLt)).2.1 s hsr,
    fun r ↦ (sequence_characterization r (hY r r.isLt)).2.2⟩

/-- The mathematical candidate for fixed position-indexed valuations and inputs. -/
noncomputable def candidate {n : ℕ} (v : Fin n → Valuation) (P : Fin n → Piece) :
    Fin n → Piece := (exists_candidate v P).choose

theorem candidate_spec {n : ℕ} (v : Fin n → Valuation) (P : Fin n → Piece) :
    IsCandidate v P (candidate v P) := (exists_candidate v P).choose_spec

end CandidateConstruction
end CakeCuttingPsomas
