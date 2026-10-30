module

public import CakeCuttingPsomas.FineCells
public import CakeCuttingPsomas.Suffix
public import CakeCuttingPsomas.DominateChoice

set_option linter.style.header false

/-! # The proof-only envy-cycle process

Section 5, proof of `lem:permute`, “Creating a δ-envy-free suffix allocation”.
Boundaries belong to input labels; a separate permutation assigns labels to agents.
This mathematical process makes no Robertson–Webb queries.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.EnvyCycle

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {P : Fin n → Piece} (d : (j : Fin n) → CellPartition (P j))

/-- All legal suffix boundaries, including both endpoints for empty pieces. -/
def boundaries (j : Fin n) : Finset ℝ := insert 0 (insert (P j).length (d j).points)

/-- Input labels survive even when several suffixes have empty support. -/
structure State where
  cut : Fin n → ℝ
  boundary : ∀ j, cut j ∈ boundaries d j
  assignment : Equiv.Perm (Fin n)

namespace State

variable {d} (X : State d)

theorem cut_mem (j : Fin n) : X.cut j ∈ Set.Icc 0 (P j).length := by
  rcases Finset.mem_insert.mp (X.boundary j) with h | h
  · rw [h]; exact ⟨le_rfl, (P j).length_nonneg⟩
  · rcases Finset.mem_insert.mp h with h | h
    · rw [h]; exact ⟨(P j).length_nonneg, le_rfl⟩
    · exact ⟨((d j).interior _ h).1.le, ((d j).interior _ h).2.le⟩

def bundle (i : Fin n) : Piece := (P (X.assignment i)).suffixAt (X.cut (X.assignment i))

theorem suffix (i : Fin n) : (X.bundle i).IsSuffix (P (X.assignment i)) :=
  (P _).suffix_isSuffix (X.cut_mem _)

theorem subset (i : Fin n) : (X.bundle i).support ⊆ (P (X.assignment i)).support :=
  (P _).suffix_subset _

/-- Non-wholeness is geometric, including zero-valued bands. -/
theorem whole_iff (i : Fin n) :
    (X.bundle i).support = (P (X.assignment i)).support ↔ X.cut (X.assignment i) = 0 := by
  constructor
  · intro h
    have hs : (P (X.assignment i)).support ⊆ (X.bundle i).support := h.symm.subset
    rw [← (P (X.assignment i)).suffix_zero] at hs
    have := ((P (X.assignment i)).suffix_subset_suffix_iff
      (X.cut_mem _) ⟨le_rfl, (P _).length_nonneg⟩).mp hs
    exact le_antisymm this (X.cut_mem _).1
  · intro h; simp [bundle, h]

/-- The usual partial allocation induced by a labelled suffix state. -/
def allocation (C : Piece) (hC : ∀ j, (P j).support ⊆ C.support)
    (hdis : ∀ j k, j ≠ k → Disjoint (P j).support (P k).support) : Allocation n C where
  bundle := X.bundle
  contained i := (X.subset i).trans (hC _)
  disjoint i j hij := (hdis _ _ (fun h ↦ hij (X.assignment.injective h))).mono
    (X.subset i) (X.subset j)

/-- Strict envy, directed from the observer to the envied recipient. -/
def Edge (v : Fin n → Valuation) (i j : Fin n) : Prop :=
  (v i).value (X.bundle i).support < (v i).value (X.bundle j).support

/-- Directed acyclicity: there is no nonempty closed envy path. -/
def Acyclic (v : Fin n → Valuation) : Prop :=
  ∀ i, ¬ Relation.TransGen (X.Edge v) i i

def DeltaEnvyFree (v : Fin n → Valuation) (δ : ℝ) : Prop :=
  ∀ i j, (v i).value (X.bundle j).support ≤ (v i).value (X.bundle i).support + δ

/-- A simple directed envy cycle, including its closing edge. -/
structure Cycle (v : Fin n → Valuation) where
  first : Fin n
  rest : List (Fin n)
  nodup : (first :: rest).Nodup
  chain : (first :: rest).IsChain (X.Edge v)
  closing : X.Edge v ((first :: rest).getLast (List.cons_ne_nil _ _)) first

namespace Cycle

variable {X} {v : Fin n → Valuation} (c : X.Cycle v)

def permutation : Equiv.Perm (Fin n) := (c.first :: c.rest).formPerm

theorem follows (i : Fin n) : c.permutation i = i ∨ X.Edge v i (c.permutation i) := by
  have h := DominateChoice.path_permutation c.first c.rest c.nodup c.chain
  by_cases hi : i = (c.first :: c.rest).getLast (List.cons_ne_nil _ _)
  · right
    rw [hi, show c.permutation _ = c.first from h.1]
    exact c.closing
  · exact h.2 i hi

theorem improves : ∃ i, X.Edge v i (c.permutation i) := by
  have h := DominateChoice.path_permutation c.first c.rest c.nodup c.chain
  refine ⟨(c.first :: c.rest).getLast (List.cons_ne_nil _ _), ?_⟩
  change X.Edge v _ ((c.first :: c.rest).formPerm _)
  rw [h.1]
  exact c.closing

end Cycle

/-- A closed path contains a simple cycle; reuse Section 3's simple-path lemma. -/
theorem cycle_of_not_acyclic {v : Fin n → Valuation} (h : ¬ X.Acyclic v) :
    Nonempty (X.Cycle v) := by
  obtain ⟨i, hi⟩ := not_forall.mp h
  obtain ⟨j, hij, hji⟩ := Relation.TransGen.head'_iff.mp (not_not.mp hi)
  obtain ⟨l, hnd, hch, hl⟩ := DominateChoice.simple_path hji
  exact ⟨⟨j, l, hnd, hch, by rw [hl]; exact hij⟩⟩

/-- Section 5, `lem:permute`: rotate a cycle; labels follow their suffixes. -/
def rotate {v : Fin n → Valuation} (c : X.Cycle v) : State d where
  cut := X.cut
  boundary := X.boundary
  assignment := c.permutation.trans X.assignment

@[simp] theorem bundle_rotate {v : Fin n → Valuation} (c : X.Cycle v) (i : Fin n) :
    (X.rotate c).bundle i = X.bundle (c.permutation i) := rfl

/-- Rotations change recipients but preserve the exact allocated support. -/
theorem rotate_support {v : Fin n → Valuation} (c : X.Cycle v) :
    (⋃ i, ((X.rotate c).bundle i).support) = ⋃ i, (X.bundle i).support := by
  ext x
  simp only [Set.mem_iUnion, bundle_rotate]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨c.permutation i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨c.permutation.symm i, by simpa using hi⟩

theorem rotate_own_le {v : Fin n → Valuation} (c : X.Cycle v) (i : Fin n) :
    (v i).value (X.bundle i).support ≤ (v i).value ((X.rotate c).bundle i).support := by
  rw [bundle_rotate]
  rcases c.follows i with h | h
  · rw [h]
  · exact h.le

/-- Section 5, `lem:permute`: rotating an envy cycle preserves δ-envy-freeness. -/
theorem rotate_deltaEnvyFree {v : Fin n → Valuation} {δ : ℝ}
    (h : X.DeltaEnvyFree v δ) (c : X.Cycle v) : (X.rotate c).DeltaEnvyFree v δ := by
  intro i j
  have h₁ := h i (c.permutation j)
  have h₂ := X.rotate_own_le c i
  rw [bundle_rotate]
  linarith

/-- Adjoin the cell preceding the recipient's suffix, keeping its input label. -/
def enlarge (i : Fin n) (a : (d (X.assignment i)).Index) : State d where
  cut := Function.update X.cut (X.assignment i) a.val
  boundary j := by
    by_cases h : j = X.assignment i
    · subst j
      simp only [Function.update_self]
      rcases Finset.mem_insert.mp ((d _).start_mem a) with h | h
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_of_mem h))
    · simpa [Function.update_of_ne h] using X.boundary j
  assignment := X.assignment

@[simp] theorem bundle_enlarge_self (i : Fin n) (a : (d (X.assignment i)).Index) :
    (X.enlarge i a).bundle i = (P (X.assignment i)).suffixAt a.val := by
  simp [bundle, enlarge]

theorem bundle_enlarge_other (i j : Fin n) (a : (d (X.assignment i)).Index) (h : j ≠ i) :
    (X.enlarge i a).bundle j = X.bundle j := by
  simp [bundle, enlarge, Function.update_of_ne (X.assignment.injective.ne h)]

/-- The preceding cell is disjoint from every old bundle, assuming disjoint inputs. -/
theorem preceding_disjoint
    (hdis : ∀ j k, j ≠ k → Disjoint (P j).support (P k).support)
    (i : Fin n) (a : (d (X.assignment i)).Index)
    (ha : (d _).finish a = X.cut (X.assignment i)) (j : Fin n) :
    Disjoint ((d _).piece a).support (X.bundle j).support := by
  by_cases hj : j = i
  · subst j
    simpa only [ha, bundle] using (d _).cell_disjoint_suffix a
  · exact (hdis _ _ (X.assignment.injective.ne (Ne.symm hj))).mono
      ((d _).subset a) (X.subset j)

/-- Section 5, `lem:permute`: enlargement adds exactly the preceding cell. -/
theorem enlarge_support (i : Fin n) (a : (d (X.assignment i)).Index)
    (ha : (d _).finish a = X.cut (X.assignment i)) :
    (⋃ j, ((X.enlarge i a).bundle j).support) =
      ((d _).piece a).support ∪ ⋃ j, (X.bundle j).support := by
  have he : ((X.enlarge i a).bundle i).support =
      ((d _).piece a).support ∪ (X.bundle i).support := by
    rw [bundle_enlarge_self, ← (d _).cell_union_suffix a, ha]
    rfl
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rcases he ▸ hj with hx | hx
      · exact Or.inl hx
      · exact Or.inr ⟨i, hx⟩
    · exact Or.inr ⟨j, by simpa only [X.bundle_enlarge_other i j a hji] using hj⟩
  · rintro (hx | ⟨j, hj⟩)
    · exact ⟨i, he.symm ▸ Or.inl hx⟩
    · by_cases hji : j = i
      · subst j
        exact ⟨i, he.symm ▸ Or.inr hj⟩
      · exact ⟨j, by simpa only [X.bundle_enlarge_other i j a hji] using hj⟩

/-- Every proper boundary suffix has a preceding cell. -/
theorem preceding (i : Fin n)
    (h : (X.bundle i).support ≠ (P (X.assignment i)).support) :
    ∃ a : (d (X.assignment i)).Index, (d _).finish a = X.cut (X.assignment i) := by
  have hn : X.cut (X.assignment i) ≠ 0 := fun hz ↦ h ((X.whole_iff i).mpr hz)
  exact (d _).exists_preceding
    ((Finset.mem_insert.mp (X.boundary _)).resolve_left hn)
    (lt_of_le_of_ne (X.cut_mem _).1 (Ne.symm hn))

/-- Section 5, `lem:permute`: enlarging an unenvied suffix by a fine cell
preserves δ-envy-freeness, including cells of value zero. -/
theorem enlarge_deltaEnvyFree {v : Fin n → Valuation} {δ : ℝ}
    (h : X.DeltaEnvyFree v δ)
    (hf : ∀ j i (a : (d j).Index), (v i).value ((d j).piece a).support ≤ δ)
    (i : Fin n) (hu : ∀ j, ¬ X.Edge v j i) (a : (d (X.assignment i)).Index)
    (ha : (d _).finish a = X.cut (X.assignment i)) :
    (X.enlarge i a).DeltaEnvyFree v δ := by
  have hv (k : Fin n) : (v k).value ((X.enlarge i a).bundle i).support =
      (v k).value ((d _).piece a).support + (v k).value (X.bundle i).support := by
    rw [bundle_enlarge_self, (d _).value_suffix_step a (v k), ha]
    rfl
  have hn (k : Fin n) : 0 ≤ (v k).value ((d _).piece a).support :=
    (v k).value_nonneg ((d _).piece a).measurableSet_support
      ((d _).piece a).support_subset_unit
  intro k j
  by_cases hk : k = i
  · subst k
    by_cases hj : j = i
    · subst j
      have hδ : 0 ≤ δ := (hn i).trans (hf _ i a)
      linarith
    · rw [X.bundle_enlarge_other i j a hj, hv]
      have := h i j
      linarith [hn i]
  · rw [X.bundle_enlarge_other i k a hk]
    by_cases hj : j = i
    · subst j
      rw [hv]
      have := not_lt.mp (hu k)
      change (v k).value (X.bundle i).support ≤ (v k).value (X.bundle k).support at this
      linarith [hf _ k a]
    · rw [X.bundle_enlarge_other i j a hj]
      exact h k j

/-- The mathematical process starts with empty suffixes and distinct labels. -/
def initial : State d where
  cut j := (P j).length
  boundary _j := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  assignment := Equiv.refl _

@[simp] theorem bundle_initial (i : Fin n) : (initial (d := d)).bundle i = Piece.empty := by
  simp [initial, bundle]

theorem initial_deltaEnvyFree {v : Fin n → Valuation} {δ : ℝ} (hδ : 0 ≤ δ) :
    (initial (d := d)).DeltaEnvyFree v δ := by
  intro i j
  simpa only [bundle_initial, Piece.support_empty, Valuation.value_empty, zero_add] using hδ

/-- Section 5's two transitions, with cycle rotations taking priority. -/
inductive Step (v : Fin n → Valuation) : State d → State d → Prop
  | rotate (X : State d) (c : X.Cycle v) : Step v X (X.rotate c)
  | enlarge (X : State d) (acyclic : X.Acyclic v) (i : Fin n)
      (unenvied : ∀ j, ¬ X.Edge v j i) (a : (d (X.assignment i)).Index)
      (preceding : (d _).finish a = X.cut (X.assignment i)) : Step v X (X.enlarge i a)

/-- Terminal states expose exactly the hypotheses needed for candidate containment. -/
def Terminal (v : Fin n → Valuation) : Prop :=
  X.Acyclic v ∧ ∀ i, (X.bundle i).support ≠ (P (X.assignment i)).support →
    ∃ j, X.Edge v j i

theorem terminal_iff_no_step (v : Fin n → Valuation) :
    X.Terminal v ↔ ¬ ∃ Y, Step v X Y := by
  constructor
  · rintro ⟨hc, hu⟩ ⟨Y, hY⟩
    cases hY with
    | rotate c =>
      have hpath : Relation.ReflTransGen (X.Edge v) c.first
          ((c.first :: c.rest).getLast (List.cons_ne_nil _ _)) := by
        exact List.relationReflTransGen_of_exists_isChain_cons c.rest c.chain rfl
      exact hc _ (Relation.TransGen.tail' hpath c.closing)
    | enlarge _ i hi a ha =>
      have hn : (X.bundle i).support ≠ (P (X.assignment i)).support := by
        intro he
        have hz := (X.whole_iff i).mp he
        have hp := (d _).finish_spec a
        have h0 := (d _).start_nonneg a
        rw [ha, hz] at hp
        linarith [hp.1]
      obtain ⟨j, hj⟩ := hu i hn
      exact hi j hj
  · intro h
    have hc : X.Acyclic v := by
      by_contra hn
      obtain ⟨c⟩ := X.cycle_of_not_acyclic hn
      exact h ⟨_, .rotate X c⟩
    refine ⟨hc, fun i hi ↦ ?_⟩
    by_contra hn
    have hu : ∀ j, ¬ X.Edge v j i := by simpa using hn
    obtain ⟨a, ha⟩ := X.preceding i hi
    exact h ⟨_, .enlarge X hc i hu a ha⟩

end State
end CakeCuttingPsomas.EnvyCycle
