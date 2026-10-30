module

public import CakeCuttingPsomas.TraversalPartition

set_option linter.style.header false

/-! # Proof-only fine cells for Permute

Section 5, proof of `lem:permute`, paragraph “Creating a δ-envy-free suffix
allocation”. Value-scaled subdivision targets remove the example's normalization
assumption. This construction is mathematical and makes no protocol queries.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas

open TraversalPartition

attribute [local instance] Classical.propDecidable

/-- A finite set of internal boundaries on the piece's specified traversal.
The endpoints are implicit; an empty piece has no cells. -/
structure CellPartition (P : Piece) where
  points : Finset ℝ
  interior : ∀ x ∈ points, 0 < x ∧ x < P.length

namespace CellPartition

/-- Cell starts in traversal order, excluding the terminal boundary. -/
def boundaries {P : Piece} (d : CellPartition P) : Finset ℝ :=
  (starts d.points).filter (· < P.length)

/-- A cell is labelled by its starting traversal position. -/
abbrev Index {P : Piece} (d : CellPartition P) := {a // a ∈ d.boundaries}

/-- The consecutive band from this start to the next mark or the piece's end. -/
def piece {P : Piece} (d : CellPartition P) (a : d.Index) : Piece :=
  cell P d.points a.val

/-- The next boundary, possibly the terminal endpoint. -/
def finish {P : Piece} (d : CellPartition P) (a : d.Index) : ℝ :=
  next P.length d.points a.val

theorem start_mem {P : Piece} (d : CellPartition P) (a : d.Index) :
    a.val ∈ starts d.points := (Finset.mem_filter.mp a.property).1

theorem start_nonneg {P : Piece} (d : CellPartition P) (a : d.Index) : 0 ≤ a.val := by
  rcases Finset.mem_insert.mp (d.start_mem a) with h | h
  · exact h ▸ le_rfl
  · exact (d.interior _ h).1.le

theorem finish_spec {P : Piece} (d : CellPartition P) (a : d.Index) :
    a.val < d.finish a ∧ d.finish a ≤ P.length ∧
      (d.finish a = P.length ∨ d.finish a ∈ d.points) ∧
      ∀ x ∈ d.points, a.val < x → d.finish a ≤ x :=
  next_spec d.interior (Finset.mem_filter.mp a.property).2

/-- Every represented cell is nonempty, even if every agent values it at zero. -/
theorem nonempty {P : Piece} (d : CellPartition P) (a : d.Index) :
    (d.piece a).support.Nonempty :=
  cell_nonempty P d.points (lt_of_le_of_lt (d.start_nonneg a)
    (Finset.mem_filter.mp a.property).2) d.interior (d.start_mem a)

theorem subset {P : Piece} (d : CellPartition P) (a : d.Index) :
    (d.piece a).support ⊆ P.support := by
  intro x hx
  exact P.prefix_subset _ ((support_cell P d.points a.val ▸ hx).1)

/-- Section 5, proof of `lem:permute`: the consecutive cells partition the
piece exactly, including endpoints and zero-valued stretches. -/
theorem partition {P : Piece} (d : CellPartition P) :
    (⋃ a : d.Index, (d.piece a).support) = P.support ∧
      ∀ a b : d.Index, a ≠ b → Disjoint (d.piece a).support (d.piece b).support := by
  by_cases hL : 0 < P.length
  · have hb : d.boundaries = starts d.points := by
      apply Finset.filter_eq_self.mpr
      exact fun a ha ↦ start_lt hL d.interior ha
    obtain ⟨hc, hd⟩ := cells_partition P d.points hL d.interior
    constructor
    · rw [← hc]
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨⟨a.val, d.start_mem a⟩, ha⟩
      · rintro ⟨a, ha⟩
        exact ⟨⟨a.val, by rw [hb]; exact a.property⟩, ha⟩
    · intro a b hab
      exact hd ⟨a.val, d.start_mem a⟩ ⟨b.val, d.start_mem b⟩
        (fun h ↦ hab (Subtype.ext (congrArg (fun c : {x // x ∈ starts d.points} ↦ c.val) h)))
  · have hz : P.length = 0 := le_antisymm (le_of_not_gt hL) P.length_nonneg
    have he : P.support = ∅ := by
      have h := congrArg Piece.support P.prefix_length
      simpa [hz] using h.symm
    have hi (a : d.Index) : False := by
      have := (Finset.mem_filter.mp a.property).2
      have := d.start_nonneg a
      linarith
    constructor
    · rw [he]
      exact Set.iUnion_eq_empty.mpr fun a ↦ (hi a).elim
    · exact fun a ↦ (hi a).elim

/-- Empty pieces have no cells, rather than one degenerate cell. -/
theorem boundaries_of_length_zero {P : Piece} (d : CellPartition P)
    (hP : P.length = 0) : d.boundaries = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have ha0 : 0 ≤ a := d.start_nonneg ⟨a, ha⟩
  have := (Finset.mem_filter.mp ha).2
  linarith

/-- Section 5's enlargement step is always available at a positive boundary:
every internal mark or terminal endpoint has an immediately preceding cell. -/
theorem exists_preceding {P : Piece} (d : CellPartition P) {b : ℝ}
    (hb : b ∈ insert P.length d.points) (hb0 : 0 < b) :
    ∃ a : d.Index, d.finish a = b := by
  have hbL : b ≤ P.length := by
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact le_rfl
    · exact (d.interior _ hb).2.le
  let S := (starts d.points).filter (· < b)
  have hS : S.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hb0⟩⟩
  let x := S.max' hS
  have hx := Finset.mem_filter.mp (Finset.max'_mem S hS)
  let a : d.Index := ⟨x, Finset.mem_filter.mpr ⟨hx.1, hx.2.trans_le hbL⟩⟩
  have hnext := d.finish_spec a
  have hle : d.finish a ≤ b := by
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hnext.2.1
    · exact hnext.2.2.2 b hb hx.2
  refine ⟨a, le_antisymm hle ?_⟩
  by_contra hn
  have hlt : d.finish a < b := lt_of_not_ge hn
  have hmem : d.finish a ∈ S := by
    have hp : d.finish a ∈ d.points := by
      rcases hnext.2.2.1 with he | hp
      · rw [he] at hlt
        exact (not_lt_of_ge hbL hlt).elim
      · exact hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hp, hlt⟩
  have hmax := Finset.le_max' S (d.finish a) hmem
  have hxa : a.val = S.max' hS := rfl
  rw [← hxa] at hmax
  exact (not_lt_of_ge hmax) hnext.1

/-- Section 5's enlargement step: adjoining the immediately preceding cell to
a boundary suffix gives exactly the suffix at the preceding boundary. -/
theorem cell_union_suffix {P : Piece} (d : CellPartition P) (a : d.Index) :
    (d.piece a).support ∪ (P.suffixAt (d.finish a)).support =
      (P.suffixAt a.val).support := by
  have hsub := P.prefix_mono (d.finish_spec a).1.le
  have hP := P.prefix_subset (d.finish a)
  change (cell P d.points a.val).support ∪ _ = _
  rw [support_cell, Piece.support_suffix, Piece.support_suffix]
  ext x
  simp only [Set.mem_union, Set.mem_sdiff]
  constructor
  · rintro (⟨hx, ha⟩ | ⟨hx, hb⟩)
    · exact ⟨hP hx, ha⟩
    · exact ⟨hx, fun ha ↦ hb (hsub ha)⟩
  · rintro ⟨hx, ha⟩
    by_cases hb : x ∈ (P.prefixAt (d.finish a)).support
    · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨hx, hb⟩

theorem cell_disjoint_suffix {P : Piece} (d : CellPartition P) (a : d.Index) :
    Disjoint (d.piece a).support (P.suffixAt (d.finish a)).support := by
  rw [piece, support_cell, Piece.support_suffix]
  exact Set.disjoint_left.mpr fun _ hx hy ↦ hy.2 hx.1

/-- Suffix enlargement adds precisely the cell's value for every observer. -/
theorem value_suffix_step {P : Piece} (d : CellPartition P) (a : d.Index)
    (v : Valuation) :
    v.value (P.suffixAt a.val).support =
      v.value (d.piece a).support + v.value (P.suffixAt (d.finish a)).support := by
  rw [← d.cell_union_suffix a]
  exact v.value_union (d.piece a).measurableSet_support
    (P.suffixAt (d.finish a)).measurableSet_support (d.piece a).support_subset_unit
    (P.suffixAt (d.finish a)).support_subset_unit (d.cell_disjoint_suffix a)

end CellPartition

namespace FineCells

/-- Number of equal-value shares for one observer, scaled to an absolute bound. -/
def subdivisions (A δ : ℝ) : ℕ := max 1 ⌈A / δ⌉₊

theorem subdivisions_pos (A δ : ℝ) : 0 < subdivisions A δ := by
  unfold subdivisions
  omega

theorem share_le (A δ : ℝ) (hδ : 0 < δ) : A / subdivisions A δ ≤ δ := by
  have hm : (0 : ℝ) < subdivisions A δ := by exact_mod_cast subdivisions_pos A δ
  have hc : A / δ ≤ (subdivisions A δ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈A / δ⌉₊))
  apply (div_le_iff₀ hm).mpr
  have := (div_le_iff₀ hδ).mp hc
  linarith

private theorem exists_mark (P : Piece) (v : Valuation) (M : ℕ)
    (hM : 0 < M) (hpos : 0 < v.value P.support) (k : Fin (M - 1)) :
    ∃ x, (0 < x ∧ x < P.length) ∧
      v.value (P.prefixAt x).support = (k.val + 1 : ℕ) * (v.value P.support / M) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hk : (0 : ℝ) < (k.val + 1 : ℕ) := by positivity
  have hkm : ((k.val + 1 : ℕ) : ℝ) < M := by
    exact_mod_cast (show k.val + 1 < M by omega)
  have ht : 0 < (k.val + 1 : ℕ) * (v.value P.support / M) :=
    mul_pos hk (div_pos hpos hm)
  have he : (M : ℝ) * (v.value P.support / M) = v.value P.support :=
    mul_div_cancel₀ _ hm.ne'
  have hlt : (k.val + 1 : ℕ) * (v.value P.support / M) < v.value P.support := by
    nlinarith [div_pos hpos hm]
  obtain ⟨x, hx, hv, _⟩ := v.exists_smallest_prefix P ht.le hlt.le
  refine ⟨x, ⟨?_, ?_⟩, hv⟩
  · by_contra hn
    rw [P.prefix_nonpos (le_of_not_gt hn)] at hv
    have hz : (k.val + 1 : ℕ) * (v.value P.support / M) = 0 := by
      simpa only [Piece.support_empty, Valuation.value_empty] using hv.symm
    linarith
  · by_contra hn
    have hxL : x = P.length := le_antisymm hx.2 (le_of_not_gt hn)
    rw [hxL, Piece.prefix_length] at hv
    linarith

/-- Section 5, proof of `lem:permute`, “Creating a δ-envy-free suffix allocation”:
every piece admits finite consecutive cells worth at most δ to every agent.
Subdivision counts scale with each observer's value; normalization, positive
values, and nonempty input are not required. This is proof-only existence. -/
theorem exists_partition {n : ℕ} (v : Fin n → Valuation) (P : Piece)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ d : CellPartition P, ∀ i (a : d.Index), (v i).value (d.piece a).support ≤ δ := by
  let M (i : Fin n) := subdivisions ((v i).value P.support) δ
  let Agents := {i : Fin n // 0 < (v i).value P.support}
  have hex (i : Agents) (k : Fin (M i.val - 1)) :=
    exists_mark P (v i.val) (M i.val) (subdivisions_pos _ _) i.property k
  choose x hx hv using hex
  let points : Finset ℝ := Finset.univ.biUnion fun i : Agents ↦
    Finset.univ.image (x i)
  have hp : ∀ y ∈ points, 0 < y ∧ y < P.length := by
    intro y hy
    obtain ⟨i, _, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    exact hx i k
  let d : CellPartition P := ⟨points, hp⟩
  refine ⟨d, ?_⟩
  intro i a
  by_cases hpos : 0 < (v i).value P.support
  · have hmks (k : Fin (M i - 1)) : ∃ y ∈ points,
        (v i).value (P.prefixAt y).support =
          (k.val + 1 : ℕ) * ((v i).value P.support / M i) := by
      exact ⟨x ⟨i, hpos⟩ k, Finset.mem_biUnion.mpr ⟨⟨i, hpos⟩,
        Finset.mem_univ _, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩,
        hv ⟨i, hpos⟩ k⟩
    exact (cell_value_le P points (M i) (v i) (subdivisions_pos _ _) hpos
      (lt_of_le_of_lt (d.start_nonneg a) (Finset.mem_filter.mp a.property).2)
      hp hmks a.val (d.start_mem a)).trans (share_le _ δ hδ)
  · exact ((v i).value_mono (d.piece a).measurableSet_support P.measurableSet_support
      (d.subset a) P.support_subset_unit).trans ((le_of_not_gt hpos).trans hδ.le)

/-- Section 5's simultaneous discretization of all labelled input pieces.
Empty labels are retained, and no disjointness assumption is needed to subdivide. -/
theorem exists_partitions {n : ℕ} (v : Fin n → Valuation) (pieces : Fin n → Piece)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ d : (j : Fin n) → CellPartition (pieces j),
      ∀ j i (a : (d j).Index), (v i).value ((d j).piece a).support ≤ δ := by
  exact Classical.axiom_of_choice (fun j ↦ exists_partition v (pieces j) δ hδ)

end FineCells
end CakeCuttingPsomas
