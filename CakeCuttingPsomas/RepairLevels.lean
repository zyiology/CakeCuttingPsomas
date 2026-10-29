module

public import CakeCuttingPsomas.RepairRoundRobin
public import CakeCuttingPsomas.Permute
public import Mathlib.Order.Interval.Finset.Fin

set_option linter.style.header false

/-! # Repair preserves the old bundles

Section 4, proof of `lem:repair main`: ordered concatenation, levels,
higher-level preference, and the missing-level argument. Permute is used only
through its contract; no implementation of Section 5 is assumed here.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.RepairLevels

open Finset
attribute [local instance] Classical.propDecidable

private theorem piece_eq {P Q : Piece} (h : P.intervals = Q.intervals) : P = Q := by
  cases P
  cases Q
  simp_all

/-- The selected paper cells, indexed by original agent and zero-based round.
These are pieces of the old residue, disjoint across all picks. -/
structure Picks {n : ℕ} {C : Piece} (D : Allocation n C) where
  cell : Fin n → Fin (n - 1) → Piece
  disjoint : ∀ i r j q, (i, r) ≠ (j, q) →
    Disjoint (cell i r).support (cell j q).support
  subset_residue : ∀ i r, (cell i r).support ⊆ D.residue

variable {n : ℕ} {C : Piece} {D : Allocation n C}

namespace Picks

variable (p : Picks D)

def roundList : List (Fin (n - 1)) := List.ofFn id

theorem roundList_nodup : (roundList (n := n)).Nodup :=
  List.nodup_ofFn.mpr Function.injective_id

private theorem mem_roundList_drop (k : ℕ) (r : Fin (n - 1)) :
    r ∈ (roundList (n := n)).drop k ↔ k ≤ r.val := by
  simp only [List.mem_drop_iff_getElem, roundList, List.length_ofFn, List.getElem_ofFn]
  constructor
  · rintro ⟨j, hj, he⟩
    have := congrArg Fin.val he
    dsimp at this
    omega
  · intro h
    refine ⟨r.val - k, by omega, ?_⟩
    apply Fin.ext
    change k + (r.val - k) = r.val
    omega

/-- Chosen cells from round `k` onward, in pick order. -/
def added (i : Fin n) (k : ℕ) : Piece :=
  (RepairRoundRobin.join (p.cell i)
    (fun r q h ↦ p.disjoint i r i q (by simpa using h))
    ((roundList (n := n)).drop k) (by exact (roundList_nodup (n := n)).drop)).piece

theorem added_intervals (i : Fin n) (k : ℕ) :
    (p.added i k).intervals =
      ((roundList (n := n)).drop k).flatMap (fun r ↦ (p.cell i r).intervals) :=
  (RepairRoundRobin.join _ _ _ _).intervals_eq

theorem added_support (i : Fin n) (k : ℕ) :
    (p.added i k).support = ⋃ r : Fin (n - 1), ⋃ (_ : k ≤ r.val), (p.cell i r).support := by
  rw [added, (RepairRoundRobin.join _ _ _ _).support_eq]
  simp only [mem_roundList_drop]

theorem added_subset (i : Fin n) (k : ℕ) : (p.added i k).support ⊆ D.residue := by
  rw [added_support]
  exact Set.iUnion₂_subset fun r _ ↦ p.subset_residue i r

/-- The trailing cells followed by the old bundle. At `k = 0` this is `Pᵢ`. -/
def tail (i : Fin n) (k : ℕ) : Piece :=
  (p.added i k).append (D.bundle i)
    ((D.disjoint_bundle_residue i).mono_right (p.added_subset i k)).symm

def input (i : Fin n) : Piece := p.tail i 0

theorem tail_support (i : Fin n) (k : ℕ) :
    (p.tail i k).support = (D.bundle i).support ∪
      ⋃ r : Fin (n - 1), ⋃ (_ : k ≤ r.val), (p.cell i r).support := by
  rw [tail, Piece.support_append, added_support, Set.union_comm]

theorem input_intervals (i : Fin n) :
    (p.input i).intervals =
      (List.ofFn (fun r ↦ (p.cell i r).intervals)).flatten ++ (D.bundle i).intervals := by
  simp [input, tail, Piece.append, added_intervals, roundList, List.flatMap,
    List.map_ofFn]

theorem input_contained (i : Fin n) : (p.input i).support ⊆ C.support := by
  rw [input, tail_support]
  apply Set.union_subset (D.contained i)
  exact Set.iUnion₂_subset fun r _ ↦ (p.subset_residue i r).trans D.residue_subset

theorem input_disjoint (i j : Fin n) (hij : i ≠ j) :
    Disjoint (p.input i).support (p.input j).support := by
  simp only [input, tail_support]
  rw [Set.disjoint_union_left,
    Set.disjoint_union_right, Set.disjoint_union_right]
  refine ⟨⟨D.disjoint i j hij, ?_⟩, ?_, ?_⟩
  · simp only [Set.disjoint_iUnion_right]
    intro r _
    exact (D.disjoint_bundle_residue i).mono_right (p.subset_residue j r)
  · simp only [Set.disjoint_iUnion_left]
    intro r _
    exact ((D.disjoint_bundle_residue j).mono_right (p.subset_residue i r)).symm
  · simp only [Set.disjoint_iUnion_left, Set.disjoint_iUnion_right]
    intro q _ r _
    exact p.disjoint i r j q (by intro h; exact hij (congrArg Prod.fst h))

theorem input_represents {s : RecordedState n}
    (hc : ∀ i r, s.Represents (p.cell i r).support)
    (hD : ∀ i, s.Represents (D.bundle i).support) (i : Fin n) :
    s.Represents (p.input i).support := by
  have ha : s.Represents (p.added i 0).support :=
    RepairRoundRobin.join_represents s (p.cell i)
      (fun r q h ↦ p.disjoint i r i q (by simpa using h)) (hc i) _ _
  rw [input, tail, Piece.support_append]
  exact ha.union (hD i) ((D.disjoint_bundle_residue i).mono_right (p.added_subset i 0)).symm

/-- The cake passed to Permute consists of the selected cells and old bundles.
Unselected residue remains outside this call (Algorithm `alg:repair`). -/
def cake : Piece :=
  (RepairRoundRobin.join p.input p.input_disjoint (List.ofFn id)
    (List.nodup_ofFn.mpr Function.injective_id)).piece

theorem cake_support : p.cake.support = ⋃ i, (p.input i).support := by
  rw [cake, (RepairRoundRobin.join _ _ _ _).support_eq]
  simp

theorem cake_contained : p.cake.support ⊆ C.support := by
  rw [cake_support]
  exact Set.iUnion_subset p.input_contained

theorem cake_represents {s : RecordedState n}
    (hc : ∀ i r, s.Represents (p.cell i r).support)
    (hD : ∀ i, s.Represents (D.bundle i).support) : s.Represents p.cake.support :=
  RepairRoundRobin.join_represents s p.input p.input_disjoint
    (p.input_represents hc hD) _ _

private theorem tail_boundary (i : Fin n) (k : ℕ) :
    ∃ t ∈ Set.Icc 0 (p.input i).length,
      ((p.input i).suffixAt t).support = (p.tail i k).support := by
  let L := roundList (n := n)
  let A := RepairRoundRobin.join (p.cell i)
    (fun r q h ↦ p.disjoint i r i q (by simpa using h)) (L.take k)
    (by exact (roundList_nodup (n := n)).take)
  have hdis : Disjoint A.piece.support (p.tail i k).support := by
    rw [A.support_eq, p.tail_support, Set.disjoint_iUnion_left]
    intro r
    rw [Set.disjoint_iUnion_left]
    intro hr
    rw [Set.disjoint_union_right]
    refine ⟨((D.disjoint_bundle_residue i).mono_right (p.subset_residue i r)).symm, ?_⟩
    simp only [Set.disjoint_iUnion_right]
    intro q hq
    apply p.disjoint
    intro he
    have he' : r = q := congrArg Prod.snd he
    subst q
    have : r ∈ L.drop k := (mem_roundList_drop k r).mpr hq
    exact List.disjoint_left.mp (List.disjoint_take_drop roundList_nodup (le_refl k)) hr this
  have he : p.input i = A.piece.append (p.tail i k) hdis := by
    have hi : (p.input i).intervals = (A.piece.append (p.tail i k) hdis).intervals := by
      change ((p.added i 0).intervals ++ (D.bundle i).intervals) =
        A.piece.intervals ++ ((p.added i k).intervals ++ (D.bundle i).intervals)
      rw [p.added_intervals, p.added_intervals, A.intervals_eq, ← List.append_assoc,
        ← List.flatMap_append, List.take_append_drop]
      rfl
    exact piece_eq hi
  refine ⟨A.piece.length, ⟨A.piece.length_nonneg, ?_⟩, ?_⟩
  · rw [he, Piece.length_append]
    linarith [(p.tail i k).length_nonneg]
  · rw [he, Piece.support_suffix_append_length]

/-- Any retained suffix is comparable with every cell-boundary suffix. -/
theorem comparable_tail {S : Piece} (i : Fin n) (hS : S.IsSuffix (p.input i)) (k : ℕ) :
    S.support ⊆ (p.tail i k).support ∨ (p.tail i k).support ⊆ S.support := by
  obtain ⟨t, ht, he⟩ := p.tail_boundary i k
  rw [← he]
  exact hS.support_comparable ((p.input i).suffix_isSuffix ht)

theorem tail_contains (i : Fin n) (k : ℕ) (r : Fin (n - 1)) (hr : k ≤ r.val) :
    (p.cell i r).support ⊆ (p.tail i k).support := by
  rw [tail_support]
  intro x hx
  exact Or.inr (Set.mem_iUnion₂.mpr ⟨r, hr, hx⟩)

theorem tail_disjoint (i : Fin n) (k : ℕ) (r : Fin (n - 1)) (hr : r.val < k) :
    Disjoint (p.cell i r).support (p.tail i k).support := by
  rw [tail_support, Set.disjoint_union_right]
  refine ⟨((D.disjoint_bundle_residue i).mono_right (p.subset_residue i r)).symm, ?_⟩
  simp only [Set.disjoint_iUnion_right]
  intro q hq
  apply p.disjoint i r i q
  intro h
  have he : r.val = q.val := congrArg (fun x : Fin n × Fin (n - 1) ↦ x.2.val) h
  omega

/-- Whole chosen cells retained by a suffix. -/
def complete (S : Piece) (i : Fin n) : Finset (Fin (n - 1)) :=
  univ.filter fun r ↦ (p.cell i r).support ⊆ S.support

theorem complete_upper {S : Piece} (i : Fin n) (hS : S.IsSuffix (p.input i))
    (hne : ∀ r, (p.cell i r).support.Nonempty)
    {r q : Fin (n - 1)} (hr : r ∈ p.complete S i) (hrq : r ≤ q) :
    q ∈ p.complete S i := by
  simp only [complete, mem_filter, mem_univ, true_and] at hr ⊢
  by_contra hq
  have htail : S.support ⊆ (p.tail i q.val).support :=
    (p.comparable_tail i hS q.val).resolve_right fun h ↦ hq ((p.tail_contains i _ q le_rfl).trans h)
  have hd := p.tail_disjoint i q.val r (by
    have : r ≠ q := by intro h; exact hq (h ▸ hr)
    exact Fin.lt_def.mp (lt_of_le_of_ne hrq this))
  obtain ⟨x, hx⟩ := hne r
  exact Set.disjoint_left.mp hd hx (htail (hr hx))

/-- Counting a terminal segment identifies precisely which rounds survive. -/
theorem mem_complete_iff {S : Piece} (i : Fin n) (hS : S.IsSuffix (p.input i))
    (hne : ∀ r, (p.cell i r).support.Nonempty) (r : Fin (n - 1)) :
    r ∈ p.complete S i ↔ n - 1 - (p.complete S i).card ≤ r.val := by
  have hk : (p.complete S i).card ≤ n - 1 := by
    simpa using card_le_card (subset_univ (p.complete S i))
  constructor
  · intro hr
    have hs : Ici r ⊆ p.complete S i := fun q hq ↦
      p.complete_upper i hS hne hr (mem_Ici.mp hq)
    have hc := card_le_card hs
    rw [Fin.card_Ici] at hc
    omega
  · intro hr
    by_contra hn
    have hs : p.complete S i ⊆ Ioi r := by
      intro q hq
      simp only [mem_Ioi]
      by_contra h
      exact hn (p.complete_upper i hS hne hq (le_of_not_gt h))
    have hc := card_le_card hs
    rw [Fin.card_Ioi] at hc
    omega

/-- Section 4, `lem:repair main`: the paper's level, with `-1` precisely when
the old bundle is cut. Otherwise count whole retained paper cells. -/
def level (S : Piece) (i : Fin n) : ℤ :=
  if (D.bundle i).support ⊆ S.support then (p.complete S i).card else -1

theorem level_bounds (S : Piece) (i : Fin n) :
    -1 ≤ p.level S i ∧ p.level S i ≤ (n : ℤ) - 1 := by
  have hk : (p.complete S i).card ≤ n - 1 := by
    simpa using card_le_card (subset_univ (p.complete S i))
  have hn := i.isLt
  unfold level
  split_ifs <;> omega

theorem level_nonneg_iff (S : Piece) (i : Fin n) :
    0 ≤ p.level S i ↔ (D.bundle i).support ⊆ S.support := by
  simp only [level]
  split_ifs <;> simp_all

theorem whole_level {S : Piece} (i : Fin n) (he : S.support = (p.input i).support) :
    p.level S i = (n : ℤ) - 1 := by
  have hD : (D.bundle i).support ⊆ S.support := by
    rw [he, input, tail_support]
    exact Set.subset_union_left
  have hc : p.complete S i = univ := by
    ext r
    simp only [complete, mem_filter, mem_univ, true_and, iff_true]
    rw [he]
    exact p.tail_contains i 0 r (Nat.zero_le _)
  rw [level, ite_eq_left hD, hc, card_univ, Fintype.card_fin]
  have := i.isLt
  omega

theorem cut_subset_old {S : Piece} (i : Fin n) (hS : S.IsSuffix (p.input i))
    (hcut : ¬ (D.bundle i).support ⊆ S.support) : S.support ⊆ (D.bundle i).support := by
  have he : (p.tail i (n - 1)).support = (D.bundle i).support := by
    rw [tail_support]
    simp only [show (∀ r : Fin (n - 1), ¬n - 1 ≤ r.val) from fun r ↦ by omega,
      Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty]
  have := p.comparable_tail i hS (n - 1)
  rw [he] at this
  exact this.resolve_right hcut

theorem tail_lower {S : Piece} (i : Fin n) (hS : S.IsSuffix (p.input i))
    (hne : ∀ r, (p.cell i r).support.Nonempty)
    (hD : (D.bundle i).support ⊆ S.support) :
    (p.tail i (n - 1 - (p.complete S i).card)).support ⊆ S.support := by
  rw [tail_support]
  apply Set.union_subset hD
  apply Set.iUnion₂_subset
  intro r hr
  exact (mem_filter.mp ((p.mem_complete_iff i hS hne r).mpr hr)).2

/-- A suffix may retain one partial cell in addition to its complete cells. -/
theorem tail_upper {S : Piece} (i : Fin n) (hS : S.IsSuffix (p.input i))
    (hne : ∀ r, (p.cell i r).support.Nonempty) :
    S.support ⊆ (p.tail i (n - 1 - (p.complete S i).card - 1)).support := by
  by_cases h : n - 1 - (p.complete S i).card = 0
  · rw [h, Nat.zero_sub]
    exact (by
      obtain ⟨t, _, rfl⟩ := hS
      exact (p.input i).suffix_subset t)
  · let r : Fin (n - 1) := ⟨n - 1 - (p.complete S i).card - 1, by omega⟩
    have hr : r ∉ p.complete S i := by rw [p.mem_complete_iff i hS hne]; dsimp [r]; omega
    apply (p.comparable_tail i hS r.val).resolve_right
    intro ht
    apply hr
    simp only [complete, mem_filter, mem_univ, true_and]
    exact (p.tail_contains i r.val r le_rfl).trans ht

theorem tail_value (i : Fin n) (k : ℕ) (v : Valuation) :
    v.value (p.tail i k).support = v.value (D.bundle i).support +
      ∑ r ∈ univ.filter (fun r : Fin (n - 1) ↦ k ≤ r.val), v.value (p.cell i r).support := by
  have he : (p.added i k).support =
      ⋃ r ∈ univ.filter (fun r : Fin (n - 1) ↦ k ≤ r.val), (p.cell i r).support := by
    rw [added_support]
    simp only [mem_filter, mem_univ, true_and]
  rw [tail, Piece.support_append, v.value_union (p.added i k).measurableSet_support
    (D.bundle i).measurableSet_support (p.added i k).support_subset_unit
    (D.bundle i).support_subset_unit
    ((D.disjoint_bundle_residue i).mono_right (p.added_subset i k)).symm,
    he, RepairRoundRobin.value_cells (p.cell i)
      (fun r q h ↦ p.disjoint i r i q (by simpa using h))]
  exact add_comm _ _

theorem retained_lower {S : Piece} (i : Fin n) (hS : S.IsSuffix (p.input i))
    (hne : ∀ r, (p.cell i r).support.Nonempty) (hD : (D.bundle i).support ⊆ S.support)
    (v : Valuation) :
    v.value (D.bundle i).support + ∑ r ∈ p.complete S i, v.value (p.cell i r).support ≤
      v.value S.support := by
  have h := v.value_mono (p.tail i _).measurableSet_support S.measurableSet_support
    (p.tail_lower i hS hne hD) S.support_subset_unit
  rw [p.tail_value] at h
  have he : univ.filter (fun r : Fin (n - 1) ↦ n - 1 - (p.complete S i).card ≤ r.val) =
      p.complete S i := by
    ext r
    simp only [mem_filter, mem_univ, true_and, p.mem_complete_iff i hS hne]
  rwa [he] at h

/-- Section 4, Inequality `eq:levels` in the proof of `lem:repair main`:
an agent strictly prefers her own labelled suffix to any suffix two levels lower. -/
theorem higher_levels_preferred (hn : 2 ≤ n) (S : Fin n → Piece)
    (hS : ∀ i, (S i).IsSuffix (p.input i))
    (hne : ∀ i r, (p.cell i r).support.Nonempty)
    (v : Fin n → Valuation) (ε : ℝ)
    (halmost : ∀ i j, (v i).value (D.bundle j).support ≤
      (v i).value (D.bundle i).support + ε * (v i).value D.residue)
    (hcompare : ∀ (r q : Fin (n - 1)), r.val < q.val → ∀ i j,
      (v i).value (p.cell j q).support ≤ (v i).value (p.cell i r).support)
    (hlast : ∀ i, ε * (v i).value D.residue <
      (v i).value (p.cell i ⟨n - 2, by omega⟩).support)
    (i j : Fin n) (hlevel : p.level (S j) j + 2 ≤ p.level (S i) i) :
    (v i).value (S j).support < (v i).value (S i).support := by
  have hbi := p.level_bounds (S i) i
  have hbj := p.level_bounds (S j) j
  have hDi : (D.bundle i).support ⊆ (S i).support :=
    (p.level_nonneg_iff _ _).mp (by omega)
  have hli : p.level (S i) i = (p.complete (S i) i).card := by
    simp only [level, ite_eq_left hDi]
  let last : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hlastmem : last ∈ p.complete (S i) i := by
    rw [p.mem_complete_iff i (hS i) (hne i)]
    dsimp [last]
    omega
  have hlower := p.retained_lower i (hS i) (hne i) hDi (v i)
  have hsum : (∑ r ∈ (p.complete (S i) i).erase last, (v i).value (p.cell i r).support) +
      (v i).value (p.cell i last).support =
      ∑ r ∈ p.complete (S i) i, (v i).value (p.cell i r).support :=
    sum_erase_add _ _ hlastmem
  by_cases hDj : (D.bundle j).support ⊆ (S j).support
  · have hlj : p.level (S j) j = (p.complete (S j) j).card := by
      simp only [level, ite_eq_left hDj]
    let A := univ.filter (fun r : Fin (n - 1) ↦ n - 1 - (p.complete (S j) j).card - 1 ≤ r.val)
    let pred : Fin (n - 1) → Fin (n - 1) := fun r ↦ ⟨r.val - 1, by omega⟩
    have hA : ∀ r ∈ A, 0 < r.val := by
      intro r hr
      have hr' : n - 1 - (p.complete (S j) j).card - 1 ≤ r.val := (mem_filter.mp hr).2
      omega
    have hinj : Set.InjOn pred A := by
      intro r hr q hq he
      have := congrArg Fin.val he
      have := hA r hr
      have := hA q hq
      apply Fin.ext
      dsimp [pred] at *
      omega
    have hmap : A.image pred ⊆ (p.complete (S i) i).erase last := by
      intro r hr
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hr
      have hq' : n - 1 - (p.complete (S j) j).card - 1 ≤ q.val := (mem_filter.mp hq).2
      simp only [mem_erase, p.mem_complete_iff i (hS i) (hne i)]
      constructor
      · intro he
        have := congrArg Fin.val he
        dsimp [pred, last] at this
        have := q.isLt
        omega
      · dsimp [pred]
        omega
    have hsumle : (∑ r ∈ A, (v i).value (p.cell j r).support) ≤
        ∑ r ∈ (p.complete (S i) i).erase last, (v i).value (p.cell i r).support := by
      apply sum_le_sum_of_injOn pred hinj hmap
      · intro r hr
        apply hcompare (pred r) r (by dsimp [pred]; have := hA r hr; omega)
      · intro r _ _
        exact (v i).value_nonneg (p.cell i r).measurableSet_support (p.cell i r).support_subset_unit
    have hupper := (v i).value_mono (S j).measurableSet_support
      (p.tail j _).measurableSet_support (p.tail_upper j (hS j) (hne j))
      (p.tail j _).support_subset_unit
    rw [p.tail_value] at hupper
    change (v i).value (S j).support ≤ (v i).value (D.bundle j).support +
      ∑ r ∈ A, (v i).value (p.cell j r).support at hupper
    have := halmost i j
    have := hlast i
    change ε * (v i).value D.residue < (v i).value (p.cell i last).support at this
    linarith
  · have hupper := (v i).value_mono (S j).measurableSet_support
      (D.bundle j).measurableSet_support (p.cut_subset_old j (hS j) hDj)
      (D.bundle j).support_subset_unit
    have hnonneg : 0 ≤ ∑ r ∈ (p.complete (S i) i).erase last,
        (v i).value (p.cell i r).support :=
      sum_nonneg fun r _ ↦ (v i).value_nonneg
        (p.cell i r).measurableSet_support (p.cell i r).support_subset_unit
    have := halmost i j
    have := hlast i
    change ε * (v i).value D.residue < (v i).value (p.cell i last).support at this
    linarith

end Picks

/-- Section 4, proof of `lem:repair main`: with both extreme levels present,
`n` pieces cannot occupy all `n+1` levels. -/
theorem missing_level (hn : 2 ≤ n) (ℓ : Fin n → ℤ)
    (hlo : ∃ i, ℓ i = -1) (hhi : ∃ i, ℓ i = (n : ℤ) - 1) :
    ∃ gap : ℤ, 0 ≤ gap ∧ gap ≤ (n : ℤ) - 2 ∧ ∀ i, ℓ i ≠ gap := by
  by_contra h
  push Not at h
  have hsub : Icc (-1 : ℤ) ((n : ℤ) - 1) ⊆ univ.image ℓ := by
    intro gap hgap
    obtain ⟨hl, hu⟩ := mem_Icc.mp hgap
    apply mem_image.mpr
    by_cases he : gap = -1
    · obtain ⟨i, hi⟩ := hlo
      exact ⟨i, mem_univ _, hi.trans he.symm⟩
    by_cases he' : gap = (n : ℤ) - 1
    · obtain ⟨i, hi⟩ := hhi
      exact ⟨i, mem_univ _, hi.trans he'.symm⟩
    obtain ⟨i, hi⟩ := h gap (by omega) (by omega)
    exact ⟨i, mem_univ _, hi⟩
  have hc := (card_le_card hsub).trans (card_image_le (s := univ) (f := ℓ))
  rw [Int.card_Icc, card_univ, Fintype.card_fin] at hc
  omega

/-- Section 4, the missing-level and Permute-(ii) argument in `lem:repair main`.
Input labels are related to recipients by `π`; no label is identified with its holder. -/
theorem old_bundle_subset_of_preference (p : Picks D) (hn : 2 ≤ n)
    {K : Piece} (W : Allocation n K) (π : Equiv.Perm (Fin n))
    (v : Fin n → Valuation) (hEF : W.EnvyFree v)
    (hwhole : ∃ a, (W.bundle a).support = (p.input (π a)).support)
    (hindiff : ∀ A : Finset (Fin n), A.Nonempty →
      (∀ a ∈ A, (W.bundle a).support ≠ (p.input (π a)).support) →
      ∃ a ∈ A, ∃ b ∉ A, (v b).value (W.bundle a).support = (v b).value (W.bundle b).support)
    (hpref : ∀ i j,
      p.level (W.bundle (π.symm j)) j + 2 ≤ p.level (W.bundle (π.symm i)) i →
      (v i).value (W.bundle (π.symm j)).support < (v i).value (W.bundle (π.symm i)).support) :
    ∀ i, (D.bundle i).support ⊆ (W.bundle (π.symm i)).support := by
  let ℓ := fun i ↦ p.level (W.bundle (π.symm i)) i
  intro cut
  by_contra hcut
  have hlo : ℓ cut = -1 := by simp only [ℓ, Picks.level, ite_eq_right hcut]
  obtain ⟨a, ha⟩ := hwhole
  have hhi : ℓ (π a) = (n : ℤ) - 1 := by
    dsimp [ℓ]
    simpa using p.whole_level (π a) ha
  obtain ⟨gap, hgap0, hgapn, hmissing⟩ := missing_level hn ℓ ⟨cut, hlo⟩ ⟨π a, hhi⟩
  let H := univ.filter fun i ↦ gap < ℓ i
  let L := univ.filter fun i ↦ ℓ i < gap
  have hlow : ∀ i, i ∈ L ↔ ℓ i < gap := by intro i; simp [L]
  have hhigh : ∀ i, i ∈ H ↔ gap < ℓ i := by intro i; simp [H]
  have hsep : ∀ i ∈ H, ∀ j ∈ L,
      (v i).value (W.bundle (π.symm j)).support < (v i).value (W.bundle i).support := by
    intro i hi j hj
    have hi' := (hhigh i).mp hi
    have hj' := (hlow j).mp hj
    have h := hpref i j (by change ℓ j + 2 ≤ ℓ i; omega)
    exact h.trans_le (hEF i (π.symm i))
  have hmap : Set.MapsTo π H H := by
    intro i hi
    apply (hhigh (π i)).mpr
    by_contra h
    have hj : π i ∈ L := (hlow _).mpr (by have := hmissing (π i); omega)
    have := hsep i hi (π i) hj
    simp at this
  have hsurj : Set.SurjOn π H H :=
    surjOn_of_injOn_of_card_le π hmap π.injective.injOn (le_refl _)
  have hmapL : ∀ j ∈ L, π j ∈ L := by
    intro j hj
    apply (hlow _).mpr
    by_contra h
    have hπj : π j ∈ H := (hhigh _).mpr (by have := hmissing (π j); omega)
    obtain ⟨i, hi, he⟩ := hsurj hπj
    have hij := π.injective he
    subst i
    have := (hhigh j).mp hi
    have := (hlow j).mp hj
    omega
  have hLne : L.Nonempty := ⟨cut, (hlow cut).mpr (by omega)⟩
  have hproper : ∀ j ∈ L, (W.bundle j).support ≠ (p.input (π j)).support := by
    intro j hj he
    have ht : ℓ (π j) = (n : ℤ) - 1 := by
      dsimp [ℓ]
      simpa using p.whole_level (π j) he
    have := (hlow (π j)).mp (hmapL j hj)
    omega
  obtain ⟨j, hj, i, hi, he⟩ := hindiff L hLne hproper
  have hiH : i ∈ H := (hhigh i).mpr (by
    have := hmissing i
    have : ¬ℓ i < gap := fun h ↦ hi ((hlow i).mpr h)
    omega)
  have hstrict := hsep i hiH (π j) (hmapL j hj)
  simp only [Equiv.symm_apply_apply] at hstrict
  exact (ne_of_lt hstrict) he

/-- Section 4, proof of `lem:repair main`: the suffix, whole-piece, and
indifference guarantees of Permute preserve every old bundle after round robin. -/
theorem Picks.old_bundle_subset (p : Picks D) (hn : 2 ≤ n)
    {K : Piece} (W : Allocation n K) (π : Equiv.Perm (Fin n))
    (v : Fin n → Valuation) (ε : ℝ)
    (hS : ∀ i, (W.bundle i).IsSuffix (p.input (π i)))
    (hne : ∀ i r, (p.cell i r).support.Nonempty)
    (halmost : ∀ i j, (v i).value (D.bundle j).support ≤
      (v i).value (D.bundle i).support + ε * (v i).value D.residue)
    (hcompare : ∀ (r q : Fin (n - 1)), r.val < q.val → ∀ i j,
      (v i).value (p.cell j q).support ≤ (v i).value (p.cell i r).support)
    (hlast : ∀ i, ε * (v i).value D.residue <
      (v i).value (p.cell i ⟨n - 2, by omega⟩).support)
    (hEF : W.EnvyFree v)
    (hwhole : ∃ a, (W.bundle a).support = (p.input (π a)).support)
    (hindiff : ∀ A : Finset (Fin n), A.Nonempty →
      (∀ a ∈ A, (W.bundle a).support ≠ (p.input (π a)).support) →
      ∃ a ∈ A, ∃ b ∉ A, (v b).value (W.bundle a).support = (v b).value (W.bundle b).support) :
    ∀ i, (D.bundle i).support ⊆ (W.bundle (π.symm i)).support := by
  apply old_bundle_subset_of_preference p hn W π v hEF hwhole hindiff
  exact p.higher_levels_preferred hn (fun i ↦ W.bundle (π.symm i))
    (fun i ↦ by simpa using hS (π.symm i)) hne v ε halmost hcompare hlast

/-- The actual selected paper cells of the recorded round-robin protocol. -/
def ofRoundRobin {m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (hsub : ∀ c, (cells c).support ⊆ D.residue) : Picks D where
  cell i r := cells (RepairRoundRobin.chosen s cells hn d r i)
  disjoint i r j q h := RepairRoundRobin.chosen_disjoint s cells hn d hcap hd
    (r, i) (q, j) (by
      intro he
      apply h
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he))
  subset_residue i r := hsub _

/-- The construction uses the existing ordered chosen bundle without changing
the order of either its cells or their component intervals. -/
theorem ofRoundRobin_added {m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (hsub : ∀ c, (cells c).support ⊆ D.residue) (i : Fin n) :
    (ofRoundRobin s cells hn d hcap hd hsub).added i 0 =
      RepairRoundRobin.bundle s cells hn d hcap hd i := by
  apply piece_eq
  rw [Picks.added_intervals, RepairRoundRobin.bundle_intervals]
  simp only [Picks.roundList, List.drop_zero, List.flatMap, List.map_ofFn,
    Function.comp_def, id_eq, ofRoundRobin]

/-- Section 4, `lem:repair main`: the proved recorded round robin supplies all
the hypotheses of the levels argument. The old bundle labelled `i` is held by
recipient `π.symm i`. The almost-envy-free hypothesis is exactly Repair's. -/
theorem roundRobin_old_bundle_subset {m : ℕ} (hn : 2 ≤ n)
    (s : RecordedState n) (cells : Fin m → Piece) (d : Fin m)
    (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (hsub : ∀ c, (cells c).support ⊆ D.residue)
    (R : Piece) (hR : R.support = D.residue) (ε : ℝ) (hε : 0 < ε)
    (v : Fin n → Valuation) (hpos : ∀ i, 0 < (v i).value D.residue)
    (g : RepairRoundRobin.Guarantees s cells (by omega) d hcap hd R ε v)
    (halmost : ∀ i j, (v i).value (D.bundle j).support - ε * (v i).value D.residue ≤
      (v i).value (D.bundle i).support)
    {K : Piece} (W : Allocation n K) (π : Equiv.Perm (Fin n))
    (hS : ∀ i, (W.bundle i).IsSuffix
      ((ofRoundRobin s cells (by omega) d hcap hd hsub).input (π i)))
    (hEF : W.EnvyFree v)
    (hwhole : ∃ a, (W.bundle a).support =
      ((ofRoundRobin s cells (by omega) d hcap hd hsub).input (π a)).support)
    (hindiff : ∀ A : Finset (Fin n), A.Nonempty →
      (∀ a ∈ A, (W.bundle a).support ≠
        ((ofRoundRobin s cells (by omega) d hcap hd hsub).input (π a)).support) →
      ∃ a ∈ A, ∃ b ∉ A, (v b).value (W.bundle a).support = (v b).value (W.bundle b).support) :
    ∀ i, (D.bundle i).support ⊆ (W.bundle (π.symm i)).support := by
  let p := ofRoundRobin s cells (by omega) d hcap hd hsub
  have hstrict : ∀ i r, 0 < (v i).value (p.cell i r).support := by
    intro i r
    have hh := g.pick_strict r i
    rw [hR] at hh
    exact (mul_pos hε (hpos i)).trans hh
  apply p.old_bundle_subset hn W π v ε hS ?_ ?_ g.comparison ?_ hEF hwhole hindiff
  · intro i r
    by_contra he
    have he' : (p.cell i r).support = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    have hh := hstrict i r
    rw [he', Valuation.value_empty] at hh
    exact lt_irrefl _ hh
  · intro i j
    have := halmost i j
    linarith
  · intro i
    simpa only [p, ofRoundRobin, hR] using g.last_pick hn i

/-- Section 4, Algorithm `alg:repair`, line `rep:permute`, and the preservation
argument in `lem:repair main`: a correct Permute call on the ordered enlarged
bundles preserves each old bundle under the inverse assignment. -/
theorem Picks.permute_preserves (p : Picks D) (hn : 2 ≤ n)
    (P : PermuteProtocol) (hP : P.Correct) (s : RecordedState n)
    (v : Fin n → Valuation) (hs : s.Correct v)
    (hc : ∀ i r, s.Represents (p.cell i r).support)
    (hD : ∀ i, s.Represents (D.bundle i).support)
    (hne : ∀ i r, (p.cell i r).support.Nonempty) (ε : ℝ)
    (halmost : ∀ i j, (v i).value (D.bundle j).support - ε * (v i).value D.residue ≤
      (v i).value (D.bundle i).support)
    (hcompare : ∀ (r q : Fin (n - 1)), r.val < q.val → ∀ i j,
      (v i).value (p.cell j q).support ≤ (v i).value (p.cell i r).support)
    (hlast : ∀ i, ε * (v i).value D.residue <
      (v i).value (p.cell i ⟨n - 2, by omega⟩).support) :
    ∃ (r : PermuteResult n p.cake) (count : ℕ),
      (P n (by omega) s p.cake p.input).Runs v r count ∧ r.state.Correct v ∧
      r.toRecordedAllocationResult.Inherits s ∧ r.allocation.EnvyFree v ∧
      (∀ i, (r.allocation.bundle i).IsSuffix (p.input (r.assignment i))) ∧
      (∀ i, (D.bundle i).support ⊆ (r.allocation.bundle (r.assignment.symm i)).support) ∧
      count ≤ permuteQueryBound n := by
  obtain ⟨r, count, hrun, hrs, hinherits, hEF, hS, hwhole, hindiff, hcost⟩ :=
    hP n (by omega) s p.cake p.input v hs (p.input_represents hc hD)
      p.input_disjoint p.cake_support.symm
  refine ⟨r, count, hrun, hrs, hinherits, hEF, hS, ?_, hcost⟩
  apply p.old_bundle_subset hn r.allocation r.assignment v ε hS hne ?_
    hcompare hlast hEF hwhole hindiff
  intro i j
  have := halmost i j
  linarith

/-- Section 4, Algorithm `alg:repair`, lines `rep:pieces` and `rep:permute`:
the recorded round-robin guarantees and Repair's original valuation hypotheses
give a Permute execution preserving all old bundles, conditional only on its
existing correctness contract. -/
theorem roundRobin_permute_preserves {m : ℕ} (hn : 2 ≤ n)
    (s : RecordedState n) (cells : Fin m → Piece) (d : Fin m)
    (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (hsub : ∀ c, (cells c).support ⊆ D.residue)
    (R : Piece) (hR : R.support = D.residue) (ε : ℝ) (hε : 0 < ε)
    (v : Fin n → Valuation) (hpos : ∀ i, 0 < (v i).value D.residue)
    (g : RepairRoundRobin.Guarantees s cells (by omega) d hcap hd R ε v)
    (halmost : ∀ i j, (v i).value (D.bundle j).support - ε * (v i).value D.residue ≤
      (v i).value (D.bundle i).support)
    (P : PermuteProtocol) (hP : P.Correct) (hs : s.Correct v)
    (hD : ∀ i, s.Represents (D.bundle i).support) :
    let p := ofRoundRobin s cells (by omega) d hcap hd hsub
    ∃ (r : PermuteResult n p.cake) (count : ℕ),
      (P n (by omega) s p.cake p.input).Runs v r count ∧ r.state.Correct v ∧
      r.toRecordedAllocationResult.Inherits s ∧ r.allocation.EnvyFree v ∧
      (∀ i, (r.allocation.bundle i).IsSuffix (p.input (r.assignment i))) ∧
      (∀ i, (D.bundle i).support ⊆ (r.allocation.bundle (r.assignment.symm i)).support) ∧
      count ≤ permuteQueryBound n := by
  let p := ofRoundRobin s cells (by omega) d hcap hd hsub
  have hrep : ∀ i, s.Represents (p.input i).support := by
    intro i
    rw [Picks.input, Picks.tail, Piece.support_append]
    have ha : s.Represents (p.added i 0).support := by
      rw [ofRoundRobin_added]
      exact g.bundle_represents i
    exact ha.union (hD i) ((D.disjoint_bundle_residue i).mono_right (p.added_subset i 0)).symm
  obtain ⟨r, count, hrun, hrs, hinherits, hEF, hS, hwhole, hindiff, hcost⟩ :=
    hP n (by omega) s p.cake p.input v hs hrep p.input_disjoint p.cake_support.symm
  refine ⟨r, count, hrun, hrs, hinherits, hEF, hS, ?_, hcost⟩
  exact roundRobin_old_bundle_subset hn s cells d hcap hd hsub R hR ε hε v hpos g
    halmost r.allocation r.assignment hS hEF hwhole hindiff

end CakeCuttingPsomas.RepairLevels
