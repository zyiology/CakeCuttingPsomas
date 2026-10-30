module

public import CakeCuttingPsomas.Traversal
public import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-! # Consecutive cells between pooled traversal marks

Mathematical geometry shared by Section 4's Repair partition and Section 5's
proof-only discretization. Cells follow the specified interval-list traversal.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.TraversalPartition

attribute [local instance] Classical.propDecidable

/-- The next pooled mark, or the end of the residue if no later mark remains. -/
def next (L : ℝ) (points : Finset ℝ) (a : ℝ) : ℝ :=
  if h : (points.filter (a < ·)).Nonempty then (points.filter (a < ·)).min' h else L

theorem next_spec {L a : ℝ} {points : Finset ℝ}
    (hpoints : ∀ x ∈ points, 0 < x ∧ x < L) (ha : a < L) :
    a < next L points a ∧ next L points a ≤ L ∧
      (next L points a = L ∨ next L points a ∈ points) ∧
      ∀ x ∈ points, a < x → next L points a ≤ x := by
  unfold next
  split_ifs with h
  · have hm := Finset.min'_mem _ h
    obtain ⟨hmP, ham⟩ := Finset.mem_filter.mp hm
    exact ⟨ham, (hpoints _ hmP).2.le, Or.inr hmP,
      fun x hx hax ↦ Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hx, hax⟩)⟩
  · refine ⟨ha, le_rfl, Or.inl rfl, ?_⟩
    intro x hx hax
    exact (h ⟨x, Finset.mem_filter.mpr ⟨hx, hax⟩⟩).elim

/-- A paper cell may span several recorded intervals, including gaps in `R`. -/
def cell (R : Piece) (points : Finset ℝ) (a : ℝ) : Piece :=
  (R.prefixAt (next R.length points a)).diff (R.prefixAt a)

/-- Cell labels are the initial boundary and the distinct pooled marks. -/
def starts (points : Finset ℝ) : Finset ℝ := insert 0 points

theorem start_lt {R : Piece} {points : Finset ℝ}
    (hL : 0 < R.length) (hp : ∀ x ∈ points, 0 < x ∧ x < R.length)
    {a : ℝ} (ha : a ∈ starts points) : a < R.length := by
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact hL
  · exact (hp a ha).2

@[simp] theorem support_cell (R : Piece) (points : Finset ℝ) (a : ℝ) :
    (cell R points a).support =
      (R.prefixAt (next R.length points a)).support \ (R.prefixAt a).support :=
  Piece.support_diff _ _

/-- Section 4, `line:rep:cells`: cells between successive pooled marks cover
exactly the residue and are pairwise disjoint, regardless of inherited cuts. -/
theorem cells_partition (R : Piece) (points : Finset ℝ) (hL : 0 < R.length)
    (hp : ∀ x ∈ points, 0 < x ∧ x < R.length) :
    (⋃ a : {a // a ∈ starts points}, (cell R points a).support) = R.support ∧
      ∀ a b : {a // a ∈ starts points}, a ≠ b →
        Disjoint (cell R points a).support (cell R points b).support := by
  constructor
  · apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
      exact R.prefix_subset _ ((support_cell R points a ▸ ha).1)
    · intro y hy
      let S := (starts points).filter fun a ↦ y ∉ (R.prefixAt a).support
      have hS : S.Nonempty := ⟨0, by simp [S, starts]⟩
      let a := S.max' hS
      have ha := Finset.mem_filter.mp (Finset.max'_mem S hS)
      obtain ⟨hab, hbL, hb, _⟩ := next_spec hp (start_lt hL hp ha.1)
      have hyb : y ∈ (R.prefixAt (next R.length points a)).support := by
        by_contra hn
        rcases hb with hb | hb
        · rw [hb, Piece.prefix_length] at hn
          exact hn hy
        · have hbS : next R.length points a ∈ S :=
            Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hb, hn⟩
          have := Finset.le_max' S _ hbS
          change next R.length points a ≤ a at this
          linarith
      exact Set.mem_iUnion.mpr ⟨⟨a, ha.1⟩, by rw [support_cell]; exact ⟨hyb, ha.2⟩⟩
  · have ordered (a b : {a // a ∈ starts points}) (hab : a.val < b.val) :
        Disjoint (cell R points a).support (cell R points b).support := by
      have hbP : b.val ∈ points := by
        rcases Finset.mem_insert.mp b.property with hb | hb
        · have ha0 : 0 ≤ a.val := by
            rcases Finset.mem_insert.mp a.property with ha | ha
            · exact ha ▸ le_rfl
            · exact (hp _ ha).1.le
          linarith
        · exact hb
      have hnext := (next_spec hp (start_lt hL hp a.property)).2.2.2 b hbP hab
      apply Set.disjoint_left.mpr
      intro y hy hz
      rw [support_cell] at hy hz
      exact hz.2 (R.prefix_mono hnext hy.1)
    intro a b hab
    rcases lt_trichotomy a.val b.val with h | h | h
    · exact ordered a b h
    · exact (hab (Subtype.ext h)).elim
    · exact (ordered b a h).symm

/-- Every cell has nonempty support; zero-valued stretches are retained. -/
theorem cell_nonempty (R : Piece) (points : Finset ℝ) (hL : 0 < R.length)
    (hp : ∀ x ∈ points, 0 < x ∧ x < R.length)
    {a : ℝ} (ha : a ∈ starts points) : (cell R points a).support.Nonempty := by
  have ha0 : 0 ≤ a := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    · exact (hp a ha).1.le
  obtain ⟨hab, hb, _⟩ := next_spec hp (start_lt hL hp ha)
  obtain ⟨y, hyb, hya⟩ := R.exists_mem_prefix_diff ha0 hab hb
  exact ⟨y, by rw [support_cell]; exact ⟨hyb, hya⟩⟩

/-- The paper's cell count depends only on new marks, not old recorded intervals. -/
theorem card_starts {points : Finset ℝ} (hp : ∀ x ∈ points, 0 < x) :
    (starts points).card = points.card + 1 := by
  apply Finset.card_insert_of_notMem
  intro h
  exact (lt_irrefl (0 : ℝ)) (hp 0 h)

private theorem value_cell_add (R : Piece) (points : Finset ℝ) (a : ℝ)
    (v : Valuation) (hab : a ≤ next R.length points a) :
    v.value (cell R points a).support + v.value (R.prefixAt a).support =
      v.value (R.prefixAt (next R.length points a)).support := by
  have hd : Disjoint (cell R points a).support (R.prefixAt a).support := by
    rw [support_cell]
    exact Set.disjoint_left.mpr fun _ hx hy ↦ hx.2 hy
  rw [← v.value_union (cell R points a).measurableSet_support
    (R.prefixAt a).measurableSet_support (cell R points a).support_subset_unit
    (R.prefixAt a).support_subset_unit hd, support_cell,
    Set.sdiff_union_of_subset (R.prefix_mono hab)]


/-- Section 4, `line:rep:cells`: no common cell can cross an equal-value
boundary of any agent, so its value is at most that agent's `1/M` share. -/
theorem cell_value_le (R : Piece) (points : Finset ℝ) (M : ℕ) (v : Valuation)
    (hM : 0 < M) (hpos : 0 < v.value R.support) (hL : 0 < R.length)
    (hp : ∀ x ∈ points, 0 < x ∧ x < R.length)
    (hmarks : ∀ k : Fin (M - 1), ∃ x ∈ points,
      v.value (R.prefixAt x).support = (k.val + 1 : ℕ) * (v.value R.support / M))
    (a : ℝ) (ha : a ∈ starts points) :
    v.value (cell R points a).support ≤ v.value R.support / M := by
  let t := v.value R.support / M
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have ht : 0 < t := div_pos hpos hm
  have htotal : (M : ℝ) * t = v.value R.support := mul_div_cancel₀ _ (ne_of_gt hm)
  let A := v.value (R.prefixAt a).support
  let B := v.value (R.prefixAt (next R.length points a)).support
  have hA : 0 ≤ A := v.value_nonneg (R.prefixAt a).measurableSet_support
    (R.prefixAt a).support_subset_unit
  have hB : B ≤ v.value R.support := v.value_mono
    (R.prefixAt _).measurableSet_support R.measurableSet_support
    (R.prefix_subset _) R.support_subset_unit
  obtain ⟨hab, _, _, hnext⟩ := next_spec hp (start_lt hL hp ha)
  have hadd := value_cell_add R points a v hab.le
  change v.value (cell R points a).support + A = B at hadd
  by_contra hbig
  have hgap : A + t < B := by change ¬_ ≤ t at hbig; linarith
  let k := ⌊A / t⌋₊
  have hklo : (k : ℝ) * t ≤ A := (le_div_iff₀ ht).mp (Nat.floor_le (div_nonneg hA ht.le))
  have hkhi : A < ((k : ℝ) + 1) * t := (div_lt_iff₀ ht).mp (Nat.lt_floor_add_one (A / t))
  have hkM : k + 1 < M := by
    have : ((k : ℝ) + 1) * t < (M : ℝ) * t := by linarith
    have : (k : ℝ) + 1 < M := (mul_lt_mul_iff_left₀ ht).mp this
    exact_mod_cast this
  obtain ⟨x, hx, hvx⟩ := hmarks ⟨k, by omega⟩
  have hvx' : v.value (R.prefixAt x).support = ((k : ℝ) + 1) * t := by
    simpa [t] using hvx
  have hax : a < x := by
    by_contra hn
    have hh := v.monotone_value_prefix R (le_of_not_gt hn)
    dsimp only at hh
    rw [hvx'] at hh
    change _ ≤ A at hh
    linarith
  have hxb : x < next R.length points a := by
    by_contra hn
    have hh := v.monotone_value_prefix R (le_of_not_gt hn)
    dsimp only at hh
    rw [hvx'] at hh
    change B ≤ _ at hh
    nlinarith
  exact (not_lt_of_ge (hnext x hx hax)) hxb

/-- Section 4, proof of `lem:repair main`: one positive-valued agent alone
supplies `M-1` distinct interior marks. -/
theorem marks_card_le (R : Piece) (points : Finset ℝ) (M : ℕ) (v : Valuation)
    (hM : 0 < M) (hpos : 0 < v.value R.support)
    (hmarks : ∀ k : Fin (M - 1), ∃ x ∈ points,
      v.value (R.prefixAt x).support = (k.val + 1 : ℕ) * (v.value R.support / M)) :
    M - 1 ≤ points.card := by
  choose x hx hv using hmarks
  have ht : 0 < v.value R.support / M := div_pos hpos (by exact_mod_cast hM)
  have hinj : Function.Injective x := by
    intro i j he
    have hh : ((i.val + 1 : ℕ) : ℝ) * (v.value R.support / M) =
        ((j.val + 1 : ℕ) : ℝ) * (v.value R.support / M) := by rw [← hv i, ← hv j, he]
    have hh' := (mul_left_inj' (ne_of_gt ht)).mp hh
    have hhN : i.val + 1 = j.val + 1 := by exact_mod_cast hh'
    apply Fin.ext
    omega
  have hc := Finset.card_le_card (show Finset.univ.image x ⊆ points from by
    intro y hy; obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy; exact hx k)
  simpa [Finset.card_image_of_injective _ hinj] using hc


/-- A pooled mark is a cell boundary, even when it lies at an old interval end. -/
theorem cell_does_not_cross_mark (R : Piece) (points : Finset ℝ) (hL : 0 < R.length)
    (hp : ∀ x ∈ points, 0 < x ∧ x < R.length)
    {a x : ℝ} (ha : a ∈ starts points) (hx : x ∈ points) :
    (cell R points a).support ⊆ (R.prefixAt x).support ∨
      Disjoint (cell R points a).support (R.prefixAt x).support := by
  by_cases hax : a < x
  · left
    intro y hy
    rw [support_cell] at hy
    exact R.prefix_mono ((next_spec hp (start_lt hL hp ha)).2.2.2 x hx hax) hy.1
  · right
    apply Set.disjoint_left.mpr
    intro y hy hz
    rw [support_cell] at hy
    exact hy.2 (R.prefix_mono (le_of_not_gt hax) hz)

end CakeCuttingPsomas.TraversalPartition
