module

public import CakeCuttingPsomas.Piece
public import CakeCuttingPsomas.Valuation
public import CakeCuttingPsomas.Protocol
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact

/-! # Smallest interval cuts

Existence of the Robertson–Webb cuts from the introduction and the prefix-cut
conventions of Section 1.3 of `paper/main.tex`. Only integrability and
nonnegativity are used; recursive inputs may have value zero.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas

namespace Valuation

/-- Closed and half-open intervals have the same value for density valuations. -/
theorem value_Icc_eq_Ico (v : Valuation) (a b : ℝ) :
    v.value (Set.Icc a b) = v.value (Set.Ico a b) :=
  MeasureTheory.integral_Icc_eq_integral_Ico

@[simp]
theorem value_singleton (v : Valuation) (a : ℝ) : v.value {a} = 0 := by
  simp [value]

/-- Cumulative interval value is continuous, as used in Section 1.3's
existence argument for prefix cuts. No strict positivity is required. -/
theorem continuousOn_value_Icc (v : Valuation) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    ContinuousOn (fun x ↦ v.value (Set.Icc a x)) (Set.Icc a b) :=
  intervalIntegral.continuousOn_primitive_Icc
    (v.integrableOn fun _ hx ↦ ⟨ha.trans hx.1, hx.2.trans hb⟩)

theorem monotoneOn_value_Icc (v : Valuation) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    MonotoneOn (fun x ↦ v.value (Set.Icc a x)) (Set.Icc a b) := by
  intro x _ y hy hxy
  exact v.value_mono measurableSet_Icc measurableSet_Icc
    (Set.Icc_subset_Icc_right hxy) (fun _ hz ↦ ⟨ha.trans hz.1, hz.2.trans (hy.2.trans hb)⟩)

/-- A smallest cut exists for every legal target on an interval, including
zero targets and flat regions. This is the interval case of Section 1.3's
prefix-cut existence statement and the introduction's Cut-query convention. -/
theorem exists_smallest_cut (v : Valuation) {a b t : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (ht : 0 ≤ t) (htb : t ≤ v.value (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, v.value (Set.Icc a x) = t ∧
      ∀ y ∈ Set.Icc a b, v.value (Set.Icc a y) = t → x ≤ y := by
  have hc := v.continuousOn_value_Icc ha hb
  have hstart : v.value (Set.Icc a a) = 0 := by simp
  obtain ⟨x, hx, hxt⟩ := intermediate_value_Icc hab hc (by simpa [hstart] using And.intro ht htb)
  let S : Set (Set.Icc a b) := {y | v.value (Set.Icc a y.val) = t}
  have hS : IsCompact S := (isClosed_eq hc.domRestrict continuous_const).isCompact
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn ⟨⟨x, hx⟩, hxt⟩ continuous_subtype_val.continuousOn
  exact ⟨z.val, z.property, hz, fun y hy hyt ↦ hmin (show (⟨y, hy⟩ : Set.Icc a b) ∈ S from hyt)⟩

/-- A stored interval's value agrees with the closed interval used by queries. -/
theorem value_interval (v : Valuation) (I : CakeInterval) :
    v.value I.support = v.value (Set.Icc I.left I.right) := by
  unfold CakeInterval.support
  split
  · rfl
  · exact (v.value_Icc_eq_Ico _ _).symm

/-- Geometric prefixes have the cumulative value queried by Cut. Endpoint
ownership changes only a null singleton. -/
theorem value_before (v : Valuation) (I : CakeInterval) {x : ℝ}
    (hx : x ∈ Set.Icc I.left I.right) :
    v.value (I.before x).support = v.value (Set.Icc I.left x) := by
  rw [CakeInterval.support_before]
  split_ifs with h
  · have : x = I.right := le_antisymm hx.2 h
    subst x
    exact v.value_interval I
  · rw [v.value_Icc_eq_Ico]
    congr 1
    ext y
    simp only [CakeInterval.support, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
    split_ifs <;> simp_all only [Set.mem_Icc, Set.mem_Ico] <;> grind

/-- The value of a clamped geometric interval prefix is continuous on all
positions; this allows ordered pieces to concatenate such prefixes. -/
theorem continuous_value_before (v : Valuation) (I : CakeInterval) :
    Continuous (fun x ↦ v.value (I.before x).support) := by
  let c : ℝ → ℝ := fun x ↦ max I.left (min I.right x)
  have hmem (x : ℝ) : c x ∈ Set.Icc I.left I.right :=
    ⟨le_max_left _ _, max_le I.ordered.le (min_le_left _ _)⟩
  have hclamp (x : ℝ) : I.before (c x) = I.before x := by
    by_cases hr : I.right ≤ x
    · simp [c, max_eq_right I.ordered.le, CakeInterval.before, hr]
    · by_cases hl : x ≤ I.left
      · have hc : c x = I.left := max_eq_left ((min_le_right _ _).trans hl)
        rw [hc, CakeInterval.before_left]
        simp [CakeInterval.before, hr, not_lt.mpr hl]
      · simp only [c, min_eq_right (le_of_not_ge hr), max_eq_right (le_of_not_ge hl)]
  have heq : (fun x ↦ v.value (I.before x).support) =
      (fun x ↦ v.value (Set.Icc I.left (c x))) := by
    funext x
    rw [← hclamp x, v.value_before I (hmem x)]
  rw [heq]
  exact (v.continuousOn_value_Icc I.left_nonneg I.right_le_one).comp_continuous
    (continuous_const.max (continuous_const.min continuous_id)) hmem

end Valuation

namespace RWQuery

/-- Every legal Cut query has a unique valid answer, including in flat regions,
as required by the introduction's smallest-answer convention. -/
theorem existsUnique_cut_answer {n : ℕ} (v : Fin n → Valuation) (i : Fin n)
    {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 ≤ t)
    (ht1 : t ≤ (v i).value (Set.Icc a 1)) :
    ∃! x, (RWQuery.cut i a t).AnswerValid v x := by
  obtain ⟨x, hx, hxt, hmin⟩ := (v i).exists_smallest_cut ha ha1 le_rfl ht ht1
  refine ⟨x, ⟨ha, ha1, ht, ht1, hx.1, hx.2, hxt, ?_⟩, ?_⟩
  · intro y hay hy1 hyt
    exact hmin y ⟨hay, hy1⟩ hyt
  · intro y hy
    exact le_antisymm (hy.2.2.2.2.2.2.2 x hx.1 hx.2 hxt)
      (hmin y ⟨hy.2.2.2.2.1, hy.2.2.2.2.2.1⟩ hy.2.2.2.2.2.2.1)

/-- A zero-target Cut returns its left endpoint even across zero-valued cake,
by the introduction's smallest-answer rule. -/
theorem cut_zero_answer {n : ℕ} (v : Fin n → Valuation) (i : Fin n) {a x : ℝ}
    (h : (RWQuery.cut i a 0).AnswerValid v x) : x = a := by
  obtain ⟨_, ha1, _, _, hax, _, _, hmin⟩ := h
  exact le_antisymm (hmin a le_rfl ha1 (by simp)) hax

/-- A Cut begun in a stored component stays in that component when its value
covers the target. Its geometric prefix has exactly the requested value,
linking Robertson–Webb queries to Section 1.3's prefix operations. -/
theorem cut_answer_before {n : ℕ} (v : Fin n → Valuation) (i : Fin n)
    (I : CakeInterval) {t x : ℝ}
    (h : (RWQuery.cut i I.left t).AnswerValid v x)
    (ht : t ≤ (v i).value I.support) :
    x ∈ Set.Icc I.left I.right ∧ (v i).value (I.before x).support = t := by
  obtain ⟨_, _, ht0, _, hax, _, hxt, hmin⟩ := h
  rw [(v i).value_interval I] at ht
  obtain ⟨y, hy, hyt, _⟩ := (v i).exists_smallest_cut I.left_nonneg I.ordered.le
    I.right_le_one ht0 ht
  have hx : x ∈ Set.Icc I.left I.right :=
    ⟨hax, (hmin y hy.1 (hy.2.trans I.right_le_one) hyt).trans hy.2⟩
  exact ⟨hx, ((v i).value_before I hx).trans hxt⟩

end RWQuery
end CakeCuttingPsomas
