module

public import CakeCuttingPsomas.Cut

-- This project does not prescribe mathlib's copyright/license header format.
set_option linter.style.header false

/-! # Ordered prefixes and suffixes

Section 1.3 of `paper/main.tex` orders a piece's intervals independently of
spatial position. A prefix position is distance through that list (geometric
length, not value). Positions outside the piece are clamped to empty or whole.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas

/-- Geometric length of a component, unrelated to its possibly zero value. -/
def CakeInterval.length (I : CakeInterval) : ℝ := I.right - I.left

@[simp]
theorem CakeInterval.length_pos (I : CakeInterval) : 0 < I.length := sub_pos.mpr I.ordered

/-- Total geometric length, traversing the piece's specified interval order. -/
def Piece.length (P : Piece) : ℝ := (P.intervals.map CakeInterval.length).sum

theorem Piece.length_nonneg (P : Piece) : 0 ≤ P.length := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨I, _, rfl⟩ := List.mem_map.mp hx
  exact I.length_pos.le

/-- Geometric length of an interval prefix, clamped to the component. -/
theorem CakeInterval.length_before (I : CakeInterval) (x : ℝ) :
    (I.before x).length = min I.length (max 0 (x - I.left)) := by
  have hlen : I.length = I.right - I.left := rfl
  have hpos := I.length_pos
  unfold CakeInterval.before
  split_ifs <;>
    simp only [Piece.length, Piece.ofInterval, Piece.empty, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, CakeInterval.length] <;>
    simp only [min_def, max_def] <;> split_ifs <;> grind

namespace Piece

/-- Fragments of a prefix in list order. At most one component is cut. -/
def prefixIntervals : List CakeInterval → ℝ → List CakeInterval
  | [], _ => []
  | I :: Is, s => (I.before (I.left + s)).intervals ++ prefixIntervals Is (s - I.length)

private theorem prefixIntervals_subset (Is : List CakeInterval) (s : ℝ) :
    ∀ K ∈ prefixIntervals Is s, K.support ⊆ {x | ∃ I ∈ Is, x ∈ I.support} := by
  induction Is generalizing s with
  | nil => simp [prefixIntervals]
  | cons I Is ih =>
    intro K hK x hx
    simp only [prefixIntervals, List.mem_append] at hK
    rcases hK with hK | hK
    · exact ⟨I, List.mem_cons_self, I.before_subset _ ⟨K, hK, hx⟩⟩
    · obtain ⟨J, hJ, hxJ⟩ := ih _ K hK hx
      exact ⟨J, List.mem_cons_of_mem _ hJ, hxJ⟩

private theorem disjoint_before_prefixIntervals (I : CakeInterval) (Is : List CakeInterval)
    (h : ∀ J ∈ Is, Disjoint I.support J.support) (s t : ℝ) :
    Disjoint (I.before s).support {x | ∃ J ∈ prefixIntervals Is t, x ∈ J.support} := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨J, hJ, hxJ⟩
  obtain ⟨K, hK, hxK⟩ := prefixIntervals_subset Is t J hJ hxJ
  exact Set.disjoint_left.mp (h K hK) (I.before_subset s hx) hxK

theorem pairwise_prefixIntervals (Is : List CakeInterval)
    (h : Is.Pairwise (fun I J ↦ Disjoint I.support J.support)) (s : ℝ) :
    (prefixIntervals Is s).Pairwise (fun I J ↦ Disjoint I.support J.support) := by
  induction Is generalizing s with
  | nil => simp [prefixIntervals]
  | cons I Is ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
    rw [prefixIntervals, List.pairwise_append]
    refine ⟨(I.before _).disjoint, ih htail _, ?_⟩
    intro J hJ K hK
    apply (disjoint_before_prefixIntervals I Is hhead _ _).mono
    · intro x hx
      exact ⟨J, hJ, hx⟩
    · intro x hx
      exact ⟨K, hK, hx⟩

/-- Prefix at distance `s` through the ordered interval list. Full components
precede the possibly cut component; negative positions give the empty prefix. -/
def prefixAt (P : Piece) (s : ℝ) : Piece where
  intervals := prefixIntervals P.intervals s
  disjoint := pairwise_prefixIntervals _ P.disjoint s

theorem prefix_subset (P : Piece) (s : ℝ) : (P.prefixAt s).support ⊆ P.support := by
  rintro x ⟨K, hK, hx⟩
  exact prefixIntervals_subset _ s K hK hx

private theorem prefixIntervals_nonpos (Is : List CakeInterval) {s : ℝ} (hs : s ≤ 0) :
    prefixIntervals Is s = [] := by
  induction Is generalizing s with
  | nil => rfl
  | cons I Is ih =>
    have hbefore : I.before (I.left + s) = Piece.empty := by
      simp [CakeInterval.before, show ¬I.right ≤ I.left + s by have := I.ordered; grind,
        show ¬I.left < I.left + s by grind]
    simp only [prefixIntervals, hbefore, Piece.empty, List.nil_append]
    exact ih (by have := I.length_pos; grind)

/-- Nonpositive traversal positions give the empty prefix. -/
theorem prefix_nonpos (P : Piece) {s : ℝ} (hs : s ≤ 0) : P.prefixAt s = Piece.empty := by
  cases P
  simp only [prefixAt, prefixIntervals_nonpos _ hs, Piece.empty]

@[simp]
theorem prefix_zero (P : Piece) : P.prefixAt 0 = Piece.empty := by
  cases P
  simp only [prefixAt, prefixIntervals_nonpos _ le_rfl, Piece.empty]

/-- Before the first component is exhausted, the tail contributes no fragments. -/
theorem prefixIntervals_cons_of_le (I : CakeInterval) (Is : List CakeInterval)
    {s : ℝ} (hs : s ≤ I.length) :
    prefixIntervals (I :: Is) s = (I.before (I.left + s)).intervals := by
  rw [prefixIntervals, prefixIntervals_nonpos Is (sub_nonpos.mpr hs), List.append_nil]

/-- After a whole component, traversal continues through the remaining list. -/
theorem prefixIntervals_cons_of_ge (I : CakeInterval) (Is : List CakeInterval)
    {s : ℝ} (hs : I.length ≤ s) :
    prefixIntervals (I :: Is) s = I :: prefixIntervals Is (s - I.length) := by
  have hr : I.right ≤ I.left + s := by have : I.length = I.right - I.left := rfl; grind
  simp only [prefixIntervals, CakeInterval.before, dite_eq_left hr, ofInterval,
    List.singleton_append]

/-- A suffix is the exact remainder after removing its ordered prefix. -/
def suffixAt (P : Piece) (s : ℝ) : Piece := P.diff (P.prefixAt s)

@[simp]
theorem support_suffix (P : Piece) (s : ℝ) :
    (P.suffixAt s).support = P.support \ (P.prefixAt s).support := P.support_diff _

theorem suffix_subset (P : Piece) (s : ℝ) : (P.suffixAt s).support ⊆ P.support := by
  rw [support_suffix]
  exact Set.sdiff_subset

/-- Prefix and suffix are exactly disjoint, including endpoints (Section 1.3). -/
theorem prefix_disjoint_suffix (P : Piece) (s : ℝ) :
    Disjoint (P.prefixAt s).support (P.suffixAt s).support := by
  rw [support_suffix]
  exact Set.disjoint_left.mpr fun _ hx hy ↦ hy.2 hx

/-- Removing a prefix leaves an exact partition of the input (Section 1.3). -/
theorem prefix_union_suffix (P : Piece) (s : ℝ) :
    (P.prefixAt s).support ∪ (P.suffixAt s).support = P.support := by
  rw [support_suffix, Set.union_sdiff_cancel (P.prefix_subset s)]

@[simp]
theorem suffix_zero (P : Piece) : P.suffixAt 0 = P := by
  simp [suffixAt]

private theorem prefixIntervals_whole (Is : List CakeInterval) {s : ℝ}
    (hs : (Is.map CakeInterval.length).sum ≤ s) : prefixIntervals Is s = Is := by
  induction Is generalizing s with
  | nil => rfl
  | cons I Is ih =>
    have hnonneg : 0 ≤ (Is.map CakeInterval.length).sum :=
      List.sum_nonneg fun x hx ↦ by
        obtain ⟨J, _, rfl⟩ := List.mem_map.mp hx
        exact J.length_pos.le
    have hsum : I.length + (Is.map CakeInterval.length).sum ≤ s := by simpa using hs
    have hright : I.right ≤ I.left + s := by have hlen : I.length = I.right - I.left := rfl; grind
    simp only [prefixIntervals, CakeInterval.before, dite_eq_left hright, ofInterval,
      List.singleton_append]
    rw [ih (by grind)]

@[simp]
theorem prefix_length (P : Piece) : P.prefixAt P.length = P := by
  cases P
  simp only [prefixAt, length, prefixIntervals_whole _ le_rfl]

/-- Prefixes are nested in traversal order even when the interval list is not
spatially sorted. This order determines the smallest prefix in Section 1.3. -/
theorem prefix_mono (P : Piece) : Monotone (fun s ↦ (P.prefixAt s).support) := by
  suffices ∀ (Is : List CakeInterval) (s t : ℝ), s ≤ t →
      {x | ∃ I ∈ prefixIntervals Is s, x ∈ I.support} ⊆
      {x | ∃ I ∈ prefixIntervals Is t, x ∈ I.support} by
    exact fun s t hst ↦ this P.intervals s t hst
  intro Is
  induction Is with
  | nil => simp [prefixIntervals]
  | cons I Is ih =>
    intro s t hst x hx
    obtain ⟨J, hJ, hxJ⟩ := hx
    simp only [prefixIntervals, List.mem_append] at hJ ⊢
    rcases hJ with hJ | hJ
    · have hbefore : (I.before (I.left + s)).support ⊆ (I.before (I.left + t)).support := by
        rw [CakeInterval.support_before, CakeInterval.support_before]
        split_ifs <;> intro y hy <;> simp_all only [Set.mem_inter_iff, Set.mem_Iio] <;> grind
      obtain ⟨K, hK, hxK⟩ := hbefore ⟨J, hJ, hxJ⟩
      exact ⟨K, Or.inl hK, hxK⟩
    · obtain ⟨K, hK, hxK⟩ := ih (s - I.length) (t - I.length) (by grind) ⟨J, hJ, hxJ⟩
      exact ⟨K, Or.inr hK, hxK⟩

/-- Later suffixes are contained in earlier ones, regardless of spatial order. -/
theorem suffix_antitone (P : Piece) : Antitone (fun s ↦ (P.suffixAt s).support) := by
  intro s t hst
  simp only [support_suffix]
  exact Set.sdiff_subset_sdiff_right (P.prefix_mono hst)

@[simp]
theorem support_suffix_length (P : Piece) : (P.suffixAt P.length).support = ∅ := by
  simp

@[simp]
theorem suffix_length (P : Piece) : P.suffixAt P.length = Piece.empty :=
  (P.suffixAt P.length).eq_empty_of_support_eq_empty P.support_suffix_length

theorem support_prefixAt_cons (I : CakeInterval) (Is : List CakeInterval)
    (h : (I :: Is).Pairwise (fun I J ↦ Disjoint I.support J.support)) (s : ℝ) :
    ((⟨I :: Is, h⟩ : Piece).prefixAt s).support =
      (I.before (I.left + s)).support ∪
        ((⟨Is, (List.pairwise_cons.mp h).2⟩ : Piece).prefixAt (s - I.length)).support := by
  ext x
  simp only [prefixAt, prefixIntervals, support, List.mem_append, Set.mem_union,
    Set.mem_ofPred_eq]
  grind

private theorem length_prefixIntervals (Is : List CakeInterval) (s : ℝ) :
    ((prefixIntervals Is s).map CakeInterval.length).sum =
      min (Is.map CakeInterval.length).sum (max 0 s) := by
  induction Is generalizing s with
  | nil => simp [prefixIntervals]
  | cons I Is ih =>
    have hI := I.length_pos
    have htail : 0 ≤ (Is.map CakeInterval.length).sum :=
      List.sum_nonneg fun x hx ↦ by
        obtain ⟨J, _, rfl⟩ := List.mem_map.mp hx
        exact J.length_pos.le
    simp only [prefixIntervals, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons]
    change (I.before (I.left + s)).length +
      min (Is.map CakeInterval.length).sum (max 0 (s - I.length)) = _
    rw [CakeInterval.length_before]
    simp only [add_sub_cancel_left, min_def, max_def]
    split_ifs <;> grind

/-- Traversal position agrees with actual geometric prefix length. This also
justifies using lengths to parameterize prefixes and suffixes in the paper. -/
theorem length_prefixAt (P : Piece) (s : ℝ) :
    (P.prefixAt s).length = min P.length (max 0 s) :=
  length_prefixIntervals P.intervals s

/-- `Q` is an ordered prefix of `P`, with its inherited interval representation. -/
def IsPrefix (Q P : Piece) : Prop := ∃ s ∈ Set.Icc 0 P.length, Q = P.prefixAt s

/-- `Q` is the remainder after an ordered prefix of `P`. -/
def IsSuffix (Q P : Piece) : Prop := ∃ s ∈ Set.Icc 0 P.length, Q = P.suffixAt s

theorem prefix_isPrefix (P : Piece) {s : ℝ} (hs : s ∈ Set.Icc 0 P.length) :
    (P.prefixAt s).IsPrefix P := ⟨s, hs, rfl⟩

theorem suffix_isSuffix (P : Piece) {s : ℝ} (hs : s ∈ Set.Icc 0 P.length) :
    (P.suffixAt s).IsSuffix P := ⟨s, hs, rfl⟩

theorem empty_isPrefix (P : Piece) : Piece.empty.IsPrefix P :=
  ⟨0, ⟨le_rfl, P.length_nonneg⟩, P.prefix_zero.symm⟩

theorem whole_isPrefix (P : Piece) : P.IsPrefix P :=
  ⟨P.length, ⟨P.length_nonneg, le_rfl⟩, P.prefix_length.symm⟩

theorem empty_isSuffix (P : Piece) : Piece.empty.IsSuffix P :=
  ⟨P.length, ⟨P.length_nonneg, le_rfl⟩, P.suffix_length.symm⟩

theorem whole_isSuffix (P : Piece) : P.IsSuffix P :=
  ⟨0, ⟨le_rfl, P.length_nonneg⟩, P.suffix_zero.symm⟩

/-- Any two suffixes of one ordered piece are nested, as used in Section 4's
proof of `Permute`. Their physical coordinates need not be sorted. -/
theorem IsSuffix.support_comparable {Q R P : Piece} (hQ : Q.IsSuffix P)
    (hR : R.IsSuffix P) : Q.support ⊆ R.support ∨ R.support ⊆ Q.support := by
  obtain ⟨s, _, rfl⟩ := hQ
  obtain ⟨t, _, rfl⟩ := hR
  rcases le_total s t with h | h
  · exact Or.inr (P.suffix_antitone h)
  · exact Or.inl (P.suffix_antitone h)

end Piece
namespace Valuation

private def prefixValue (v : Valuation) : List CakeInterval → ℝ → ℝ
  | [], _ => 0
  | I :: Is, s => v.value (I.before (I.left + s)).support + prefixValue v Is (s - I.length)

private theorem value_prefix_eq (v : Valuation) (Is : List CakeInterval)
    (h : Is.Pairwise (fun I J ↦ Disjoint I.support J.support)) (s : ℝ) :
    v.value ((⟨Is, h⟩ : Piece).prefixAt s).support = prefixValue v Is s := by
  induction Is generalizing s with
  | nil => simp [Piece.prefixAt, Piece.prefixIntervals, Piece.support, prefixValue]
  | cons I Is ih =>
    let T : Piece := ⟨Is, (List.pairwise_cons.mp h).2⟩
    have hd : Disjoint (I.before (I.left + s)).support
        (T.prefixAt (s - I.length)).support :=
      Piece.disjoint_before_prefixIntervals I Is (List.pairwise_cons.mp h).1 _ _
    rw [Piece.support_prefixAt_cons]
    rw [v.value_union (I.before _).measurableSet_support (T.prefixAt _).measurableSet_support
      (I.before _).support_subset_unit (T.prefixAt _).support_subset_unit hd]
    exact congrArg (v.value (I.before (I.left + s)).support + ·) (ih _ _)

/-- Prefix value varies continuously with traversal length, as asserted in
Section 1.3 and used for suffix-length compactness in Section 4 of the paper. -/
theorem continuous_value_prefix (v : Valuation) (P : Piece) :
    Continuous (fun s ↦ v.value (P.prefixAt s).support) := by
  have heq : (fun s ↦ v.value (P.prefixAt s).support) = prefixValue v P.intervals := by
    funext s
    exact value_prefix_eq v P.intervals P.disjoint s
  rw [heq]
  suffices ∀ Is, Continuous (prefixValue v Is) by exact this _
  intro Is
  induction Is with
  | nil => exact continuous_const
  | cons I Is ih =>
    exact ((v.continuous_value_before I).comp (continuous_const.add continuous_id)).add
      (ih.comp (continuous_id.sub continuous_const))

/-- Ordered prefix values are nondecreasing, without assuming positive density. -/
theorem monotone_value_prefix (v : Valuation) (P : Piece) :
    Monotone (fun s ↦ v.value (P.prefixAt s).support) := by
  intro s t hst
  exact v.value_mono (P.prefixAt s).measurableSet_support (P.prefixAt t).measurableSet_support
    (P.prefix_mono hst) (P.prefixAt t).support_subset_unit

/-- A smallest prefix with any target between zero and the piece's value exists,
as stated in Section 1.3. Minimization retains every unnecessary zero-valued
suffix, including when the target equals the piece's total value. -/
theorem exists_smallest_prefix (v : Valuation) (P : Piece) {t : ℝ}
    (ht : 0 ≤ t) (htP : t ≤ v.value P.support) :
    ∃ s ∈ Set.Icc 0 P.length, v.value (P.prefixAt s).support = t ∧
      ∀ r ∈ Set.Icc 0 P.length, v.value (P.prefixAt r).support = t → s ≤ r := by
  have hc : ContinuousOn (fun s ↦ v.value (P.prefixAt s).support) (Set.Icc 0 P.length) :=
    (v.continuous_value_prefix P).continuousOn
  have hstart : v.value (P.prefixAt 0).support = 0 := by simp
  have hend : v.value (P.prefixAt P.length).support = v.value P.support := by simp
  obtain ⟨s, hs, hst⟩ := intermediate_value_Icc P.length_nonneg hc
    (by simpa only [Set.mem_Icc, hstart, hend] using And.intro ht htP)
  let S : Set (Set.Icc 0 P.length) := {r | v.value (P.prefixAt r.val).support = t}
  have hS : IsCompact S := (isClosed_eq hc.domRestrict continuous_const).isCompact
  obtain ⟨r, hr, hmin⟩ := hS.exists_isMinOn ⟨⟨s, hs⟩, hst⟩ continuous_subtype_val.continuousOn
  exact ⟨r.val, r.property, hr,
    fun q hq hqt ↦ hmin (show (⟨q, hq⟩ : Set.Icc 0 P.length) ∈ S from hqt)⟩

/-- A smallest exact-value prefix also precedes every prefix meeting or
exceeding its target. This supplies the trimming minimality of Section 1.3. -/
theorem smallest_prefix_le_of_value_ge (v : Valuation) (P : Piece) {s t r : ℝ}
    (hs : v.value (P.prefixAt s).support = t)
    (hmin : ∀ q ∈ Set.Icc 0 P.length, v.value (P.prefixAt q).support = t → s ≤ q)
    (hr : r ∈ Set.Icc 0 P.length) (hrt : t ≤ v.value (P.prefixAt r).support) : s ≤ r := by
  by_cases hsr : s ≤ r
  · exact hsr
  · exact hmin r hr (le_antisymm ((v.monotone_value_prefix P (le_of_not_ge hsr)).trans_eq hs) hrt)

/-- A target-zero smallest prefix is empty even if the entire cake has value
zero. This prevents unnecessary trimming in Section 4's `Permute`. -/
theorem smallest_prefix_zero (v : Valuation) (P : Piece) {s : ℝ}
    (hs : s ∈ Set.Icc 0 P.length)
    (hmin : ∀ r ∈ Set.Icc 0 P.length, v.value (P.prefixAt r).support = 0 → s ≤ r) :
    s = 0 := by
  exact le_antisymm (hmin 0 ⟨le_rfl, P.length_nonneg⟩ (by simp)) hs.1

/-- The smallest prefix is contained in every ordered prefix with the target
value. This is the minimality used when `Permute` trims in Section 4. -/
theorem exists_least_prefix (v : Valuation) (P : Piece) {t : ℝ}
    (ht : 0 ≤ t) (htP : t ≤ v.value P.support) :
    ∃ Q : Piece, Q.IsPrefix P ∧ v.value Q.support = t ∧
      ∀ Q' : Piece, Q'.IsPrefix P → v.value Q'.support = t → Q.support ⊆ Q'.support := by
  obtain ⟨s, hs, hst, hmin⟩ := v.exists_smallest_prefix P ht htP
  refine ⟨P.prefixAt s, P.prefix_isPrefix hs, hst, ?_⟩
  rintro Q ⟨r, hr, rfl⟩ hrt
  exact P.prefix_mono (hmin r hr hrt)

/-- Exact value decomposition for an ordered split (Section 1.3). -/
theorem value_prefix_add_suffix (v : Valuation) (P : Piece) (s : ℝ) :
    v.value (P.prefixAt s).support + v.value (P.suffixAt s).support = v.value P.support := by
  rw [← v.value_union (P.prefixAt s).measurableSet_support (P.suffixAt s).measurableSet_support
    (P.prefixAt s).support_subset_unit (P.suffixAt s).support_subset_unit
    (P.prefix_disjoint_suffix s), P.prefix_union_suffix]

/-- Suffix value is continuous in traversal position, including flat regions;
this is the continuity used in Section 4's suffix compactness argument. -/
theorem continuous_value_suffix (v : Valuation) (P : Piece) :
    Continuous (fun s ↦ v.value (P.suffixAt s).support) := by
  have heq : (fun s ↦ v.value (P.suffixAt s).support) =
      (fun s ↦ v.value P.support - v.value (P.prefixAt s).support) := by
    funext s
    have := v.value_prefix_add_suffix P s
    grind
  rw [heq]
  exact continuous_const.sub (v.continuous_value_prefix P)

end Valuation

end CakeCuttingPsomas
