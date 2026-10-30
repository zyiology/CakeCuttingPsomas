module

public import CakeCuttingPsomas.Traversal

set_option linter.style.header false

/-! # Suffix geometry for Permute

Section 1.3 and Section 5, `permute:trim` and `eq:permute-caps`.
All equalities of pieces retain their specified interval-list traversal.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas

theorem Piece.eq_of_intervals_eq {P Q : Piece} (h : P.intervals = Q.intervals) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

private theorem interval_separated {I J : CakeInterval} (h : Disjoint I.support J.support) :
    I.right ≤ J.left ∨ J.right ≤ I.left := by
  by_contra! hn
  have hxI : max I.left J.left ∈ I.support := by
    have hi := I.ordered
    simp only [CakeInterval.support]
    split_ifs <;> simp only [Set.mem_Icc, Set.mem_Ico] <;> constructor <;> grind
  have hxJ : max I.left J.left ∈ J.support := by
    have hj := J.ordered
    simp only [CakeInterval.support]
    split_ifs <;> simp only [Set.mem_Icc, Set.mem_Ico] <;> constructor <;> grind
  exact Set.disjoint_left.mp h hxI hxJ

theorem CakeInterval.diff_of_disjoint (I J : CakeInterval)
    (h : Disjoint I.support J.support) : I.diff J = Piece.ofInterval I := by
  rcases interval_separated h with h | h
  · have hr : I.right ≤ J.right := h.trans J.ordered.le
    apply Piece.eq_of_intervals_eq
    simp [diff, before, h, after, hr, Piece.append, Piece.empty]
  · have hl : ¬I.left < J.left := by have := J.ordered; linarith
    have hr : ¬I.right ≤ J.left := by have := I.ordered; have := J.ordered; linarith
    have hJ : J.right ≠ 1 := by have := I.ordered; have := I.right_le_one; linarith
    simp [diff, before, hr, hl, hJ, after, h, Piece.append, Piece.empty,
      show ¬I.right ≤ J.right by have := I.ordered; linarith]

namespace Piece

theorem diff_of_disjoint (P Q : Piece) (h : Disjoint P.support Q.support) : P.diff Q = P := by
  suffices ∀ Js, Disjoint P.support {x | ∃ J ∈ Js, x ∈ J.support} →
      P.diffIntervals Js = P by
    exact this Q.intervals h
  intro Js
  induction Js with
  | nil => intro _; rfl
  | cons J Js ih =>
    intro hd
    have hJ : P.eraseInterval J = P := by
      apply eq_of_intervals_eq
      change P.intervals.flatMap _ = P.intervals
      have he : ∀ I ∈ P.intervals, (I.diff J).intervals = [I] := by
        intro I hI
        apply congrArg Piece.intervals (I.diff_of_disjoint J ?_)
        exact Set.disjoint_left.mpr fun x hx hy ↦ Set.disjoint_left.mp hd
          ⟨I, hI, hx⟩ ⟨J, List.mem_cons_self, hy⟩
      rw [List.flatMap_congr he]
      simp
    rw [diffIntervals, hJ]
    exact ih (Set.disjoint_left.mpr fun x hx ⟨K, hK, hy⟩ ↦
      Set.disjoint_left.mp hd hx ⟨K, List.mem_cons_of_mem _ hK, hy⟩)

theorem diff_append (P Q R : Piece) (hd : Disjoint P.support Q.support) :
    (P.append Q hd).diff R =
      (P.diff R).append (Q.diff R) (hd.mono (by simp) (by simp)) := by
  apply eq_of_intervals_eq
  suffices ∀ Js, ((P.append Q hd).diffIntervals Js).intervals =
      (P.diffIntervals Js).intervals ++ (Q.diffIntervals Js).intervals by
    exact this R.intervals
  intro Js
  induction Js generalizing P Q with
  | nil => rfl
  | cons J Js ih =>
    have he : (P.append Q hd).eraseInterval J =
        (P.eraseInterval J).append (Q.eraseInterval J)
          (hd.mono (by rw [support_eraseInterval]; exact Set.sdiff_subset)
            (by rw [support_eraseInterval]; exact Set.sdiff_subset)) := by
      apply eq_of_intervals_eq
      exact List.flatMap_append
    simpa only [diffIntervals, he] using ih (P.eraseInterval J) (Q.eraseInterval J) _

theorem diff_append_right (P Q R : Piece) (hd : Disjoint Q.support R.support) :
    P.diff (Q.append R hd) = (P.diff Q).diff R := by
  suffices ∀ (Js Ks : List CakeInterval) (P : Piece),
      P.diffIntervals (Js ++ Ks) = (P.diffIntervals Js).diffIntervals Ks by
    exact this Q.intervals R.intervals P
  intro Js
  induction Js with
  | nil => intros; rfl
  | cons J Js ih => intros; exact ih _ _

theorem diff_eq_empty_of_subset (P Q : Piece) (h : P.support ⊆ Q.support) :
    P.diff Q = empty := by
  apply eq_empty_of_support_eq_empty
  rw [support_diff]
  exact Set.sdiff_eq_empty.mpr h

@[simp] theorem empty_diff (Q : Piece) : empty.diff Q = empty :=
  diff_eq_empty_of_subset _ _ (by simp)

theorem suffix_nonpos (P : Piece) {s : ℝ} (hs : s ≤ 0) : P.suffixAt s = P := by
  simp [suffixAt, P.prefix_nonpos hs]

private theorem interval_diff_before (I : CakeInterval) (x : ℝ) :
    (ofInterval I).diff (I.before x) = I.after x := by
  unfold CakeInterval.before
  split_ifs with hr hl
  · rw [diff_eq_empty_of_subset _ _ Set.Subset.rfl]
    simp [CakeInterval.after, hr]
  · have hx : x ≠ 1 := by have := I.right_le_one; linarith
    have he : I.before I.left = empty := I.before_left
    simp [diff, diffIntervals, eraseInterval, ofInterval, CakeInterval.diff,
      he, hx, CakeInterval.after, hr, show ¬x ≤ I.left by linarith, append, empty]
  · simp [CakeInterval.after, hr, le_of_not_gt hl]

theorem suffixAt_cons_of_le (I : CakeInterval) (Is : List CakeInterval)
    (hd : (I :: Is).Pairwise (fun I J ↦ Disjoint I.support J.support))
    {s : ℝ} (hs : s ≤ I.length) :
    ((⟨I :: Is, hd⟩ : Piece).suffixAt s).intervals =
      (I.after (I.left + s)).intervals ++ Is := by
  let T : Piece := ⟨Is, (List.pairwise_cons.mp hd).2⟩
  have hIT : Disjoint (ofInterval I).support T.support := by
    exact Set.disjoint_left.mpr fun x hx ⟨J, hJ, hy⟩ ↦
      Set.disjoint_left.mp ((List.pairwise_cons.mp hd).1 J hJ) (by simpa using hx) hy
  have hp : (⟨I :: Is, hd⟩ : Piece).prefixAt s = I.before (I.left + s) :=
    eq_of_intervals_eq (prefixIntervals_cons_of_le I Is hs)
  have hP : (⟨I :: Is, hd⟩ : Piece) = (ofInterval I).append T hIT := rfl
  rw [suffixAt, hp, hP, diff_append]
  change ((ofInterval I).diff (I.before (I.left + s))).intervals ++
    (T.diff (I.before (I.left + s))).intervals = _
  rw [interval_diff_before, diff_of_disjoint T _ (hIT.symm.mono_right (by
    simpa using I.before_subset (I.left + s)))]

theorem suffixAt_cons_of_ge (I : CakeInterval) (Is : List CakeInterval)
    (hd : (I :: Is).Pairwise (fun I J ↦ Disjoint I.support J.support))
    {s : ℝ} (hs : I.length ≤ s) :
    (⟨I :: Is, hd⟩ : Piece).suffixAt s =
      (⟨Is, (List.pairwise_cons.mp hd).2⟩ : Piece).suffixAt (s - I.length) := by
  let T : Piece := ⟨Is, (List.pairwise_cons.mp hd).2⟩
  have hIT : Disjoint (ofInterval I).support T.support := by
    exact Set.disjoint_left.mpr fun x hx ⟨J, hJ, hy⟩ ↦
      Set.disjoint_left.mp ((List.pairwise_cons.mp hd).1 J hJ) (by simpa using hx) hy
  have hP : (⟨I :: Is, hd⟩ : Piece) = (ofInterval I).append T hIT := rfl
  have hp : (⟨I :: Is, hd⟩ : Piece).prefixAt s =
      (ofInterval I).append (T.prefixAt (s - I.length)) (hIT.mono_right (T.prefix_subset _)) :=
    eq_of_intervals_eq (prefixIntervals_cons_of_ge I Is hs)
  rw [suffixAt, hp, diff_append_right, hP, diff_append]
  have he : ((ofInterval I).diff (ofInterval I)).append (T.diff (ofInterval I))
      (hIT.mono (by simp) (by simp)) = T := by
    apply eq_of_intervals_eq
    change ((ofInterval I).diff (ofInterval I)).intervals ++
      (T.diff (ofInterval I)).intervals = T.intervals
    rw [diff_eq_empty_of_subset _ _ Set.Subset.rfl, diff_of_disjoint T _ hIT.symm]
    rfl
  rw [he]
  rfl

/-- Section 1.3: the suffix length is the distance remaining in the traversal. -/
theorem length_suffixAt (P : Piece) {s : ℝ} (hs : s ∈ Set.Icc 0 P.length) :
    (P.suffixAt s).length = P.length - s := by
  obtain ⟨Is, hd⟩ := P
  induction Is generalizing s with
  | nil => simp_all [length, suffixAt, prefixAt, prefixIntervals, diff, diffIntervals]
  | cons I Is ih =>
    let T : Piece := ⟨Is, (List.pairwise_cons.mp hd).2⟩
    have hlen : (⟨I :: Is, hd⟩ : Piece).length = I.length + T.length := by simp [length, T]
    by_cases h : I.length ≤ s
    · have hsT : s - I.length ∈ Set.Icc 0 T.length := by
        rw [hlen] at hs
        exact ⟨by linarith, by linarith [hs.2]⟩
      rw [suffixAt_cons_of_ge I Is hd h, ih T.disjoint hsT, hlen]
      ring
    · rw [length, suffixAt_cons_of_le I Is hd (le_of_not_ge h),
        List.map_append, List.sum_append]
      have hr : ¬I.right ≤ I.left + s := by
        have hc := lt_of_not_ge h
        simp only [CakeInterval.length] at hc
        linarith
      by_cases hz : s = 0
      · subst s
        simp [CakeInterval.after_left, ofInterval, length]
      · have hl : ¬I.left + s ≤ I.left := by
          have hs0 : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hz)
          linarith
        simp [CakeInterval.after, hr, hl, ofInterval, CakeInterval.length, length]
        ring

private theorem after_shift (I : CakeInterval) {a : ℝ} (ha : 0 < a) (haI : a < I.length)
    (b : ℝ) (hb : 0 ≤ b) :
    let R : CakeInterval := ⟨I.left + a, I.right, by have := I.left_nonneg; linarith,
      by dsimp [CakeInterval.length] at haI; linarith, I.right_le_one⟩
    R.after (R.left + b) = I.after (I.left + (a + b)) := by
  dsimp
  have he : I.left + a + b = I.left + (a + b) := by ring
  simp only [CakeInterval.after, he]
  split_ifs <;> try rfl
  all_goals try (exfalso; linarith)
  all_goals
    apply eq_of_intervals_eq
    simp only [ofInterval, List.singleton_inj]
    congr 1; linarith

/-- Section 5, `permute:trim`: nested trims are exact suffixes of the original
piece, with traversal positions adding even across zero-valued components. -/
theorem suffixAt_suffixAt (P : Piece) {a b : ℝ} (ha : a ∈ Set.Icc 0 P.length)
    (hb : b ∈ Set.Icc 0 (P.suffixAt a).length) :
    (P.suffixAt a).suffixAt b = P.suffixAt (a + b) := by
  have hab : a + b ≤ P.length := by rw [length_suffixAt P ha] at hb; linarith [hb.2]
  obtain ⟨Is, hd⟩ := P
  induction Is generalizing a b with
  | nil =>
    have haz : a = 0 := by simpa [length] using ha
    subst a
    simp
  | cons I Is ih =>
    let T : Piece := ⟨Is, (List.pairwise_cons.mp hd).2⟩
    have hlen : (⟨I :: Is, hd⟩ : Piece).length = I.length + T.length := by simp [length, T]
    by_cases hz : a = 0
    · subst a; simp
    by_cases h : I.length ≤ a
    · rw [suffixAt_cons_of_ge I Is hd h] at hb ⊢
      rw [suffixAt_cons_of_ge I Is hd (by linarith [hb.1])]
      have haT : a - I.length ∈ Set.Icc 0 T.length := by
        rw [hlen] at ha
        exact ⟨by linarith, by linarith [ha.2]⟩
      have he := ih T.disjoint haT hb
        (by change a - I.length + b ≤ T.length; rw [hlen] at hab; linarith)
      convert he using 1; congr 1; ring
    · have ha0 : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm hz)
      have har : I.left + a < I.right := by
        have hc := lt_of_not_ge h
        simp only [CakeInterval.length] at hc
        linarith
      let R : CakeInterval := ⟨I.left + a, I.right,
        by have := I.left_nonneg; linarith, har, I.right_le_one⟩
      have he : (⟨I :: Is, hd⟩ : Piece).suffixAt a =
          (ofInterval R).append T (by
            apply Set.disjoint_left.mpr
            intro x hx ⟨J, hJ, hy⟩
            apply Set.disjoint_left.mp ((List.pairwise_cons.mp hd).1 J hJ) _ hy
            have hr : ¬I.right ≤ I.left + a := not_le.mpr har
            have hl : ¬I.left + a ≤ I.left := by linarith
            apply I.after_subset (I.left + a)
            simpa [CakeInterval.after, hr, hl, R] using hx) := by
        apply eq_of_intervals_eq
        rw [suffixAt_cons_of_le I Is hd (le_of_not_ge h)]
        have hr : ¬I.right ≤ I.left + a := not_le.mpr har
        simp [CakeInterval.after, hr, show ¬I.left + a ≤ I.left by linarith,
          R, append, ofInterval, T]
      rw [he]
      change (⟨R :: Is, _⟩ : Piece).suffixAt b = _
      by_cases hbr : b ≤ R.length
      · apply eq_of_intervals_eq
        erw [suffixAt_cons_of_le R Is _ hbr,
          suffixAt_cons_of_le I Is hd (by
            change a + b ≤ I.right - I.left
            have hc : b ≤ I.right - (I.left + a) := hbr
            linarith)]
        rw [after_shift I ha0 (lt_of_not_ge h) b hb.1]
      · erw [suffixAt_cons_of_ge R Is _ (le_of_not_ge hbr),
          suffixAt_cons_of_ge I Is hd (by
            change I.right - I.left ≤ a + b
            have hc : ¬b ≤ I.right - (I.left + a) := hbr
            linarith)]
        congr 1
        dsimp [R, CakeInterval.length]
        ring

/-- A suffix's traversal position is determined by the length removed. -/
theorem IsSuffix.position_mem {P Q : Piece} (h : Q.IsSuffix P) :
    P.length - Q.length ∈ Set.Icc 0 P.length := by
  obtain ⟨a, ha, rfl⟩ := h
  rw [length_suffixAt P ha]
  simpa only [sub_sub_cancel] using ha

/-- The canonical traversal position reconstructs the exact suffix. -/
theorem IsSuffix.eq_suffixAt_length_sub_length {P Q : Piece} (h : Q.IsSuffix P) :
    Q = P.suffixAt (P.length - Q.length) := by
  obtain ⟨a, ha, rfl⟩ := h
  rw [length_suffixAt P ha, sub_sub_cancel]

theorem IsSuffix.trans {P Q R : Piece} (hRQ : R.IsSuffix Q) (hQP : Q.IsSuffix P) :
    R.IsSuffix P := by
  obtain ⟨a, ha, rfl⟩ := hQP
  obtain ⟨b, hb, rfl⟩ := hRQ
  refine ⟨a + b, ⟨by linarith [ha.1, hb.1], ?_⟩, suffixAt_suffixAt P ha hb⟩
  rw [length_suffixAt P ha] at hb
  linarith [hb.2]

/-- Section 5, `eq:permute-caps`: containment of suffixes is exactly reverse
order of their traversal positions, including zero-value bands. -/
theorem suffix_subset_suffix_iff (P : Piece) {a b : ℝ}
    (ha : a ∈ Set.Icc 0 P.length) (hb : b ∈ Set.Icc 0 P.length) :
    (P.suffixAt b).support ⊆ (P.suffixAt a).support ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, (fun h ↦ P.suffix_antitone h)⟩
  by_contra! hab
  obtain ⟨x, hx, hn⟩ := P.exists_mem_prefix_diff hb.1 hab ha.2
  have hxP := P.prefix_subset a hx
  have hxB : x ∈ (P.suffixAt b).support := by simpa using And.intro hxP hn
  have hxA := h hxB
  rw [support_suffix] at hxA
  exact hxA.2 hx

theorem IsSuffix.of_support_subset {P Q R : Piece} (hQ : Q.IsSuffix P)
    (hR : R.IsSuffix P) (h : R.support ⊆ Q.support) : R.IsSuffix Q := by
  obtain ⟨a, ha, rfl⟩ := hQ
  obtain ⟨b, hb, rfl⟩ := hR
  have hab := (P.suffix_subset_suffix_iff ha hb).mp h
  have hpos : b - a ∈ Set.Icc 0 (P.suffixAt a).length := by
    rw [length_suffixAt P ha]
    exact ⟨sub_nonneg.mpr hab, sub_le_sub_right hb.2 a⟩
  refine ⟨b - a, hpos, ?_⟩
  rw [suffixAt_suffixAt P ha hpos, add_sub_cancel]

private theorem support_prefix_suffixAt (P : Piece) {a b : ℝ}
    (ha : a ∈ Set.Icc 0 P.length) (hb : b ∈ Set.Icc 0 (P.suffixAt a).length) :
    ((P.suffixAt a).prefixAt b).support =
      (P.prefixAt (a + b)).support \ (P.prefixAt a).support := by
  have he := P.suffixAt_suffixAt ha hb
  have hu := (P.suffixAt a).prefix_union_suffix b
  have hd := (P.suffixAt a).prefix_disjoint_suffix b
  have hp := (P.suffixAt a).prefix_subset b
  simp only [he, support_suffix] at hu hd hp
  have hsub := P.prefix_subset (a + b)
  ext x
  have hu' := Set.ext_iff.mp hu x
  have hd' : ¬(x ∈ ((P.suffixAt a).prefixAt b).support ∧
      x ∈ P.support \ (P.prefixAt (a + b)).support) :=
    fun hx ↦ Set.disjoint_left.mp hd hx.1 hx.2
  simp only [Set.mem_union, Set.mem_sdiff] at hu' hd' hp ⊢
  grind

/-- Section 1.3's subdivision convention preserves every suffix support. -/
theorem SameTraversal.support_suffix_eq {P Q : Piece} (h : P.SameTraversal Q) (a : ℝ) :
    (P.suffixAt a).support = (Q.suffixAt a).support := by
  simp only [support_suffix, h.support_eq, h.2]

/-- Section 5, `permute:trim`: subdivision preserves the traversal of the
remaining suffix, so later trims can use current cells and original positions. -/
theorem SameTraversal.suffixAt {P Q : Piece} (h : P.SameTraversal Q) {a : ℝ}
    (ha : a ∈ Set.Icc 0 P.length) : (P.suffixAt a).SameTraversal (Q.suffixAt a) := by
  have haQ : a ∈ Set.Icc 0 Q.length := h.1 ▸ ha
  have hlen : (P.suffixAt a).length = (Q.suffixAt a).length := by
    rw [length_suffixAt P ha, length_suffixAt Q haQ, h.1]
  refine ⟨hlen, fun b ↦ ?_⟩
  by_cases hb : b ≤ 0
  · rw [prefix_nonpos _ hb, prefix_nonpos _ hb]
  by_cases hbl : (P.suffixAt a).length ≤ b
  · have full (R : Piece) (hr : R.length ≤ b) : (R.prefixAt b).support = R.support := by
      exact Set.Subset.antisymm (R.prefix_subset b)
        (by simpa only [prefix_length] using R.prefix_mono hr)
    rw [full _ hbl, full _ (hlen ▸ hbl), h.support_suffix_eq]
  · rw [support_prefix_suffixAt P ha ⟨le_of_not_ge hb, le_of_not_ge hbl⟩,
      support_prefix_suffixAt Q haQ ⟨le_of_not_ge hb, by rw [← hlen]; exact le_of_not_ge hbl⟩,
      h.2, h.2]

end Piece

namespace Valuation

/-- Section 5, `permute:trim`: remove the smallest prefix needed for a
nonnegative cap. A satisfied cap removes the empty prefix. -/
def IsCapTrim (v : Valuation) (P : Piece) (cap : ℝ) (Q : Piece) : Prop :=
  0 ≤ cap ∧ ∃ a ∈ Set.Icc 0 P.length, Q = P.suffixAt a ∧
    v.value (P.prefixAt a).support = max 0 (v.value P.support - cap) ∧
    ∀ b ∈ Set.Icc 0 P.length,
      v.value (P.prefixAt b).support = max 0 (v.value P.support - cap) → a ≤ b

/-- Section 1.3 and Section 5, `permute:trim`: a minimal cap trim exists
without positive-value or nonempty-piece assumptions. -/
theorem exists_capTrim (v : Valuation) (P : Piece) {cap : ℝ} (hc : 0 ≤ cap) :
    ∃ Q, v.IsCapTrim P cap Q := by
  have hv := v.value_nonneg P.measurableSet_support P.support_subset_unit
  obtain ⟨a, ha, he, hm⟩ := v.exists_smallest_prefix P
    (t := max 0 (v.value P.support - cap)) (le_max_left 0 _)
    (max_le hv (by linarith))
  exact ⟨P.suffixAt a, hc, a, ha, rfl, he, hm⟩

namespace IsCapTrim

theorem isSuffix {v : Valuation} {P Q : Piece} {cap : ℝ}
    (h : v.IsCapTrim P cap Q) : Q.IsSuffix P := by
  obtain ⟨_, a, ha, he, _, _⟩ := h
  exact ⟨a, ha, he⟩

theorem support_subset {v : Valuation} {P Q : Piece} {cap : ℝ}
    (h : v.IsCapTrim P cap Q) : Q.support ⊆ P.support := by
  obtain ⟨a, _, rfl⟩ := h.isSuffix
  exact P.suffix_subset a

/-- Section 5, `permute:trim`: a trim meets its cap exactly when the cap is
below the old value; otherwise it keeps the old value. -/
theorem value_eq {v : Valuation} {P Q : Piece} {cap : ℝ}
    (h : v.IsCapTrim P cap Q) : v.value Q.support = min (v.value P.support) cap := by
  obtain ⟨_, a, _, rfl, he, _⟩ := h
  have hv := v.value_prefix_add_suffix P a
  rw [he] at hv
  simp only [max_def, min_def] at hv ⊢
  split_ifs at hv ⊢ <;> linarith

theorem value_le {v : Valuation} {P Q : Piece} {cap : ℝ}
    (h : v.IsCapTrim P cap Q) : v.value Q.support ≤ cap :=
  h.value_eq.trans_le (min_le_right _ _)

/-- Section 5, `eq:permute-caps`: removing the smallest prefix preserves
every suffix satisfying the cap, including zero-valued trailing intervals. -/
theorem preserves {v : Valuation} {P Q T : Piece} {cap : ℝ}
    (h : v.IsCapTrim P cap Q) (hT : T.IsSuffix P) (hvT : v.value T.support ≤ cap) :
    T.support ⊆ Q.support := by
  obtain ⟨_, a, ha, rfl, he, hm⟩ := h
  obtain ⟨b, hb, rfl⟩ := hT
  apply P.suffix_antitone
  apply v.smallest_prefix_le_of_value_ge P he hm hb
  have hv := v.value_prefix_add_suffix P b
  have hn := v.value_nonneg (P.prefixAt b).measurableSet_support
    (P.prefixAt b).support_subset_unit
  exact max_le hn (by linarith)

/-- Section 5, `permute:trim`: satisfied caps do not remove even zero-valued cake. -/
theorem eq_self {v : Valuation} {P Q : Piece} {cap : ℝ}
    (h : v.IsCapTrim P cap Q) (hc : v.value P.support ≤ cap) : Q = P := by
  obtain ⟨_, a, ha, rfl, _, hm⟩ := h
  have he : max 0 (v.value P.support - cap) = 0 := max_eq_left (by linarith)
  rw [he] at hm
  rw [v.smallest_prefix_zero P ha hm, P.suffix_zero]

/-- Section 5's minimal-prefix convention retains an entirely zero-valued
piece, including all its geometrically nonempty components. -/
theorem eq_self_of_value_zero {v : Valuation} {P Q : Piece} {cap : ℝ}
    (h : v.IsCapTrim P cap Q) (hv : v.value P.support = 0) : Q = P :=
  h.eq_self (by rw [hv]; exact h.1)

theorem eq_empty {v : Valuation} {Q : Piece} {cap : ℝ}
    (h : v.IsCapTrim Piece.empty cap Q) : Q = Piece.empty :=
  h.eq_self_of_value_zero (by simp)

/-- Repeating a satisfied cap never removes additional zero-valued cake. -/
theorem idempotent {v : Valuation} {P Q R : Piece} {cap : ℝ}
    (h : v.IsCapTrim P cap Q) (h' : v.IsCapTrim Q cap R) : R = Q :=
  h'.eq_self h.value_le

/-- Section 5, proof of `lem:permute` (ii): an actual trim leaves equality
with the trimming agent's cap. Subsequent no-op trims preserve this witness. -/
theorem value_eq_cap_of_ne {v : Valuation} {P Q : Piece} {cap : ℝ}
    (h : v.IsCapTrim P cap Q) (hne : Q.support ≠ P.support) : v.value Q.support = cap := by
  have hc : cap < v.value P.support := by
    by_contra! hn
    exact hne (congrArg Piece.support (h.eq_self hn))
  rw [h.value_eq, min_eq_right hc.le]

/-- A surviving original suffix is a suffix of the trimmed remainder itself. -/
theorem preserves_isSuffix {v : Valuation} {P Q T : Piece} {cap : ℝ}
    (h : v.IsCapTrim P cap Q) (hT : T.IsSuffix P) (hvT : v.value T.support ≤ cap) :
    T.IsSuffix Q := h.isSuffix.of_support_subset hT (h.preserves hT hvT)

end IsCapTrim
end Valuation

/-- Section 5's successive earlier-agent caps for a single candidate piece. -/
inductive CapTrimSequence : Piece → List (Valuation × ℝ) → Piece → Prop
  | nil (P : Piece) : CapTrimSequence P [] P
  | cons {P Q R : Piece} {v : Valuation} {cap : ℝ} {caps : List (Valuation × ℝ)}
      (trim : v.IsCapTrim P cap Q) (rest : CapTrimSequence Q caps R) :
      CapTrimSequence P ((v, cap) :: caps) R

namespace CapTrimSequence

theorem isSuffix {P Q : Piece} {caps : List (Valuation × ℝ)}
    (h : CapTrimSequence P caps Q) : Q.IsSuffix P := by
  induction h with
  | nil P => exact P.whole_isSuffix
  | cons trim _ ih => exact ih.trans trim.isSuffix

theorem support_subset {P Q : Piece} {caps : List (Valuation × ℝ)}
    (h : CapTrimSequence P caps Q) : Q.support ⊆ P.support := by
  obtain ⟨a, _, rfl⟩ := h.isSuffix
  exact P.suffix_subset a

/-- Section 5, `eq:permute-caps`: all processed caps remain satisfied. -/
theorem values_le {P Q : Piece} {caps : List (Valuation × ℝ)}
    (h : CapTrimSequence P caps Q) :
    ∀ vc ∈ caps, vc.1.value Q.support ≤ vc.2 := by
  induction h with
  | nil => simp
  | @cons P Q R v cap caps trim rest ih =>
    intro vc hvc
    rcases List.mem_cons.mp hvc with rfl | hvc
    · exact (v.value_mono R.measurableSet_support Q.measurableSet_support
        rest.support_subset Q.support_subset_unit).trans trim.value_le
    · exact ih vc hvc

/-- Section 5, `eq:permute-caps`: every original suffix meeting all caps
survives every trim. This is the geometric invariant for `claim:containment`. -/
theorem preserves {P Q T : Piece} {caps : List (Valuation × ℝ)}
    (h : CapTrimSequence P caps Q) (hT : T.IsSuffix P)
    (hc : ∀ vc ∈ caps, vc.1.value T.support ≤ vc.2) : T.support ⊆ Q.support := by
  induction h with
  | nil P => obtain ⟨a, _, rfl⟩ := hT; exact P.suffix_subset a
  | cons trim rest ih =>
    exact ih (trim.preserves_isSuffix hT (hc _ List.mem_cons_self))
      (fun vc hvc ↦ hc vc (List.mem_cons_of_mem _ hvc))

/-- Section 5, proof of `lem:permute` (ii): a proper final suffix has a cap
witness from the last actual trim, even if later checks remove nothing. -/
theorem last_trim_value {P Q : Piece} {caps : List (Valuation × ℝ)}
    (h : CapTrimSequence P caps Q) (hne : Q.support ≠ P.support) :
    ∃ vc ∈ caps, vc.1.value Q.support = vc.2 := by
  induction h with
  | nil => exact (hne rfl).elim
  | @cons P Q R v cap caps trim rest ih =>
    by_cases he : R.support = Q.support
    · refine ⟨(v, cap), List.mem_cons_self, ?_⟩
      rw [he]
      exact trim.value_eq_cap_of_ne (fun hq ↦ hne (he.trans hq))
    · obtain ⟨vc, hvc, hv⟩ := ih he
      exact ⟨vc, List.mem_cons_of_mem _ hvc, hv⟩

theorem exists_sequence (P : Piece) (caps : List (Valuation × ℝ))
    (hc : ∀ vc ∈ caps, 0 ≤ vc.2) : ∃ Q, CapTrimSequence P caps Q := by
  induction caps generalizing P with
  | nil => exact ⟨P, .nil P⟩
  | cons vc caps ih =>
    obtain ⟨Q, hQ⟩ := vc.1.exists_capTrim P (hc vc List.mem_cons_self)
    obtain ⟨R, hR⟩ := ih Q (fun vd hvd ↦ hc vd (List.mem_cons_of_mem _ hvd))
    exact ⟨R, .cons hQ hR⟩

end CapTrimSequence
end CakeCuttingPsomas
