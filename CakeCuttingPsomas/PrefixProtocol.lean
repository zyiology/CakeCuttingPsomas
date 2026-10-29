module

public import CakeCuttingPsomas.RecordedProtocol

-- This project does not prescribe mathlib's copyright/license header format.
set_option linter.style.header false

/-! # Prefix cuts with recorded values

Section 1.3's prefix cuts implemented by one Cut and at most one Eval per agent.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas.RecordedState

/-- Scan recorded component values for the first interval attaining the target.
The scan is free; only the selected component issues queries. -/
def prefixCutAux {n : ℕ} (s : RecordedState n) (i : Fin n) :
    List CakeInterval → ℝ → RWProtocol n (ℝ × RecordedState n)
  | [], _ => .done (0, s)
  | I :: Is, t =>
    if t ≤ 0 then .done (0, s)
    else if t ≤ s.values i I then
      .ask (.cut i I.left t) (fun x ↦
        (s.recordCut I x).map (fun s' ↦ (x - I.left, s')))
    else (prefixCutAux s i Is (t - s.values i I)).map
      (fun result ↦ (I.length + result.1, result.2))

/-- A recorded-value prefix cut returns a traversal position and updated records. -/
def prefixCut {n : ℕ} (s : RecordedState n) (i : Fin n) (P : Piece) (t : ℝ) :
    RWProtocol n (ℝ × RecordedState n) := s.prefixCutAux i P.intervals t

private theorem prefix_value_cons (v : Valuation) (I : CakeInterval) (Is : List CakeInterval)
    (h : (I :: Is).Pairwise (fun I J ↦ Disjoint I.support J.support)) (r : ℝ) :
    (v.value ((⟨I :: Is, h⟩ : Piece).prefixAt r).support) =
      v.value (I.before (I.left + r)).support +
        v.value ((⟨Is, (List.pairwise_cons.mp h).2⟩ : Piece).prefixAt (r - I.length)).support := by
  rw [Piece.support_prefixAt_cons]
  apply v.value_union (I.before _).measurableSet_support _ (I.before _).support_subset_unit
    (Piece.support_subset_unit _)
  · apply Set.disjoint_left.mpr
    rintro x hx hxT
    have hxI := I.before_subset _ hx
    obtain ⟨J, hJ, hxJ⟩ := Piece.prefix_subset _ _ hxT
    exact Set.disjoint_left.mp ((List.pairwise_cons.mp h).1 J hJ) hxI hxJ
  · exact Piece.measurableSet_support _

/-- At a component boundary the prefix is the entire first component. -/
private theorem prefix_value_boundary (v : Valuation) (I : CakeInterval) (Is : List CakeInterval)
    (h : (I :: Is).Pairwise (fun I J ↦ Disjoint I.support J.support)) :
    v.value ((⟨I :: Is, h⟩ : Piece).prefixAt I.length).support = v.value I.support := by
  rw [prefix_value_cons]
  simp [CakeInterval.length, CakeInterval.before_right]

/-- Section 1.3's recorded-value bound: a smallest prefix cut costs at most
`n + 1` Robertson–Webb queries and leaves correct records for the participants.
The guarantee applies to unnormalized valuations and zero-valued input pieces. -/
private theorem prefixCut_runs_aux {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) (i : Fin n) (P : Piece) (hP : s.Compatible P) (t : ℝ)
    (ht : 0 ≤ t) (htP : t ≤ (v i).value P.support) :
    ∃ r s' count, (s.prefixCut i P t).Runs v (r, s') count ∧ count ≤ n + 1 ∧
      s'.Correct v ∧ r ∈ Set.Icc 0 P.length ∧ (v i).value (P.prefixAt r).support = t ∧
      (∀ q ∈ Set.Icc 0 P.length, (v i).value (P.prefixAt q).support = t → r ≤ q) ∧
      s.Refines s' ∧ s'.Represents (P.prefixAt r).support ∧
      (∀ J ∈ s.partition.intervals, Disjoint J.support P.support → J ∈ s'.partition.intervals) ∧
      s.TraversalRefines s' := by
  obtain ⟨Is, hd⟩ := P
  induction Is generalizing t with
  | nil =>
    have htz : t = 0 := by
      have hz : (v i).value ((⟨[], hd⟩ : Piece).support) = 0 := by simp [Piece.support]
      rw [hz] at htP
      exact le_antisymm htP ht
    subst t
    refine ⟨0, s, 0, .done _, by omega, hs, ?_, ?_, ?_, refines_refl s, ?_,
      (fun _ h _ ↦ h), traversalRefines_refl s⟩
    · simp [Piece.length]
    · simp
    · intro q hq _; exact hq.1
    · simpa using represents_empty s
  | cons I Is ih =>
    let P : Piece := ⟨I :: Is, hd⟩
    let T : Piece := ⟨Is, (List.pairwise_cons.mp hd).2⟩
    have hI : I ∈ s.partition.intervals := hP I (by simp)
    have hvI := hs i I hI
    have hT : s.Compatible T := fun J hJ ↦ hP J (List.mem_cons_of_mem I hJ)
    have hlen : P.length = I.length + T.length := by simp [P, T, Piece.length]
    by_cases hzero : t ≤ 0
    · have htz := le_antisymm hzero ht
      subst t
      refine ⟨0, s, 0, ?_, by omega, hs, ⟨le_rfl, P.length_nonneg⟩, by simp, ?_,
        refines_refl s, ?_, (fun _ h _ ↦ h), traversalRefines_refl s⟩
      · simp only [prefixCut, prefixCutAux, le_refl, ite_true]; exact .done _
      · intro q hq _; exact hq.1
      · simpa using represents_empty s
    · by_cases hfirst : t ≤ s.values i I
      · have htI : t ≤ (v i).value I.support := hfirst.trans_eq hvI
        have ht1 : t ≤ (v i).value (Set.Icc I.left 1) := htI.trans
          ((v i).value_mono I.measurableSet_support measurableSet_Icc
            (fun x hx ↦ by
              have hleft : I.left ≤ x := by
                unfold CakeInterval.support at hx
                split_ifs at hx <;> exact hx.1
              exact ⟨hleft, (I.support_subset_unit hx).2⟩)
            (fun _ hx ↦ ⟨I.left_nonneg.trans hx.1, hx.2⟩))
        obtain ⟨x, hx, _⟩ := RWQuery.existsUnique_cut_answer v i I.left_nonneg
          (I.ordered.le.trans I.right_le_one) ht ht1
        obtain ⟨hxI, hval⟩ := RWQuery.cut_answer_before v i I hx htI
        obtain ⟨s', c, hrun, hs', hc, href, hb, _, hkeep, htrav⟩ :=
          recordCut_runs_spec hs I hI x
        have hpos : x - I.left ∈ Set.Icc 0 P.length :=
          ⟨sub_nonneg.mpr hxI.1, by
            have := T.length_nonneg
            dsimp [CakeInterval.length] at hlen
            linarith [hxI.2]⟩
        have hvalue : (v i).value (P.prefixAt (x - I.left)).support = t := by
          rw [prefix_value_cons]
          have hsub : x - I.left - I.length ≤ 0 := by dsimp [CakeInterval.length]; linarith [hxI.2]
          rw [Piece.prefix_nonpos _ hsub]
          simpa using hval
        refine ⟨x - I.left, s', c + 1, ?_, by omega, hs', hpos, hvalue, ?_, href, ?_, ?_, htrav⟩
        · simp only [prefixCut, prefixCutAux, ite_eq_right hzero, ite_eq_left hfirst]
          exact .ask hx (hrun.map _)
        · intro q hq hqt
          by_cases hqI : I.length ≤ q
          · dsimp [CakeInterval.length] at hqI; linarith [hxI.2]
          · have hqb : I.left + q ∈ Set.Icc I.left I.right :=
              ⟨by linarith [hq.1], by dsimp [CakeInterval.length] at hqI; linarith⟩
            have hvq : (v i).value (Set.Icc I.left (I.left + q)) = t := by
              rw [prefix_value_cons] at hqt
              rw [Piece.prefix_nonpos _ (sub_nonpos.mpr (le_of_not_ge hqI))] at hqt
              simpa [(v i).value_before I hqb] using hqt
            have := hx.2.2.2.2.2.2.2 (I.left + q) hqb.1
              (hqb.2.trans I.right_le_one) hvq
            linarith
        · refine ⟨I.before x, hb, ?_⟩
          rw [Piece.support_prefixAt_cons]
          have hsub : x - I.left - I.length ≤ 0 := by
            dsimp [CakeInterval.length]; linarith [hxI.2]
          rw [Piece.prefix_nonpos _ hsub]
          simp
        · intro J hJ hdJ
          apply hkeep J hJ
          intro heq
          subst J
          exact Set.disjoint_left.mp hdJ I.left_mem_support
            ⟨I, by simp, I.left_mem_support⟩
      · have htI : (v i).value I.support < t := by linarith [hvI]
        have htail : 0 ≤ t - s.values i I := by linarith
        have hsum : (v i).value P.support = (v i).value I.support + (v i).value T.support := by
          rw [P.value_eq_sum, T.value_eq_sum]
          rfl
        have htailP : t - s.values i I ≤ (v i).value T.support := by linarith
        obtain ⟨r, s', c, hrun, hc, hs', hr, hval, hmin, href, hrep, hkeep, htrav⟩ :=
          ih (t - s.values i I) htail T.disjoint hT htailP
        have hposition : I.length + r ∈ Set.Icc 0 P.length :=
          ⟨add_nonneg I.length_pos.le hr.1, by rw [hlen]; linarith [hr.2]⟩
        have hvalue : (v i).value (P.prefixAt (I.length + r)).support = t := by
          rw [prefix_value_cons]
          have he : I.before (I.left + (I.length + r)) = Piece.ofInterval I := by
            exact dite_eq_left (by dsimp [CakeInterval.length]; linarith [hr.1])
          rw [he, Piece.support_ofInterval]
          simp [hval, hvI]
        refine ⟨I.length + r, s', c, ?_, hc, hs', hposition, hvalue, ?_, href, ?_, ?_, htrav⟩
        · simpa only [prefixCut, prefixCutAux, ite_eq_right hzero, ite_eq_right hfirst] using
            hrun.map (fun result ↦ (I.length + result.1, result.2))
        · intro q hq hqt
          have hIq : I.length ≤ q := by
            by_contra h
            have hmono := (v i).monotone_value_prefix P (le_of_not_ge h)
            change (v i).value (P.prefixAt q).support ≤
              (v i).value (P.prefixAt I.length).support at hmono
            rw [hqt, prefix_value_boundary] at hmono
            linarith
          have hqT : q - I.length ∈ Set.Icc 0 T.length :=
            ⟨sub_nonneg.mpr hIq, by rw [hlen] at hq; linarith [hq.2]⟩
          have hvq : (v i).value (T.prefixAt (q - I.length)).support = t - s.values i I := by
            rw [prefix_value_cons] at hqt
            have he : I.before (I.left + q) = Piece.ofInterval I := by
              simp [CakeInterval.before, show I.right ≤ I.left + q by
                dsimp [CakeInterval.length] at hIq; linarith]
            rw [he, Piece.support_ofInterval] at hqt
            linarith
          have := hmin _ hqT hvq
          linarith
        · have hIT : Disjoint I.support T.support := by
            apply Set.disjoint_left.mpr
            rintro x hxI ⟨J, hJ, hxJ⟩
            exact Set.disjoint_left.mp ((List.pairwise_cons.mp hd).1 J hJ) hxI hxJ
          have hhead : s'.Represents I.support := by
            refine ⟨Piece.ofInterval I, ?_, Piece.support_ofInterval I⟩
            intro J hJ
            simp only [Piece.ofInterval, List.mem_singleton] at hJ
            subst J
            exact hkeep I hI hIT
          have hdis := hIT.mono_right (T.prefix_subset r)
          have hrep' := hhead.union hrep hdis
          have he : I.before (I.left + (I.length + r)) = Piece.ofInterval I :=
            dite_eq_left (by dsimp [CakeInterval.length]; linarith [hr.1])
          simpa only [Piece.support_prefixAt_cons, he, Piece.support_ofInterval,
            add_sub_cancel_left] using hrep'
        · intro J hJ hdJ
          apply hkeep J hJ
          apply hdJ.mono_right
          rintro x ⟨K, hK, hxK⟩
          exact ⟨K, List.mem_cons_of_mem I hK, hxK⟩

/-- Section 1.3's smallest-prefix protocol with inherited records. It uses at
most `n + 1` queries, preserves all previously represented pieces, and records
both resulting pieces for future calls. Recursive valuations need not be normalized. -/
theorem prefixCut_runs {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) (i : Fin n) (P : Piece) (hP : s.Compatible P) (t : ℝ)
    (ht : 0 ≤ t) (htP : t ≤ (v i).value P.support) :
    ∃ r s' count, (s.prefixCut i P t).Runs v (r, s') count ∧ count ≤ n + 1 ∧
      s'.Correct v ∧ s.Refines s' ∧ r ∈ Set.Icc 0 P.length ∧
      (v i).value (P.prefixAt r).support = t ∧
      (∀ q ∈ Set.Icc 0 P.length, (v i).value (P.prefixAt q).support = t → r ≤ q) ∧
      s'.Represents (P.prefixAt r).support ∧ s'.Represents (P.suffixAt r).support := by
  obtain ⟨r, s', count, hrun, hc, hs', hr, hv, hmin, href, hp, _⟩ :=
    prefixCut_runs_aux hs i P hP t ht htP
  refine ⟨r, s', count, hrun, hc, hs', href, hr, hv, hmin, hp, ?_⟩
  rw [Piece.support_suffix]
  exact (href P hP).diff hp

/-- Section 1.3 and Section 4, `line:rep:cells`: prefix cuts preserve the
common traversal of every inherited piece, in addition to its support. -/
theorem prefixCut_runs_traversal {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) (i : Fin n) (P : Piece) (hP : s.Compatible P) (t : ℝ)
    (ht : 0 ≤ t) (htP : t ≤ (v i).value P.support) :
    ∃ r s' count, (s.prefixCut i P t).Runs v (r, s') count ∧ count ≤ n + 1 ∧
      s'.Correct v ∧ s.TraversalRefines s' ∧ r ∈ Set.Icc 0 P.length ∧
      (v i).value (P.prefixAt r).support = t ∧
      s'.Represents (P.prefixAt r).support := by
  obtain ⟨r, s', count, hr, hc, hs', hx, hv, _, _, hp, _, htrav⟩ :=
    prefixCut_runs_aux hs i P hP t ht htP
  exact ⟨r, s', count, hr, hc, hs', htrav, hx, hv, hp⟩

/-- Terminal prefix cut for Section 2's cut-and-choose base case. The cutter's
records locate the cut; only the chooser's split fragment is evaluated. The
result is the traversal position and the chooser's value of the prefix.
No records are refreshed, since this call finishes the division. -/
def terminalPrefixAux {n : ℕ} (s : RecordedState n) (cutter chooser : Fin n) :
    List CakeInterval → ℝ → RWProtocol n (ℝ × ℝ)
  | [], _ => .done (0, 0)
  | I :: Is, t =>
    if t ≤ 0 then .done (0, 0)
    else if t ≤ s.values cutter I then
      .ask (.cut cutter I.left t) (fun x ↦
        .ask (.eval chooser I.left x) (fun a ↦ .done (x - I.left, a)))
    else (terminalPrefixAux s cutter chooser Is (t - s.values cutter I)).map
      (fun result ↦ (I.length + result.1, s.values chooser I + result.2))

/-- Terminal prefix operation on an ordered piece, using inherited cell values. -/
def terminalPrefix {n : ℕ} (s : RecordedState n) (cutter chooser : Fin n)
    (P : Piece) (t : ℝ) : RWProtocol n (ℝ × ℝ) :=
  s.terminalPrefixAux cutter chooser P.intervals t

/-- Section 2 (`algo:divide`, `thm: main theorem`): the terminal cut-and-choose
split uses at most two queries, including the chooser's prefix value. It finds
the smallest prefix and applies to arbitrary ordered compatible pieces and
unnormalized or zero valuations. Section 1.3 supplies the inherited records. -/
theorem terminalPrefix_runs {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) (i j : Fin n) (P : Piece) (hP : s.Compatible P) (t : ℝ)
    (ht : 0 ≤ t) (htP : t ≤ (v i).value P.support) :
    ∃ r a count, (s.terminalPrefix i j P t).Runs v (r, a) count ∧ count ≤ 2 ∧
      r ∈ Set.Icc 0 P.length ∧ (v i).value (P.prefixAt r).support = t ∧
      a = (v j).value (P.prefixAt r).support ∧
      ∀ q ∈ Set.Icc 0 P.length, (v i).value (P.prefixAt q).support = t → r ≤ q := by
  obtain ⟨Is, hd⟩ := P
  induction Is generalizing t with
  | nil =>
    have htz : t = 0 := by
      have hz : (v i).value ((⟨[], hd⟩ : Piece).support) = 0 := by simp [Piece.support]
      rw [hz] at htP
      exact le_antisymm htP ht
    subst t
    refine ⟨0, 0, 0, .done _, by omega, ?_, by simp, by simp, ?_⟩
    · simp [Piece.length]
    · intro q hq _; exact hq.1
  | cons I Is ih =>
    let P : Piece := ⟨I :: Is, hd⟩
    let T : Piece := ⟨Is, (List.pairwise_cons.mp hd).2⟩
    have hI : I ∈ s.partition.intervals := hP I (by simp)
    have hvI := hs i I hI
    have hT : s.Compatible T := fun J hJ ↦ hP J (List.mem_cons_of_mem I hJ)
    have hlen : P.length = I.length + T.length := by simp [P, T, Piece.length]
    by_cases hzero : t ≤ 0
    · have htz := le_antisymm hzero ht
      subst t
      refine ⟨0, 0, 0, ?_, by omega, ⟨le_rfl, P.length_nonneg⟩,
        by simp, by simp, ?_⟩
      · simp only [terminalPrefix, terminalPrefixAux, le_refl, ite_true]; exact .done _
      · intro q hq _; exact hq.1
    · by_cases hfirst : t ≤ s.values i I
      · have htI : t ≤ (v i).value I.support := hfirst.trans_eq hvI
        have ht1 : t ≤ (v i).value (Set.Icc I.left 1) := htI.trans
          ((v i).value_mono I.measurableSet_support measurableSet_Icc
            (fun x hx ↦ by
              have hleft : I.left ≤ x := by
                unfold CakeInterval.support at hx
                split_ifs at hx <;> exact hx.1
              exact ⟨hleft, (I.support_subset_unit hx).2⟩)
            (fun _ hx ↦ ⟨I.left_nonneg.trans hx.1, hx.2⟩))
        obtain ⟨x, hx, _⟩ := RWQuery.existsUnique_cut_answer v i I.left_nonneg
          (I.ordered.le.trans I.right_le_one) ht ht1
        obtain ⟨hxI, hval⟩ := RWQuery.cut_answer_before v i I hx htI
        have hsub : x - I.left - I.length ≤ 0 := by
          dsimp [CakeInterval.length]; linarith [hxI.2]
        have val (w : Valuation) :
            w.value (P.prefixAt (x - I.left)).support = w.value (Set.Icc I.left x) := by
          rw [prefix_value_cons, Piece.prefix_nonpos _ hsub]
          simpa using w.value_before I hxI
        refine ⟨x - I.left, (v j).value (Set.Icc I.left x), 2, ?_, le_rfl,
          ⟨sub_nonneg.mpr hxI.1, ?_⟩, ?_, (val _).symm, ?_⟩
        · simp only [terminalPrefix, terminalPrefixAux, ite_eq_right hzero, ite_eq_left hfirst]
          exact .ask hx (.ask ⟨I.left_nonneg, hxI.1,
            hxI.2.trans I.right_le_one, rfl⟩ (.done _))
        · have := T.length_nonneg
          dsimp [CakeInterval.length] at hlen
          linarith [hxI.2]
        · rw [val]
          simpa [(v i).value_before I hxI] using hval
        · intro q hq hqt
          by_cases hqI : I.length ≤ q
          · dsimp [CakeInterval.length] at hqI; linarith [hxI.2]
          · have hqb : I.left + q ∈ Set.Icc I.left I.right :=
              ⟨by linarith [hq.1], by dsimp [CakeInterval.length] at hqI; linarith⟩
            have hvq : (v i).value (Set.Icc I.left (I.left + q)) = t := by
              rw [prefix_value_cons] at hqt
              rw [Piece.prefix_nonpos _ (sub_nonpos.mpr (le_of_not_ge hqI))] at hqt
              simpa [(v i).value_before I hqb] using hqt
            have := hx.2.2.2.2.2.2.2 (I.left + q) hqb.1
              (hqb.2.trans I.right_le_one) hvq
            linarith
      · have htI : (v i).value I.support < t := by linarith [hvI]
        have htail : 0 ≤ t - s.values i I := by linarith
        have hsum : (v i).value P.support = (v i).value I.support + (v i).value T.support := by
          rw [P.value_eq_sum, T.value_eq_sum]
          rfl
        have htailP : t - s.values i I ≤ (v i).value T.support := by linarith
        obtain ⟨r, a, c, hrun, hc, hr, hval, ha, hmin⟩ :=
          ih (t - s.values i I) htail T.disjoint hT htailP
        have val (w : Valuation) :
            w.value (P.prefixAt (I.length + r)).support =
              w.value I.support + w.value (T.prefixAt r).support := by
          rw [prefix_value_cons]
          have he : I.before (I.left + (I.length + r)) = Piece.ofInterval I :=
            dite_eq_left (by dsimp [CakeInterval.length]; linarith [hr.1])
          simp only [he, Piece.support_ofInterval, add_sub_cancel_left]
          rfl
        refine ⟨I.length + r, s.values j I + a, c, ?_, hc,
          ⟨add_nonneg I.length_pos.le hr.1, ?_⟩, ?_, ?_, ?_⟩
        · simpa only [terminalPrefix, terminalPrefixAux, ite_eq_right hzero,
            ite_eq_right hfirst] using
            hrun.map (fun result ↦ (I.length + result.1, s.values j I + result.2))
        · rw [hlen]; linarith [hr.2]
        · rw [val, hval, ← hvI]; ring
        · rw [val, hs j I hI, ha]
        · intro q hq hqt
          have hIq : I.length ≤ q := by
            by_contra h
            have hmono := (v i).monotone_value_prefix P (le_of_not_ge h)
            change (v i).value (P.prefixAt q).support ≤
              (v i).value (P.prefixAt I.length).support at hmono
            rw [hqt, prefix_value_boundary] at hmono
            linarith
          have hqT : q - I.length ∈ Set.Icc 0 T.length :=
            ⟨sub_nonneg.mpr hIq, by rw [hlen] at hq; linarith [hq.2]⟩
          have hvq : (v i).value (T.prefixAt (q - I.length)).support = t - s.values i I := by
            rw [prefix_value_cons] at hqt
            have he : I.before (I.left + q) = Piece.ofInterval I := by
              simp [CakeInterval.before, show I.right ≤ I.left + q by
                dsimp [CakeInterval.length] at hIq; linarith]
            rw [he, Piece.support_ofInterval] at hqt
            linarith
          have := hmin _ hqT hvq
          linarith

end CakeCuttingPsomas.RecordedState
