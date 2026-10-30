module

public import CakeCuttingPsomas.EqualPartition
public import CakeCuttingPsomas.TraversalPartition

set_option linter.style.header false

/-! # Repair's common residue partition

Algorithm `alg:repair`, line `line:rep:cells`, and the proof of `lem:repair main`
in Section 4 of `paper/main.tex`. Paper cells are consecutive portions of one
fixed traversal, not individual intervals in the inherited recorded partition.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.RepairPartition

open TraversalPartition

-- Preserve the existing Repair-facing names for the shared mathematical API.
export TraversalPartition (next cell starts support_cell cells_partition cell_nonempty
  card_starts cell_value_le marks_card_le cell_does_not_cross_mark)

attribute [local instance] Classical.propDecidable

/-- Query-independent output of collecting marks on a fixed residue traversal. -/
structure Marks (n : ℕ) where
  state : RecordedState n
  points : Finset ℝ

/-- Each target is read from the initial records before this loop starts.
Representations may subdivide, but their traversal prefixes remain identical. -/
def mark {n : ℕ} (R : Piece) :
    List (Fin n × ℝ) → RecordedState n → RWProtocol n (Marks n)
  | [], s => .done ⟨s, ∅⟩
  | (i, t) :: ts, s =>
    (s.prefixCut i (s.representAlong R) t).bind fun (x, s') ↦
      (mark R ts s').map fun r ↦ ⟨r.state, insert x r.points⟩

/-- Section 4, `line:rep:cells`: collecting marks preserves the common traversal
and all inherited records, at at most `n+1` queries per requested prefix. -/
theorem mark_correct {n : ℕ} (R : Piece) (ts : List (Fin n × ℝ))
    (s : RecordedState n) (v : Fin n → Valuation) (hs : s.Correct v)
    (hR : ∃ Q, s.Compatible Q ∧ R.SameTraversal Q)
    (ht : ∀ p ∈ ts, 0 < p.2 ∧ p.2 < (v p.1).value R.support) :
    ∃ r count, (mark R ts s).Runs v r count ∧ count ≤ ts.length * (n + 1) ∧
      r.state.Correct v ∧ s.TraversalRefines r.state ∧ r.points.card ≤ ts.length ∧
      (∀ x ∈ r.points, 0 < x ∧ x < R.length ∧
        r.state.Represents (R.prefixAt x).support) ∧
      (∀ p ∈ ts, ∃ x ∈ r.points, (v p.1).value (R.prefixAt x).support = p.2) := by
  induction ts generalizing s with
  | nil =>
    exact ⟨⟨s, ∅⟩, 0, .done _, by simp, hs, s.traversalRefines_refl,
      by simp, by simp, by simp⟩
  | cons p ts ih =>
    obtain ⟨hQ, he⟩ := RecordedState.representAlong_spec hR
    obtain ⟨ht0, htR⟩ := ht p (by simp)
    obtain ⟨x, s', a, ha, hca, hs', href, hx, hval, hp⟩ :=
      RecordedState.prefixCut_runs_traversal hs p.1 (s.representAlong R) hQ p.2
        ht0.le (by simpa [← he.support_eq] using htR.le)
    have hv : (v p.1).value (R.prefixAt x).support = p.2 := by
      simpa [← he.2 x] using hval
    have hx0 : 0 < x := by
      by_contra hn
      rw [Piece.prefix_nonpos R (le_of_not_gt hn)] at hv
      simp at hv
      linarith
    have hxR : x < R.length := by
      by_contra hn
      have hh : (R.prefixAt x).support = R.support := by
        have hmono := R.prefix_mono (le_of_not_gt hn)
        dsimp only at hmono
        rw [Piece.prefix_length] at hmono
        exact Set.Subset.antisymm (R.prefix_subset x) hmono
      rw [hh] at hv
      linarith
    have hp' : s'.Represents (R.prefixAt x).support := by simpa [← he.2 x] using hp
    obtain ⟨Q', hQ', he'⟩ := href (s.representAlong R) hQ
    obtain ⟨r, b, hb, hcb, hrs, hrr, hcard, hpoints, htargets⟩ :=
      ih s' hs' ⟨Q', hQ', he.trans he'⟩ (fun q hq ↦ ht q (by simp [hq]))
    refine ⟨⟨r.state, insert x r.points⟩, a + b, ha.bind (hb.map _), ?_, hrs,
      href.trans hrr, ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · exact (Finset.card_insert_le _ _).trans (by simpa using Nat.add_le_add_right hcard 1)
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ⟨hx0, hxR, hrr.refines.represents hp'⟩
      · exact hpoints y hy
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨x, Finset.mem_insert_self _ _, hv⟩
      · obtain ⟨y, hy, hvy⟩ := htargets q hq
        exact ⟨y, Finset.mem_insert_of_mem hy, hvy⟩

/-- All agents' `M-1` equal-value marks; targets depend only on stored values. -/
def targets {n : ℕ} (s : RecordedState n) (R : Piece) (M : ℕ) : List (Fin n × ℝ) :=
  (List.finRange n).flatMap fun i ↦
    (List.finRange (M - 1)).map fun k ↦ (i, ((k.val + 1 : ℕ) : ℝ) * (s.pieceValue i R / M))

@[simp] theorem length_targets {n : ℕ} (s : RecordedState n) (R : Piece) (M : ℕ) :
    (targets s R M).length = n * (M - 1) := by
  simp [targets, List.length_flatMap, List.sum_replicate]

/-- The valuation-independent marking protocol for a specified positive `M`. -/
def collect {n : ℕ} (s : RecordedState n) (R : Piece) (M : ℕ) : RWProtocol n (Marks n) :=
  mark R (targets s R M) s

/-- Section 4, `line:rep:cells`: every equal-value boundary is marked on the
same traversal, using at most `n(M-1)(n+1)` queries. -/
theorem collect_correct {n : ℕ} (s : RecordedState n) (R : Piece) (M : ℕ)
    (v : Fin n → Valuation) (hs : s.Correct v) (hR : s.Compatible R) (hM : 0 < M)
    (hpos : ∀ i, 0 < (v i).value R.support) :
    ∃ r count, (collect s R M).Runs v r count ∧ count ≤ n * (M - 1) * (n + 1) ∧
      r.state.Correct v ∧ s.TraversalRefines r.state ∧ r.points.card ≤ n * (M - 1) ∧
      (∀ x ∈ r.points, 0 < x ∧ x < R.length ∧
        r.state.Represents (R.prefixAt x).support) ∧
      (∀ i (k : Fin (M - 1)), ∃ x ∈ r.points,
        (v i).value (R.prefixAt x).support = (k.val + 1 : ℕ) * ((v i).value R.support / M)) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have ht : ∀ p ∈ targets s R M, 0 < p.2 ∧ p.2 < (v p.1).value R.support := by
    intro p hp
    obtain ⟨i, _, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
    rw [RecordedState.pieceValue_eq hs hR]
    have hk : (0 : ℝ) < (k.val + 1 : ℕ) := by positivity
    have hkm : ((k.val + 1 : ℕ) : ℝ) < M := by exact_mod_cast (show k.val + 1 < M by omega)
    constructor
    · exact mul_pos hk (div_pos (hpos i) hm)
    · have he : (M : ℝ) * ((v i).value R.support / M) = (v i).value R.support :=
        mul_div_cancel₀ _ (ne_of_gt hm)
      nlinarith [div_pos (hpos i) hm]
  obtain ⟨r, c, hr, hc, hrs, href, hcard, hpoints, htargets⟩ :=
    mark_correct R (targets s R M) s v hs ⟨R, hR, Piece.SameTraversal.refl R⟩ ht
  refine ⟨r, c, hr, by simpa using hc, hrs, href, by simpa using hcard, hpoints, ?_⟩
  intro i k
  have hp : (i, ((k.val + 1 : ℕ) : ℝ) * (s.pieceValue i R / M)) ∈ targets s R M := by
    simp only [targets, List.mem_flatMap, List.mem_map]
    exact ⟨i, List.mem_finRange i, k, List.mem_finRange k, rfl⟩
  simpa [RecordedState.pieceValue_eq hs hR] using htargets _ hp


/-- Number of paper cells, independent of the number of recorded intervals. -/
def Marks.cellCount {n : ℕ} (r : Marks n) : ℕ := (starts r.points).card

/-- Paper cells indexed in the common traversal order. -/
def Marks.cells {n : ℕ} (r : Marks n) (R : Piece) : Fin r.cellCount → Piece :=
  fun j ↦ cell R r.points ((starts r.points).orderIsoOfFin rfl j).val

private theorem length_pos_of_value_pos (R : Piece) (v : Valuation)
    (h : 0 < v.value R.support) : 0 < R.length := by
  by_contra hn
  have he : R.length = 0 := le_antisymm (le_of_not_gt hn) R.length_nonneg
  have hh := congrArg Piece.support R.prefix_length
  rw [he, Piece.prefix_zero, Piece.support_empty] at hh
  rw [← hh, v.value_empty] at h
  exact (lt_irrefl 0) h

/-- Repair's integer equal-partition size. -/
def size (n : ℕ) (ε : ℝ) : ℕ := ⌈1 / (3 * (n : ℝ) * ε)⌉₊

/-- Section 4, proof of `lem:repair main`: ceiling estimates giving enough
round-robin cells, a strict upper cell bound, and the per-cell value scale. -/
theorem size_bounds (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (hεmax : ε ≤ 1 / (6 * (n : ℝ) ^ 3)) :
    0 < size n ε ∧ 2 * n ^ 2 ≤ size n ε ∧
      ((n * (size n ε - 1) + 1 : ℕ) : ℝ) < 1 / (2 * ε) ∧
      1 / (size n ε : ℝ) ≤ 3 * (n : ℝ) * ε := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : 0 < 3 * (n : ℝ) * ε := by positivity
  have hx : 0 < 1 / (3 * (n : ℝ) * ε) := by positivity
  have hm : 0 < size n ε := Nat.ceil_pos.mpr hx
  have hmR : (0 : ℝ) < size n ε := by exact_mod_cast hm
  have hlo : 1 / (3 * (n : ℝ) * ε) ≤ (size n ε : ℝ) := Nat.le_ceil _
  have hhi : (size n ε : ℝ) < 1 / (3 * (n : ℝ) * ε) + 1 :=
    Nat.ceil_lt_add_one hx.le
  have hmax : ε * (6 * (n : ℝ) ^ 3) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hεmax
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have heps : ε ≤ 1 / 6 := by nlinarith
  have hlower : 2 * (n : ℝ) ^ 2 ≤ 1 / (3 * (n : ℝ) * ε) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [hmax]
  have hcount : ((n * (size n ε - 1) + 1 : ℕ) : ℝ) <
      1 / (3 * ε) + 1 := by
    have hsub : ((size n ε - 1 : ℕ) : ℝ) = (size n ε : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ size n ε)]; norm_num
    have hdiv : (n : ℝ) * (1 / (3 * (n : ℝ) * ε)) = 1 / (3 * ε) := by
      field_simp
    push_cast
    rw [hsub]
    nlinarith
  have hupper : 1 / (3 * ε) + 1 ≤ 1 / (2 * ε) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * ε)).mpr
    have hcancel : (1 / (3 * ε)) * (2 * ε) = (2 : ℝ) / 3 := by field_simp
    nlinarith
  refine ⟨hm, ?_, hcount.trans_le hupper, ?_⟩
  · exact_mod_cast hlower.trans hlo
  · apply (div_le_iff₀ hmR).mpr
    have hh := (div_le_iff₀ hd).mp hlo
    nlinarith

/-- Construct Repair's common residue partition using inherited records. -/
def run {n : ℕ} (s : RecordedState n) (R : Piece) (ε : ℝ) : RWProtocol n (Marks n) :=
  collect s R (size n ε)

/-- Section 4, Algorithm `alg:repair`, line `line:rep:cells`, and proof of
`lem:repair main`: exact common residue partition, inherited records, the paper's
cell counts and value bounds, and `n(M-1)(n+1)` Robertson--Webb queries. -/
theorem run_correct {n : ℕ} (hn : 2 ≤ n) (s : RecordedState n) (R : Piece)
    (ε : ℝ) (v : Fin n → Valuation) (hs : s.Correct v) (hR : s.Compatible R)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / (6 * (n : ℝ) ^ 3))
    (hpos : ∀ i, 0 < (v i).value R.support) :
    ∃ r count, (run s R ε).Runs v r count ∧
      count ≤ n * (size n ε - 1) * (n + 1) ∧
      r.state.Correct v ∧ s.TraversalRefines r.state ∧
      (∀ j, r.state.Represents (r.cells R j).support) ∧
      (∀ j, (r.cells R j).support.Nonempty) ∧
      (⋃ j, (r.cells R j).support) = R.support ∧
      (∀ j k, j ≠ k → Disjoint (r.cells R j).support (r.cells R k).support) ∧
      size n ε ≤ r.cellCount ∧ r.cellCount ≤ n * (size n ε - 1) + 1 ∧
      (r.cellCount : ℝ) < 1 / (2 * ε) ∧
      (∀ i j, (v i).value (r.cells R j).support ≤ (v i).value R.support / size n ε) ∧
      (∀ i j, (v i).value (r.cells R j).support ≤ 3 * (n : ℝ) * ε * (v i).value R.support) := by
  obtain ⟨hm, _, hupper, hinv⟩ := size_bounds n hn ε hε hεmax
  obtain ⟨r, c, hr, hc, hrs, href, hcard, hp, hv⟩ := collect_correct s R (size n ε) v hs hR hm hpos
  let i₀ : Fin n := ⟨0, by omega⟩
  have hL := length_pos_of_value_pos R (v i₀) (hpos i₀)
  have hpoints : ∀ x ∈ r.points, 0 < x ∧ x < R.length := fun x hx ↦ ⟨(hp x hx).1, (hp x hx).2.1⟩
  have hcount : r.cellCount = r.points.card + 1 := card_starts (fun x hx ↦ (hp x hx).1)
  have hcardlo := marks_card_le R r.points (size n ε) (v i₀) hm (hpos i₀) (hv i₀)
  have hcardhi : r.cellCount ≤ n * (size n ε - 1) + 1 := by rw [hcount]; omega
  have hrep (x : ℝ) (hx : x = R.length ∨ x ∈ starts r.points) :
      r.state.Represents (R.prefixAt x).support := by
    rcases hx with rfl | hx
    · simpa using href.refines R hR
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · simpa using r.state.represents_empty
      · exact (hp x hx).2.2
  obtain ⟨hcover, hdis⟩ := cells_partition R r.points hL hpoints
  have hvalues (i : Fin n) (j : Fin r.cellCount) :
      (v i).value (r.cells R j).support ≤ (v i).value R.support / size n ε :=
    cell_value_le R r.points (size n ε) (v i) hm (hpos i) hL hpoints (hv i)
      _ (Finset.orderEmbOfFin_mem (starts r.points) rfl j)
  refine ⟨r, c, hr, hc, hrs, href, ?_, ?_, ?_, ?_, ?_, hcardhi, ?_, hvalues, ?_⟩
  · intro j
    let a := ((starts r.points).orderIsoOfFin rfl j).val
    have ha := ((starts r.points).orderIsoOfFin rfl j).property
    have hb := (next_spec hpoints (start_lt hL hpoints ha)).2.2.1
    have hb' : next R.length r.points a = R.length ∨ next R.length r.points a ∈ starts r.points :=
      hb.imp_right Finset.mem_insert_of_mem
    change r.state.Represents (cell R r.points a).support
    rw [support_cell]
    exact (hrep _ hb').diff (hrep _ (Or.inr ha))
  · intro j
    exact cell_nonempty R r.points hL hpoints
      (Finset.orderEmbOfFin_mem (starts r.points) rfl j)
  · rw [← hcover]
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨(starts r.points).orderIsoOfFin rfl j, hj⟩
    · rintro ⟨a, ha⟩
      exact ⟨((starts r.points).orderIsoOfFin rfl).symm a, by simpa [Marks.cells] using ha⟩
  · intro j k hjk
    apply hdis ((starts r.points).orderIsoOfFin rfl j) ((starts r.points).orderIsoOfFin rfl k)
    exact fun he ↦ hjk (((starts r.points).orderIsoOfFin rfl).injective he)
  · rw [hcount]
    omega
  · have hh : (r.cellCount : ℝ) ≤ (n * (size n ε - 1) + 1 : ℕ) := by exact_mod_cast hcardhi
    exact hh.trans_lt hupper
  · intro i j
    calc
      (v i).value (r.cells R j).support ≤ (v i).value R.support / size n ε := hvalues i j
      _ ≤ 3 * (n : ℝ) * ε * (v i).value R.support := by
        have hh := mul_le_mul_of_nonneg_left hinv (hpos i).le
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh

end CakeCuttingPsomas.RepairPartition
