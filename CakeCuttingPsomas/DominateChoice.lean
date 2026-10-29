module

public import CakeCuttingPsomas.Core
public import Mathlib.Data.List.Chain
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push

set_option linter.style.header false

/-! # The choice lemma for Dominate

Section 3's `lem:alpha pi exist for dominate` in `paper/main.tex`.
The choices here are mathematical witnesses; implementing the search using
inherited records is a separate protocol construction.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas

namespace DominateChoice

/-- The finite geometric scale used in Section 3's choice step. -/
def scale (n t : ℕ) : ℝ := ((4 * (n : ℝ) ^ 2)⁻¹) ^ t

/-- An edge of the paper's non-domination graph. -/
def Edge {n : ℕ} {C : Piece} (X : Allocation n C) (v : Fin n → Valuation)
    (i j : Fin n) : Prop := i ≠ j ∧ ¬ X.Dominates v i j

/-- The normalized envy gap `gᵢⱼ` from the proof of the choice lemma. -/
def gap {n : ℕ} {R : Piece} (Y : Allocation n R) (v : Fin n → Valuation)
    (i j : Fin n) : ℝ :=
  ((v i).value (Y.bundle i).support - (v i).value (Y.bundle j).support) /
    (v i).value Y.residue

/-- The paper's (S1)--(S3), with the exponent retained as a finite choice. -/
structure Spec {n : ℕ} {C R : Piece} (X : Allocation n C) (Y : Allocation n R)
    (v : Fin n → Valuation) (t : ℕ) (i j : Fin n) (π : Equiv.Perm (Fin n)) : Prop where
  exponent_lower : 2 ≤ t
  exponent_upper : t ≤ n + 1
  distinct : i ≠ j
  not_dominates : ¬ X.Dominates v i j
  small_loss : ∀ k, (v k).value (Y.bundle k).support -
    scale n t * (v k).value Y.residue ≤ (v k).value (Y.bundle (π k)).support
  large_gap : (v i).value (Y.bundle (π j)).support ≤
    (v i).value (Y.bundle i).support -
      4 * (n : ℝ) ^ 2 * scale n t * (v i).value Y.residue

/-- Any reachable pair admits a simple directed path, represented by its vertices.
This supplies the path used in the second case of Section 3's choice lemma. -/
theorem simple_path {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    ∃ l : List α, (a :: l).Nodup ∧ (a :: l).IsChain r ∧
      (a :: l).getLast (List.cons_ne_nil _ _) = b := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], by simp, by simp, rfl⟩
  | @head a c hac h ih =>
    obtain ⟨l, hnd, hch, hlast⟩ := ih
    by_cases ha : a ∈ c :: l
    · obtain ⟨p, q, hpq⟩ := List.mem_iff_append.mp ha
      refine ⟨q, ?_, ?_, ?_⟩
      · rw [hpq] at hnd
        exact (List.nodup_append.mp hnd).2.1
      · rw [hpq] at hch
        exact hch.right_of_append
      · simpa only [hpq, List.getLast_append_of_right_ne_nil _ _
          (List.cons_ne_nil _ _)] using hlast
    · refine ⟨c :: l, List.nodup_cons.mpr ⟨ha, hnd⟩,
        List.isChain_cons_cons.mpr ⟨hac, hch⟩, ?_⟩
      simpa using hlast

/-- Cycling a simple path sends its last vertex to its first; every other
non-fixed image follows an edge of the path. -/
theorem path_permutation {α : Type*} [DecidableEq α] {r : α → α → Prop}
    (a : α) (l : List α) (hnd : (a :: l).Nodup) (hch : (a :: l).IsChain r) :
    let π := (a :: l).formPerm
    π ((a :: l).getLast (List.cons_ne_nil _ _)) = a ∧
      ∀ i, i ≠ (a :: l).getLast (List.cons_ne_nil _ _) → π i = i ∨ r i (π i) := by
  dsimp only
  refine ⟨List.formPerm_apply_getLast _ _, ?_⟩
  intro i hi
  by_cases hm : i ∈ a :: l
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
    have hnext : k + 1 < (a :: l).length := by
      by_contra hn
      have heq : k = l.length := by simp only [List.length_cons] at hk hn; omega
      subst k
      exact hi (List.getElem_cons_length rfl)
    right
    rw [List.formPerm_apply_lt_getElem _ hnd k hnext]
    exact List.isChain_iff_getElem.mp hch k hnext
  · exact Or.inl (List.formPerm_apply_of_notMem hm)

/-- No dominated group in an envy-free allocation forces positive residue value
for every agent (`lem:alpha pi exist for dominate`, first paragraph). -/
theorem residue_pos {n : ℕ} {C : Piece} (A : Allocation n C) (hn : 2 ≤ n)
    (v : Fin n → Valuation) (hef : A.EnvyFree v)
    (hgroup : ∀ E : Set (Fin n), ¬ A.DominatedGroup v E) :
    ∀ i, 0 < (v i).value A.residue := by
  intro i
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hnonneg := (v i).value_nonneg A.measurableSet_residue A.residue_subset_unit
  by_contra hpos
  have hz : (v i).value A.residue = 0 := by linarith
  apply hgroup {j | j ≠ i}
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨j, hj⟩
  · intro heq
    have hi : i ∈ ({j | j ≠ i} : Set (Fin n)) := heq.symm ▸ Set.mem_univ i
    exact hi rfl
  · intro k hk j _
    have hki : k = i := by simpa using hk
    subst k
    simpa [Allocation.Dominates, hz] using hef i j

/-- A graph with no nonempty proper set closed under outgoing edges is strongly
connected. We use the reachable set as the closed set, avoiding an SCC quotient. -/
theorem reachable_of_cut {α : Type*} {r : α → α → Prop}
    (hcut : ∀ S : Set α, S.Nonempty → S ≠ Set.univ →
      ∃ i ∈ S, ∃ j ∉ S, r i j) (a b : α) : Relation.ReflTransGen r a b := by
  by_contra hab
  let S : Set α := {j | Relation.ReflTransGen r a j}
  have hne : S.Nonempty := ⟨a, .refl⟩
  have hproper : S ≠ Set.univ := by
    intro heq
    have hb : b ∈ S := heq.symm ▸ Set.mem_univ b
    exact hab hb
  obtain ⟨i, hi, j, hj, hij⟩ := hcut S hne hproper
  exact hj (hi.tail hij)

/-- The non-domination graph is strongly connected if there is no dominated
group (`lem:alpha pi exist for dominate`, graph argument). -/
theorem strongly_connected {n : ℕ} {C : Piece} (X : Allocation n C)
    (v : Fin n → Valuation) (hgroup : ∀ E : Set (Fin n), ¬ X.DominatedGroup v E)
    (a b : Fin n) : Relation.ReflTransGen (Edge X v) a b := by
  classical
  apply reachable_of_cut _ a b
  intro S hS hproper
  by_contra hcross
  push Not at hcross
  apply hgroup Sᶜ
  refine ⟨?_, ?_, ?_⟩
  · exact Set.nonempty_compl.mpr hproper
  · intro heq
    obtain ⟨i, hi⟩ := hS
    have : i ∈ Sᶜ := heq.symm ▸ Set.mem_univ i
    exact this hi
  · intro i hi j hj
    have hiS : i ∈ S := by simpa using hi
    by_contra hdom
    exact hcross i hiS j hj ⟨fun heq ↦ hj (heq ▸ hiS), hdom⟩

/-- Finite additivity of the allocated bundles and the exact residue. -/
theorem value_partition {n : ℕ} {R : Piece} (Y : Allocation n R) (v : Valuation) :
    (∑ j, v.value (Y.bundle j).support) + v.value Y.residue = v.value R.support := by
  have ha : v.value Y.allocated = ∑ j, v.value (Y.bundle j).support :=
    MeasureTheory.integral_iUnion_fintype
      (fun j ↦ (Y.bundle j).measurableSet_support) Y.disjoint
      (fun j ↦ v.integrableOn (Y.bundle j).support_subset_unit)
  have hu : Y.allocated ∪ Y.residue = R.support := by
    exact Set.union_sdiff_cancel Y.allocated_subset
  rw [← ha, ← v.value_union Y.measurableSet_allocated Y.measurableSet_residue
    Y.allocated_subset_unit Y.residue_subset_unit Y.disjoint_allocated_residue, hu]

@[simp]
theorem gap_self {n : ℕ} {R : Piece} (Y : Allocation n R) (v : Fin n → Valuation)
    (i : Fin n) : gap Y v i i = 0 := by simp [gap]

theorem gap_nonneg {n : ℕ} {R : Piece} (Y : Allocation n R) (v : Fin n → Valuation)
    (hef : Y.EnvyFree v) (i j : Fin n) : 0 ≤ gap Y v i j :=
  div_nonneg (sub_nonneg.mpr (hef i j))
    ((v i).value_nonneg Y.measurableSet_residue Y.residue_subset_unit)

/-- The cutter's normalized gaps sum to one (`lem:alpha pi exist for dominate`). -/
theorem gap_row_sum {n : ℕ} {R : Piece} (Y : Allocation n R) (v : Fin n → Valuation)
    (hn : 2 ≤ n) (c : Fin n) (hpos : 0 < (v c).value Y.residue)
    (hshare : (v c).value (Y.bundle c).support = (v c).value R.support / n) :
    ∑ j, gap Y v c j = 1 := by
  have hp := value_partition Y (v c)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hshare' : (n : ℝ) * (v c).value (Y.bundle c).support =
      (v c).value R.support := by rw [hshare]; field_simp
  simp only [gap, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply (div_eq_one_iff_eq (ne_of_gt hpos)).mpr
  linarith

/-- Among `n-1` geometric bands, one is empty: two of the `n` column entries
are excluded, one above every band and one below every band. This is the finite
counting step of `lem:alpha pi exist for dominate`. -/
theorem empty_band {n : ℕ} (hn : 3 ≤ n) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (f : Fin n → ℝ) (c j : Fin n) (hc : q < f c) (hj : f j = 0) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ n - 1 ∧ ∀ i, f i ≤ q ^ (t + 1) ∨ q ^ t < f i := by
  classical
  by_contra h
  have hex : ∀ k : Fin (n - 1), ∃ i : Fin n,
      q ^ (k.val + 2) < f i ∧ f i ≤ q ^ (k.val + 1) := by
    intro k
    have ht : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ n - 1 := by omega
    have hh : ¬ ∀ i, f i ≤ q ^ (k.val + 1 + 1) ∨ q ^ (k.val + 1) < f i := by
      intro hall
      exact h ⟨k.val + 1, ht.1, ht.2, hall⟩
    push Not at hh
    obtain ⟨i, hi1, hi2⟩ := hh
    exact ⟨i, by simpa [Nat.add_assoc] using hi1, hi2⟩
  choose w hw using hex
  have hanti : Antitone (fun k : ℕ ↦ q ^ k) := by
    intro k l hkl
    exact pow_le_pow_of_le_one hq0.le hq1.le hkl
  have hw_inj : Function.Injective w := by
    intro k l hkl
    have hnot : ∀ a b : Fin (n - 1), a.val < b.val → w a ≠ w b := by
      intro a b hab heq
      have hp := hanti (show a.val + 2 ≤ b.val + 1 by omega)
      have h1 := (hw a).1
      have h2 := (hw b).2
      rw [heq] at h1
      linarith
    exact Fin.ext (by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hnot k l hlt hkl
      · exact hnot l k hgt hkl.symm)
  have hnotc : ∀ k, w k ≠ c := by
    intro k heq
    have hp := hanti (show 1 ≤ k.val + 1 by omega)
    have hu := (hw k).2
    rw [heq] at hu
    simp only [pow_one] at hp
    linarith
  have hnotj : ∀ k, w k ≠ j := by
    intro k heq
    have hl := (hw k).1
    rw [heq, hj] at hl
    exact (not_lt_of_ge (pow_nonneg hq0.le _)) hl
  have hcj : c ≠ j := by intro heq; rw [heq, hj] at hc; linarith
  let s := Finset.univ.image w
  have hcs : c ∉ s := by simpa [s, Finset.mem_image] using hnotc
  have hjs : j ∉ s := by simpa [s, Finset.mem_image] using hnotj
  have hcard : s.card = n - 1 := by
    dsimp only [s]
    rw [Finset.card_image_of_injective _ hw_inj]
    simp
  have hle := Finset.card_le_card (Finset.subset_univ (insert c (insert j s)))
  rw [Finset.card_insert_of_notMem (by simp [hcj, hcs]),
    Finset.card_insert_of_notMem hjs, hcard] at hle
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- The cutter's row has an off-diagonal entry at least `1/(n-1)`, as used in
the second case of `lem:alpha pi exist for dominate`. -/
theorem row_average {n : ℕ} (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ)
    (hdiag : ∀ i, g i i = 0) (c : Fin n) (hsum : ∑ j, g c j = 1) :
    ∃ j, j ≠ c ∧ 1 / ((n : ℝ) - 1) ≤ g c j := by
  classical
  let s := Finset.univ.erase c
  have hcard : s.card = n - 1 := by simp [s]
  have hne : s.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hsum_s : ∑ j ∈ s, g c j = 1 := by
    have hh := Finset.sum_erase_add Finset.univ (fun j ↦ g c j) (Finset.mem_univ c)
    simpa only [hdiag c, add_zero, hsum] using hh
  have hd : 0 < (n : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have havg : (∑ _j ∈ s, 1 / ((n : ℝ) - 1)) ≤ ∑ j ∈ s, g c j := by
    rw [hsum_s, Finset.sum_const, nsmul_eq_mul, hcard,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    exact le_of_eq (mul_one_div_cancel (ne_of_gt hd))
  obtain ⟨j, hj, hle⟩ := Finset.exists_le_of_sum_le hne havg
  exact ⟨j, (Finset.mem_erase.mp hj).1, hle⟩

/-- The finite matrix argument of `lem:alpha pi exist for dominate`, separated
from valuations. `q` is the inverse of `B = 4n²`. -/
theorem matrix_choice {n : ℕ} (hn : 3 ≤ n) (q B : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hBq : B * q = 1) (hnq : ((n : ℝ) - 1) * q < 1)
    (g : Fin n → Fin n → ℝ) (hdiag : ∀ i, g i i = 0)
    (r : Fin n → Fin n → Prop)
    (hconn : ∀ a b, Relation.ReflTransGen r a b)
    (c : Fin n) (hsum : ∑ j, g c j = 1) :
    ∃ t : ℕ, ∃ i j : Fin n, ∃ π : Equiv.Perm (Fin n),
      2 ≤ t ∧ t ≤ n + 1 ∧ r i j ∧
      (∀ k, g k (π k) ≤ q ^ t) ∧ B * q ^ t ≤ g i (π j) := by
  classical
  have hstep (t : ℕ) : B * q ^ (t + 1) = q ^ t := by
    rw [pow_succ]
    calc B * (q ^ t * q) = (B * q) * q ^ t := by ring
         _ = q ^ t := by rw [hBq, one_mul]
  by_cases hbig : ∃ i j, r i j ∧ q ^ n ≤ g i j
  · obtain ⟨i, j, hij, hg⟩ := hbig
    exact ⟨n + 1, i, j, Equiv.refl _, by omega, le_rfl, hij,
      fun k ↦ by simpa [hdiag k] using (pow_nonneg hq0.le (n + 1)),
      by simpa only [Equiv.refl_apply, hstep] using hg⟩
  · have hsmall : ∀ i j, r i j → g i j < q ^ n := by
      intro i j hij
      exact lt_of_not_ge (fun hg ↦ hbig ⟨i, j, hij, hg⟩)
    obtain ⟨jhat, _, hjavg⟩ := row_average (by omega : 2 ≤ n) g hdiag c hsum
    have hjhat : q < g c jhat := by
      have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have hden : 0 < (n : ℝ) - 1 := by linarith
      have havg : q < 1 / ((n : ℝ) - 1) := (lt_div_iff₀ hden).mpr (by nlinarith)
      exact havg.trans_le hjavg
    obtain ⟨s, hs1, hsn, hband⟩ := empty_band hn q hq0 hq1 (fun i ↦ g i jhat)
      c jhat hjhat (hdiag jhat)
    let H : Set (Fin n) := {i | q ^ s < g i jhat}
    have hanti : Antitone (fun k : ℕ ↦ q ^ k) :=
      fun _ _ h ↦ pow_le_pow_of_le_one hq0.le hq1.le h
    have hcH : c ∈ H := by
      have hp := hanti hs1
      simp only [pow_one] at hp
      exact lt_of_le_of_lt hp hjhat
    have hjH : jhat ∉ H := by
      change ¬ q ^ s < g jhat jhat
      rw [hdiag]
      exact not_lt_of_ge (pow_nonneg hq0.le s)
    have hcross : ∃ i ∈ H, ∃ j ∉ H, r i j := by
      by_contra hh
      push Not at hh
      have hreach : ∀ {b}, Relation.ReflTransGen r c b → b ∈ H := by
        intro b hb
        induction hb with
        | refl => exact hcH
        | @tail b d hp hbd ih =>
          by_contra hd
          exact hh b ih d hd hbd
      exact hjH (hreach (hconn c jhat))
    obtain ⟨i, hi, j, hj, hij⟩ := hcross
    have hjlow : g j jhat ≤ q ^ (s + 1) :=
      (hband j).resolve_right hj
    obtain ⟨l, hnd, hch, hlast⟩ := simple_path (hconn jhat j)
    let π := (jhat :: l).formPerm
    have hperm := path_permutation jhat l hnd hch
    have hπj : π j = jhat := by rw [← hlast]; exact hperm.1
    refine ⟨s + 1, i, j, π, by omega, by omega, hij, ?_, ?_⟩
    · intro k
      by_cases hkj : k = j
      · subst k
        simpa only [hπj] using hjlow
      · have hkLast : k ≠ (jhat :: l).getLast (List.cons_ne_nil _ _) := by
          simpa only [hlast] using hkj
        rcases hperm.2 k hkLast with hfix | hedge
        · change g k ((jhat :: l).formPerm k) ≤ _
          rw [hfix, hdiag]
          exact pow_nonneg hq0.le _
        · exact (hsmall k (π k) hedge).le.trans (hanti (by omega))
    · rw [hπj, hstep]
      exact le_of_lt hi

/-- Combine a same-agent allocation of the represented residue with the old
allocation, using the existing recursive adapter on the full agent set. -/
def combined {n : ℕ} {C R : Piece} (X : Allocation n C) (Y : Allocation n R)
    (hR : R.support = X.residue) : Allocation n C :=
  X.combineRecursive Y (Equiv.Set.univ (Fin n)).symm hR

theorem combined_bundle_value {n : ℕ} {C R : Piece} (X : Allocation n C)
    (Y : Allocation n R) (hR : R.support = X.residue) (v : Valuation) (i : Fin n) :
    v.value ((combined X Y hR).bundle i).support =
      v.value (X.bundle i).support + v.value (Y.bundle i).support := by
  rw [combined, Allocation.combineRecursive, Allocation.value_bundle_combine]
  simp [Allocation.extendTo, Equiv.Set.univ]

theorem combined_residue {n : ℕ} {C R : Piece} (X : Allocation n C)
    (Y : Allocation n R) (hR : R.support = X.residue) :
    (combined X Y hR).residue = Y.residue := by
  rw [combined, Allocation.combineRecursive, Allocation.residue_combine,
    Allocation.allocated_extendTo, ← hR]
  rfl

/-- The hypotheses needed for the choice lemma follow from its combined-allocation
test: envy-freeness, positive new residue, and strongly connected old graph. -/
theorem preliminaries {n : ℕ} {C R : Piece} (X : Allocation n C)
    (Y : Allocation n R) (hn : 3 ≤ n) (hR : R.support = X.residue)
    (v : Fin n → Valuation) (hX : X.EnvyFree v) (hY : Y.EnvyFree v)
    (hgroup : ∀ E : Set (Fin n), ¬ (combined X Y hR).DominatedGroup v E) :
    (∀ i, 0 < (v i).value Y.residue) ∧
      (∀ a b, Relation.ReflTransGen (Edge X v) a b) := by
  have hef : (combined X Y hR).EnvyFree v := by
    intro i j
    rw [combined_bundle_value, combined_bundle_value]
    exact add_le_add (hX i j) (hY i j)
  constructor
  · simpa only [combined_residue] using residue_pos (combined X Y hR) (by omega) v hef hgroup
  · apply strongly_connected X v
    intro E hE
    apply hgroup E
    refine ⟨hE.1, hE.2.1, ?_⟩
    intro i hi j hj
    exact Allocation.dominates_combine X
      (Y.extendTo (Equiv.Set.univ (Fin n)).symm (hR.subset.trans X.residue_subset))
      (X.allocated_extendTo_subset_residue Y (Equiv.Set.univ (Fin n)).symm hR)
      v i j (hE.2.2 i hi j hj)

/-- Section 3's `lem:alpha pi exist for dominate`: after an envy-free Core
allocation with the cutter's exact share, failure of the dominated-group test
implies positive residue values and choices satisfying exactly (S1)--(S3).
The hypotheses are the mathematical guarantees of `CoreProtocol.Correct`;
no normalization or positive input-value assumption is needed. -/
theorem exists_choice {n : ℕ} {C R : Piece} (X : Allocation n C)
    (Y : Allocation n R) (hn : 3 ≤ n) (hR : R.support = X.residue)
    (v : Fin n → Valuation) (c : Fin n) (hX : X.EnvyFree v) (hY : Y.EnvyFree v)
    (hshare : (v c).value (Y.bundle c).support = (v c).value R.support / n)
    (hgroup : ∀ E : Set (Fin n), ¬ (combined X Y hR).DominatedGroup v E) :
    (∀ i, 0 < (v i).value Y.residue) ∧
      ∃ t : ℕ, ∃ i j : Fin n, ∃ π : Equiv.Perm (Fin n), Spec X Y v t i j π := by
  obtain ⟨hpos, hconn⟩ := preliminaries X Y hn hR v hX hY hgroup
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : 0 < 4 * (n : ℝ) ^ 2 := by positivity
  have hq0 : 0 < (4 * (n : ℝ) ^ 2)⁻¹ := inv_pos.mpr hB
  have hq1 : (4 * (n : ℝ) ^ 2)⁻¹ < 1 := by
    rw [inv_eq_one_div]
    apply (div_lt_one hB).mpr
    nlinarith
  have hnq : ((n : ℝ) - 1) * (4 * (n : ℝ) ^ 2)⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    apply (div_lt_one hB).mpr
    nlinarith
  obtain ⟨t, i, j, π, ht1, ht2, hij, hsmall, hlarge⟩ :=
    matrix_choice hn (4 * (n : ℝ) ^ 2)⁻¹ (4 * (n : ℝ) ^ 2)
      hq0 hq1 (mul_inv_cancel₀ (ne_of_gt hB)) hnq
      (gap Y v) (gap_self Y v) (Edge X v) hconn c
      (gap_row_sum Y v (by omega) c (hpos c) hshare)
  refine ⟨hpos, t, i, j, π, ht1, ht2, hij.1, hij.2, ?_, ?_⟩
  · intro k
    have hk := (div_le_iff₀ (hpos k)).mp (hsmall k)
    change (v k).value (Y.bundle k).support -
      (v k).value (Y.bundle (π k)).support ≤ scale n t * (v k).value Y.residue at hk
    linarith
  · have hi := (le_div_iff₀ (hpos i)).mp hlarge
    change (4 * (n : ℝ) ^ 2 * scale n t) * (v i).value Y.residue ≤
      (v i).value (Y.bundle i).support - (v i).value (Y.bundle (π j)).support at hi
    linarith

/-- Section 3, proof of `lem: dominate`, validity of the Repair call:
bundle `i` is the old bundle `Xᵢ` followed by `Y_{π(i)}`. -/
def permutedCombined {n : ℕ} {C R : Piece} (X : Allocation n C)
    (Y : Allocation n R) (hR : R.support = X.residue) (π : Equiv.Perm (Fin n)) :
    Allocation n C :=
  X.combineRecursive Y (π.symm.trans (Equiv.Set.univ (Fin n)).symm) hR

theorem permutedCombined_bundle_support {n : ℕ} {C R : Piece} (X : Allocation n C)
    (Y : Allocation n R) (hR : R.support = X.residue) (π : Equiv.Perm (Fin n))
    (i : Fin n) :
    ((permutedCombined X Y hR π).bundle i).support =
      (X.bundle i).support ∪ (Y.bundle (π i)).support := by
  simp [permutedCombined, Allocation.combineRecursive, Allocation.extendTo, Equiv.Set.univ]

theorem permutedCombined_bundle_value {n : ℕ} {C R : Piece} (X : Allocation n C)
    (Y : Allocation n R) (hR : R.support = X.residue) (π : Equiv.Perm (Fin n))
    (v : Valuation) (i : Fin n) :
    v.value ((permutedCombined X Y hR π).bundle i).support =
      v.value (X.bundle i).support + v.value (Y.bundle (π i)).support := by
  rw [permutedCombined, Allocation.combineRecursive, Allocation.value_bundle_combine]
  simp [Allocation.extendTo, Equiv.Set.univ]

theorem permutedCombined_residue {n : ℕ} {C R : Piece} (X : Allocation n C)
    (Y : Allocation n R) (hR : R.support = X.residue) (π : Equiv.Perm (Fin n)) :
    (permutedCombined X Y hR π).residue = Y.residue := by
  rw [permutedCombined, Allocation.combineRecursive, Allocation.residue_combine,
    Allocation.allocated_extendTo, ← hR]
  rfl

/-- Section 3, proof of `lem: dominate`, validity of the Repair call:
every allowed scale is positive and strictly below Repair's epsilon bound. -/
theorem scale_repair_bounds {n t : ℕ} (hn : 3 ≤ n) (ht : 2 ≤ t) :
    0 < scale n t ∧ scale n t ≤ ((4 * (n : ℝ) ^ 2)⁻¹) ^ 2 ∧
      ((4 * (n : ℝ) ^ 2)⁻¹) ^ 2 < 1 / (6 * (n : ℝ) ^ 3) := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hbase : 0 < 4 * (n : ℝ) ^ 2 := by positivity
  have hq : (4 * (n : ℝ) ^ 2)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one hbase]
    nlinarith
  refine ⟨by unfold scale; positivity,
    pow_le_pow_of_le_one (le_of_lt (inv_pos.mpr hbase)) hq ht, ?_⟩
  rw [inv_pow, inv_eq_one_div]
  apply (div_lt_div_iff₀ (by positivity : 0 < (4 * (n : ℝ) ^ 2) ^ 2)
    (by positivity : 0 < 6 * (n : ℝ) ^ 3)).mpr
  have hmul : 6 * (n : ℝ) ^ 3 < (16 * (n : ℝ)) * (n : ℝ) ^ 3 :=
    mul_lt_mul_of_pos_right (by linarith) (by positivity)
  nlinarith

/-- Section 3, proof of `lem: dominate`, validity of the Repair call:
envy-freeness of `X` and `Y` and (S2) imply almost envy-freeness of `D`. -/
theorem Spec.permutedCombined_almost_envyFree {n t : ℕ} {C R : Piece}
    {X : Allocation n C} {Y : Allocation n R} {v : Fin n → Valuation}
    {a b : Fin n} {π : Equiv.Perm (Fin n)} (h : Spec X Y v t a b π)
    (hR : R.support = X.residue) (hX : X.EnvyFree v) (hY : Y.EnvyFree v) :
    ∀ i j, (v i).value ((permutedCombined X Y hR π).bundle j).support -
      scale n t * (v i).value (permutedCombined X Y hR π).residue ≤
        (v i).value ((permutedCombined X Y hR π).bundle i).support := by
  intro i j
  rw [permutedCombined_bundle_value, permutedCombined_bundle_value, permutedCombined_residue]
  have hx := hX i j
  have hy := hY i (π j)
  have hs := h.small_loss i
  linarith

/-- Section 3, proof of `lem: dominate`, validity of the Repair call:
the choice specification supplies all mathematical preconditions of Repair.
Positive residue values are supplied by `exists_choice`; record preparation
and the protocol execution are separate obligations. -/
theorem Spec.repair_preconditions {n t : ℕ} {C R : Piece}
    {X : Allocation n C} {Y : Allocation n R} {v : Fin n → Valuation}
    {a b : Fin n} {π : Equiv.Perm (Fin n)} (h : Spec X Y v t a b π)
    (hn : 3 ≤ n) (hR : R.support = X.residue)
    (hX : X.EnvyFree v) (hY : Y.EnvyFree v)
    (hpos : ∀ i, 0 < (v i).value Y.residue) :
    0 < scale n t ∧ scale n t ≤ 1 / (6 * (n : ℝ) ^ 3) ∧
      (∀ i, 0 < (v i).value (permutedCombined X Y hR π).residue) ∧
      (∀ i j, (v i).value ((permutedCombined X Y hR π).bundle j).support -
        scale n t * (v i).value (permutedCombined X Y hR π).residue ≤
          (v i).value ((permutedCombined X Y hR π).bundle i).support) := by
  obtain ⟨hαpos, hαle, hαlt⟩ := scale_repair_bounds hn h.exponent_lower
  refine ⟨hαpos, hαle.trans hαlt.le, ?_, h.permutedCombined_almost_envyFree hR hX hY⟩
  simpa only [permutedCombined_residue] using hpos

end DominateChoice

end CakeCuttingPsomas
