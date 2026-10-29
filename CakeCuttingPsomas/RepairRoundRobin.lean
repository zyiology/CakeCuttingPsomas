module

public import CakeCuttingPsomas.RepairPartition
public import Mathlib.Data.List.MinMax

set_option linter.style.header false

/-! # Recorded round robin for Repair

Section 4, Algorithm `alg:repair`, line `rep:choose`, and the properties of
chosen cells in the proof of `lem:repair main`. Indices refer to paper cells,
which may contain several recorded intervals. Rounds and agents are zero based.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.RepairRoundRobin

open Finset

attribute [local instance] Classical.propDecidable

/-- First maximizer in increasing cell-index order. The default only makes
exhausted, invalid inputs total; availability excludes that branch below. -/
def favorite {m : ℕ} (f : Fin m → ℝ) (d : Fin m) (A : Finset (Fin m)) : Fin m :=
  ((A.sort (· ≤ ·)).argmax f).getD d

theorem favorite_spec {m : ℕ} (f : Fin m → ℝ) (d : Fin m)
    (A : Finset (Fin m)) (hA : A.Nonempty) :
    favorite f d A ∈ A ∧ ∀ c ∈ A, f c ≤ f (favorite f d A) := by
  have hn : (A.sort (· ≤ ·)).argmax f ≠ none := by
    intro h
    obtain ⟨a, ha⟩ := hA
    have : a ∈ A.sort (· ≤ ·) := by simpa using ha
    simp [List.argmax_eq_none.mp h] at this
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hn
  have hm : c ∈ (A.sort (· ≤ ·)).argmax f := by simp [hc]
  simp only [favorite, hc, Option.getD_some]
  exact ⟨by simpa using List.argmax_mem hm,
    fun c hc ↦ List.le_of_mem_argmax (by simpa using hc) hm⟩

/-- Ties go to the first maximizer in the sorted list of available indices. -/
theorem favorite_first {m : ℕ} (f : Fin m → ℝ) (d : Fin m)
    (A : Finset (Fin m)) (hA : A.Nonempty) (c : Fin m) (hc : c ∈ A)
    (hval : f (favorite f d A) ≤ f c) :
    (A.sort (· ≤ ·)).idxOf (favorite f d A) ≤ (A.sort (· ≤ ·)).idxOf c := by
  have hm : favorite f d A ∈ (A.sort (· ≤ ·)).argmax f := by
    cases h : (A.sort (· ≤ ·)).argmax f with
    | none =>
      have he := List.argmax_eq_none.mp h
      obtain ⟨a, ha⟩ := hA
      have : a ∈ A.sort (· ≤ ·) := by simpa using ha
      simp [he] at this
    | some a => simp [favorite, h]
  exact List.index_of_argmax hm (by simpa using hc) hval

/-- Available indices before turn `t`. Scores depend only on stored records.
Each successor removes exactly the cell chosen at the preceding turn. -/
def available {m : ℕ} (score : ℕ → Fin m → ℝ) (d : Fin m) : ℕ → Finset (Fin m)
  | 0 => univ
  | t + 1 => (available score d t).erase (favorite (score t) d (available score d t))

/-- Cell chosen at turn `t`. -/
def pick {m : ℕ} (score : ℕ → Fin m → ℝ) (d : Fin m) (t : ℕ) : Fin m :=
  favorite (score t) d (available score d t)

theorem available_succ {m : ℕ} (score : ℕ → Fin m → ℝ) (d : Fin m) (t : ℕ) :
    available score d (t + 1) = (available score d t).erase (pick score d t) := rfl

theorem available_antitone {m : ℕ} (score : ℕ → Fin m → ℝ) (d : Fin m) :
    Antitone (available score d) :=
  antitone_nat_of_succ_le fun _ ↦ erase_subset _ _

/-- Section 4, proof of `lem:repair main`: every turn before exhaustion has a
favorite available cell, and exactly one cell is removed per turn. -/
theorem available_card {m : ℕ} (score : ℕ → Fin m → ℝ) (d : Fin m)
    (t : ℕ) (ht : t ≤ m) : (available score d t).card = m - t := by
  induction t with
  | zero => simp [available]
  | succ t ih =>
    have hi := ih (by omega)
    have hA : (available score d t).Nonempty := card_pos.mp (by omega)
    rw [available_succ, pick, card_erase_of_mem (favorite_spec (score t) d _ hA).1, hi]
    omega

theorem pick_spec {m : ℕ} (score : ℕ → Fin m → ℝ) (d : Fin m)
    (t : ℕ) (ht : t < m) :
    pick score d t ∈ available score d t ∧
      ∀ c ∈ available score d t, score t c ≤ score t (pick score d t) := by
  apply favorite_spec
  apply card_pos.mp
  rw [available_card score d t (by omega)]
  omega

theorem later_pick_available {m : ℕ} (score : ℕ → Fin m → ℝ) (d : Fin m)
    {t u : ℕ} (htu : t ≤ u) (hu : u < m) :
    pick score d u ∈ available score d t :=
  available_antitone score d htu (pick_spec score d u hu).1

/-- Section 4, proof of `lem:repair main`: all chosen cell indices are distinct. -/
theorem pick_ne {m : ℕ} (score : ℕ → Fin m → ℝ) (d : Fin m)
    {t u : ℕ} (htu : t < u) (hu : u < m) : pick score d t ≠ pick score d u := by
  have h := later_pick_available score d (show t + 1 ≤ u by omega) hu
  rw [available_succ] at h
  exact (mem_erase.mp h).1.symm

/-- Fixed agent order, repeated in every round. -/
def agent {n : ℕ} (hn : 0 < n) (t : ℕ) : Fin n := ⟨t % n, Nat.mod_lt t hn⟩

/-- Recorded value of a whole paper cell to the agent acting at this turn. -/
def scores {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (t : ℕ) (c : Fin m) : ℝ :=
  s.supportValue (agent hn t) (cells c).support

theorem agent_turn {n : ℕ} (hn : 0 < n) (r : ℕ) (i : Fin n) :
    agent hn (r * n + i) = i := by
  apply Fin.ext
  simp [agent, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

theorem turn_lt {n : ℕ} (r : Fin (n - 1)) (i : Fin n) :
    r.val * n + i.val < n * (n - 1) := by
  have hi := i.isLt
  have hr := r.isLt
  nlinarith

/-- The chosen index at the specified round and agent. -/
def chosen {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (r : Fin (n - 1)) (i : Fin n) : Fin m :=
  pick (scores s cells hn) d (r.val * n + i.val)

theorem chosen_injective {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m) :
    Function.Injective (fun p : Fin (n - 1) × Fin n ↦ chosen s cells hn d p.1 p.2) := by
  intro ⟨r, i⟩ ⟨q, j⟩ he
  have ht : r.val * n + i.val = q.val * n + j.val := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · exact pick_ne (scores s cells hn) d h ((turn_lt q j).trans_le hcap) he
    · exact pick_ne (scores s cells hn) d h ((turn_lt r i).trans_le hcap) he.symm
  have hij : i = j := by
    have := congrArg (agent hn) ht
    simpa only [agent_turn] using this
  have hrq : r = q := by
    apply Fin.ext
    have := congrArg Fin.val hij
    nlinarith
  exact Prod.ext hrq hij

/-- Section 4, proof of `lem:repair main`: all picked paper cells are disjoint,
including different picks made by the same agent. -/
theorem chosen_disjoint {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (p q : Fin (n - 1) × Fin n) (hpq : p ≠ q) :
    Disjoint (cells (chosen s cells hn d p.1 p.2)).support
      (cells (chosen s cells hn d q.1 q.2)).support :=
  hd _ _ (fun h ↦ hpq (@chosen_injective n m s cells hn d hcap p q h))

/-- Section 4, the round-robin inequality in the higher-level preference proof.
With zero-based rounds, `q = r+1` expresses the paper's consecutive rounds. -/
theorem comparison {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (v : Fin n → Valuation) (hs : s.Correct v)
    (hrep : ∀ c, s.Represents (cells c).support)
    (r q : Fin (n - 1)) (hrq : r.val < q.val) (i j : Fin n) :
    (v i).value (cells (chosen s cells hn d q j)).support ≤
      (v i).value (cells (chosen s cells hn d r i)).support := by
  have htime : r.val * n + i.val ≤ q.val * n + j.val := by
    have := i.isLt
    nlinarith
  have hu := (turn_lt q j).trans_le hcap
  have ht := (turn_lt r i).trans_le hcap
  have h := (pick_spec (scores s cells hn) d _ ht).2 _
    (later_pick_available (scores s cells hn) d htime hu)
  simpa only [chosen, scores, agent_turn, RecordedState.supportValue_eq hs (hrep _)] using h

/-- Finite additivity on any subfamily of pairwise disjoint paper cells. -/
theorem value_cells {m : ℕ} (cells : Fin m → Piece)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (v : Valuation) (A : Finset (Fin m)) :
    v.value (⋃ c ∈ A, (cells c).support) = ∑ c ∈ A, v.value (cells c).support := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    have hm : MeasurableSet (⋃ c ∈ A, (cells c).support) :=
      A.finite_toSet.measurableSet_biUnion fun c _ ↦ (cells c).measurableSet_support
    have hsub : (⋃ c ∈ A, (cells c).support) ⊆ Set.Icc 0 1 := by
      intro x hx
      obtain ⟨c, _, hx⟩ := Set.mem_iUnion₂.mp hx
      exact (cells c).support_subset_unit hx
    have hdis : Disjoint (cells a).support (⋃ c ∈ A, (cells c).support) := by
      rw [Set.disjoint_iUnion_right]
      intro c
      rw [Set.disjoint_iUnion_right]
      intro hc
      exact hd a c (by intro h; exact ha (h ▸ hc))
    have hu : (⋃ c ∈ insert a A, (cells c).support) =
        (cells a).support ∪ ⋃ c ∈ A, (cells c).support := by ext; simp
    rw [hu, v.value_union (cells a).measurableSet_support hm
      (cells a).support_subset_unit hsub hdis, ih, sum_insert ha]

/-- Section 4, properties of the chosen cells: throughout round robin, available
cells retain at least half of every observer's original residue value. -/
theorem available_half {n m : ℕ} (hn : 2 ≤ n) (score : ℕ → Fin m → ℝ)
    (d : Fin m) (hcap : n * (n - 1) ≤ m) (cells : Fin m → Piece) (R : Piece)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (hcover : (⋃ c, (cells c).support) = R.support)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / (6 * (n : ℝ) ^ 3))
    (v : Valuation) (hsmall : ∀ c, v.value (cells c).support ≤ 3 * n * ε * v.value R.support)
    (t : ℕ) (ht : t ≤ n * (n - 1)) :
    v.value R.support / 2 ≤ ∑ c ∈ available score d t, v.value (cells c).support := by
  let A := available score d t
  let B := univ \ A
  have hcard : B.card ≤ n ^ 2 := by
    have hA := available_card score d t (ht.trans hcap)
    have hB := card_sdiff_add_card_eq_card (subset_univ A)
    simp only [card_univ, Fintype.card_fin] at hB
    dsimp [B, A]
    dsimp [A] at hB
    have : t ≤ n ^ 2 := by nlinarith [Nat.sub_le n 1]
    omega
  have hnonneg := v.value_nonneg R.measurableSet_support R.support_subset_unit
  have hb := sum_le_card_nsmul B (fun c ↦ v.value (cells c).support)
    (3 * n * ε * v.value R.support) (fun c _ ↦ hsmall c)
  rw [nsmul_eq_mul] at hb
  have hcR : (B.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hcard
  have hbound : ∑ c ∈ B, v.value (cells c).support ≤
      3 * (n : ℝ) ^ 3 * ε * v.value R.support := by
    have h := mul_le_mul_of_nonneg_right hcR
      (show 0 ≤ 3 * (n : ℝ) * ε * v.value R.support by positivity)
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he := (le_div_iff₀ (by positivity : 0 < 6 * (n : ℝ) ^ 3)).mp hεmax
  have hhalf : 3 * (n : ℝ) ^ 3 * ε * v.value R.support ≤ v.value R.support / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right he hnonneg]
  have hsum := sum_sdiff (f := fun c ↦ v.value (cells c).support) (subset_univ A)
  have hv := value_cells cells hd v univ
  simp only [mem_univ, Set.iUnion_true] at hv
  rw [hcover] at hv
  rw [← hv] at hsum
  dsimp [B] at hbound
  dsimp [A] at hsum hbound
  linarith

/-- Section 4, the last-pick estimate in the higher-level preference proof.
In fact every pick is strictly above the epsilon threshold for its chooser. -/
theorem pick_strict {n m : ℕ} (hn : 2 ≤ n) (s : RecordedState n)
    (cells : Fin m → Piece) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (R : Piece) (v : Fin n → Valuation) (hs : s.Correct v)
    (hrep : ∀ c, s.Represents (cells c).support)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (hcover : (⋃ c, (cells c).support) = R.support)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / (6 * (n : ℝ) ^ 3))
    (hcount : (m : ℝ) < 1 / (2 * ε))
    (hpos : ∀ i, 0 < (v i).value R.support)
    (hsmall : ∀ i c, (v i).value (cells c).support ≤ 3 * n * ε * (v i).value R.support)
    (t : ℕ) (ht : t < n * (n - 1)) :
    let hn0 : 0 < n := by omega
    let i := agent hn0 t
    ε * (v i).value R.support <
      (v i).value (cells (pick (scores s cells hn0) d t)).support := by
  dsimp only
  let hn0 : 0 < n := by omega
  let i := agent hn0 t
  let score := scores s cells hn0
  let A := available score d t
  have hh := available_half hn score d hcap cells R hd hcover ε hε hεmax
    (v i) (hsmall i) t ht.le
  have hmax := (pick_spec score d t (ht.trans_le hcap)).2
  have hcard : (A.card : ℝ) < 1 / (2 * ε) := by
    have hle : A.card ≤ m := by simpa using card_le_univ A
    exact (show (A.card : ℝ) ≤ m by exact_mod_cast hle).trans_lt hcount
  have hc : (A.card : ℝ) * ε < 1 / 2 := by
    have := (lt_div_iff₀ (by positivity : 0 < 2 * ε)).mp hcard
    linarith
  by_contra h
  have hp : (v i).value (cells (pick score d t)).support ≤ ε * (v i).value R.support :=
    le_of_not_gt h
  have hsum := sum_le_card_nsmul A (fun c ↦ (v i).value (cells c).support)
    (ε * (v i).value R.support) (fun c hc ↦ by
      have hv := hmax c hc
      have hv' : (v i).value (cells c).support ≤
          (v i).value (cells (pick score d t)).support := by
        simpa only [score, scores, RecordedState.supportValue_eq hs (hrep _)] using hv
      exact hv'.trans hp)
  rw [nsmul_eq_mul] at hsum
  have := mul_lt_mul_of_pos_right hc (hpos i)
  dsimp [A] at hsum
  nlinarith

/-- A concatenation of whole cells, retaining both cell order and each cell's
own interval order. -/
structure OrderedCells {m : ℕ} (cells : Fin m → Piece) (L : List (Fin m)) where
  piece : Piece
  intervals_eq : piece.intervals = L.flatMap (fun c ↦ (cells c).intervals)
  support_eq : piece.support = ⋃ c ∈ L, (cells c).support

/-- Concatenate a list of distinct cells; no sorting of geometric intervals. -/
def join {m : ℕ} (cells : Fin m → Piece)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support) :
    (L : List (Fin m)) → L.Nodup → OrderedCells cells L
  | [], _ => ⟨Piece.empty, rfl, by simp⟩
  | a :: L, hL =>
    let tail := join cells hd L (List.nodup_cons.mp hL).2
    have hdis : Disjoint (cells a).support tail.piece.support := by
      rw [tail.support_eq, Set.disjoint_iUnion_right]
      intro b
      rw [Set.disjoint_iUnion_right]
      intro hb
      exact hd a b (by intro h; exact (List.nodup_cons.mp hL).1 (h ▸ hb))
    ⟨(cells a).append tail.piece hdis,
      by simp only [Piece.append, List.flatMap_cons, tail.intervals_eq],
      by rw [Piece.support_append, tail.support_eq]; ext; simp⟩

theorem join_represents {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (hrep : ∀ c, s.Represents (cells c).support) (L : List (Fin m)) (hL : L.Nodup) :
    s.Represents (join cells hd L hL).piece.support := by
  rw [(join cells hd L hL).support_eq]
  induction L with
  | nil => simpa using s.represents_empty
  | cons a L ih =>
    have ht := ih (List.nodup_cons.mp hL).2
    have he : (⋃ c ∈ a :: L, (cells c).support) =
        (cells a).support ∪ ⋃ c ∈ L, (cells c).support := by ext; simp
    rw [he]
    apply (hrep a).union ht
    simp only [Set.disjoint_iUnion_right]
    intro b hb
    exact hd a b (by intro h; exact (List.nodup_cons.mp hL).1 (h ▸ hb))

theorem chosen_round_injective {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m) (i : Fin n) :
    Function.Injective (fun r ↦ chosen s cells hn d r i) := by
  intro r q h
  exact congrArg Prod.fst (@chosen_injective n m s cells hn d hcap (r, i) (q, i) h)

/-- Chosen cells concatenated in pick order, before appending the old bundle. -/
def bundle {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (i : Fin n) : Piece :=
  (join cells hd (List.ofFn (fun r ↦ chosen s cells hn d r i))
    (List.nodup_ofFn.mpr (chosen_round_injective s cells hn d hcap i))).piece

/-- The paper's concatenation order is retained exactly, for the levels proof. -/
theorem bundle_intervals {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support) (i : Fin n) :
    (bundle s cells hn d hcap hd i).intervals =
      (List.ofFn (fun r ↦ chosen s cells hn d r i)).flatMap (fun c ↦ (cells c).intervals) :=
  (join cells hd _ _).intervals_eq

theorem bundle_support {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support) (i : Fin n) :
    (bundle s cells hn d hcap hd i).support =
      ⋃ r, (cells (chosen s cells hn d r i)).support := by
  rw [bundle, (join cells hd _ _).support_eq]
  ext x
  simp

theorem bundle_subset {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (R : Piece) (hcover : (⋃ c, (cells c).support) = R.support) (i : Fin n) :
    (bundle s cells hn d hcap hd i).support ⊆ R.support := by
  rw [bundle_support, ← hcover]
  exact Set.iUnion_mono' fun r ↦ ⟨_, Set.Subset.rfl⟩

theorem bundle_disjoint {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (i j : Fin n) (hij : i ≠ j) :
    Disjoint (bundle s cells hn d hcap hd i).support
      (bundle s cells hn d hcap hd j).support := by
  simp only [bundle_support, Set.disjoint_iUnion_left, Set.disjoint_iUnion_right]
  intro r q
  apply hd
  intro h
  exact hij (congrArg Prod.snd (@chosen_injective n m s cells hn d hcap (q, i) (r, j) h))

/-- Section 4, properties of the chosen cells: each agent's entire chosen cake
has the paper's addition bound, from every observer's perspective. -/
theorem bundle_value_le {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (R : Piece) (ε : ℝ) (hε : 0 ≤ ε) (v : Valuation)
    (hsmall : ∀ c, v.value (cells c).support ≤ 3 * n * ε * v.value R.support)
    (j : Fin n) :
    v.value (bundle s cells hn d hcap hd j).support ≤
      3 * (n : ℝ) * (n - 1 : ℕ) * ε * v.value R.support ∧
    v.value (bundle s cells hn d hcap hd j).support ≤
      3 * (n : ℝ) ^ 2 * ε * v.value R.support := by
  let Q := fun r ↦ cells (chosen s cells hn d r j)
  have hQ : ∀ a b, a ≠ b → Disjoint (Q a).support (Q b).support := by
    intro a b hab
    apply hd
    exact fun h ↦ hab (chosen_round_injective s cells hn d hcap j h)
  have hv := value_cells Q hQ v univ
  simp only [mem_univ, Set.iUnion_true] at hv
  rw [bundle_support, hv]
  have hsum := sum_le_card_nsmul (univ : Finset (Fin (n - 1)))
    (fun r ↦ v.value (Q r).support) (3 * n * ε * v.value R.support)
    (fun r _ ↦ hsmall _)
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hfirst : ∑ r, v.value (Q r).support ≤
      3 * (n : ℝ) * (n - 1 : ℕ) * ε * v.value R.support := by nlinarith
  refine ⟨hfirst, hfirst.trans ?_⟩
  have hle : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hnonneg := v.value_nonneg R.measurableSet_support R.support_subset_unit
  have := mul_le_mul_of_nonneg_right hle
    (show 0 ≤ 3 * (n : ℝ) * ε * v.value R.support by positivity)
  nlinarith

/-- Section 4, proof of `lem:repair main`: any portion retained by Permute
inherits the chosen cake's value bound. No assertion about Permute is needed. -/
theorem retained_value_le {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (R : Piece) (ε : ℝ) (hε : 0 ≤ ε) (v : Valuation)
    (hsmall : ∀ c, v.value (cells c).support ≤ 3 * n * ε * v.value R.support)
    (j : Fin n) (Z : Piece) (hZ : Z.support ⊆ (bundle s cells hn d hcap hd j).support) :
    v.value Z.support ≤ 3 * (n : ℝ) ^ 2 * ε * v.value R.support :=
  (v.value_mono Z.measurableSet_support (bundle s cells hn d hcap hd j).measurableSet_support
    hZ (bundle s cells hn d hcap hd j).support_subset_unit).trans
      (bundle_value_le s cells hn d hcap hd R ε hε v hsmall j).2

/-- Round robin is internal computation on records and makes no new queries. -/
def select {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) : RWProtocol n (Fin (n - 1) → Fin n → Fin m) :=
  .done (chosen s cells hn d)

theorem select_runs {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (v : Fin n → Valuation) :
    (select s cells hn d).Runs v (chosen s cells hn d) 0 := .done _

/-- Guarantees needed by Section 4's subsequent levels argument. All assertions
refer to the actual recorded selection, rather than arbitrary maximizing picks. -/
structure Guarantees {n m : ℕ} (s : RecordedState n) (cells : Fin m → Piece)
    (hn : 0 < n) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (R : Piece) (ε : ℝ) (v : Fin n → Valuation) : Prop where
  available : ∀ t, t < n * (n - 1) →
    pick (scores s cells hn) d t ∈ RepairRoundRobin.available (scores s cells hn) d t
  distinct : Function.Injective
    (fun p : Fin (n - 1) × Fin n ↦ chosen s cells hn d p.1 p.2)
  comparison : ∀ (r q : Fin (n - 1)), r.val < q.val → ∀ i j,
    (v i).value (cells (chosen s cells hn d q j)).support ≤
      (v i).value (cells (chosen s cells hn d r i)).support
  remaining_half : ∀ t, t ≤ n * (n - 1) → ∀ i,
    (v i).value R.support / 2 ≤
      ∑ c ∈ RepairRoundRobin.available (scores s cells hn) d t, (v i).value (cells c).support
  pick_strict : ∀ (r : Fin (n - 1)) i,
    ε * (v i).value R.support < (v i).value (cells (chosen s cells hn d r i)).support
  bundle_subset : ∀ i, (bundle s cells hn d hcap hd i).support ⊆ R.support
  bundle_disjoint : ∀ i j, i ≠ j → Disjoint (bundle s cells hn d hcap hd i).support
    (bundle s cells hn d hcap hd j).support
  bundle_represents : ∀ i, s.Represents (bundle s cells hn d hcap hd i).support
  bundle_value_le : ∀ i j, (v i).value (bundle s cells hn d hcap hd j).support ≤
    3 * (n : ℝ) ^ 2 * ε * (v i).value R.support

/-- Section 4, Algorithm `alg:repair`, round robin and properties of the chosen
cells in `lem:repair main`. Only partition bounds and Repair's epsilon and
positive-residue assumptions are used; almost envy-freeness is not required. -/
theorem correct {n m : ℕ} (hn : 2 ≤ n) (s : RecordedState n)
    (cells : Fin m → Piece) (d : Fin m) (hcap : n * (n - 1) ≤ m)
    (R : Piece) (v : Fin n → Valuation) (hs : s.Correct v)
    (hrep : ∀ c, s.Represents (cells c).support)
    (hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support)
    (hcover : (⋃ c, (cells c).support) = R.support)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / (6 * (n : ℝ) ^ 3))
    (hcount : (m : ℝ) < 1 / (2 * ε)) (hpos : ∀ i, 0 < (v i).value R.support)
    (hsmall : ∀ i c, (v i).value (cells c).support ≤ 3 * n * ε * (v i).value R.support) :
    Guarantees s cells (by omega) d hcap hd R ε v := by
  let hn0 : 0 < n := by omega
  refine ⟨?_, chosen_injective s cells hn0 d hcap,
    comparison s cells hn0 d hcap v hs hrep, ?_, ?_,
    bundle_subset s cells hn0 d hcap hd R hcover,
    bundle_disjoint s cells hn0 d hcap hd, ?_, ?_⟩
  · intro t ht
    exact (pick_spec (scores s cells hn0) d t (ht.trans_le hcap)).1
  · intro t ht i
    exact available_half hn (scores s cells hn0) d hcap cells R hd hcover ε hε hεmax
      (v i) (hsmall i) t ht
  · intro r i
    have h := pick_strict hn s cells d hcap R v hs hrep hd hcover ε hε hεmax hcount
      hpos hsmall (r.val * n + i.val) (turn_lt r i)
    simpa only [agent_turn, chosen] using h
  · intro i
    exact join_represents s cells hd hrep _ _
  · intro i j
    exact (bundle_value_le s cells hn0 d hcap hd R ε hε.le (v i) (hsmall i) j).2

/-- Section 4, higher-level preference proof in `lem:repair main`: the strict
last-pick inequality, using the paper's round `n-1`. -/
theorem Guarantees.last_pick {n m : ℕ} {s : RecordedState n} {cells : Fin m → Piece}
    {hn : 0 < n} {d : Fin m} {hcap : n * (n - 1) ≤ m}
    {hd : ∀ a b, a ≠ b → Disjoint (cells a).support (cells b).support}
    {R : Piece} {ε : ℝ} {v : Fin n → Valuation}
    (h : Guarantees s cells hn d hcap hd R ε v) (hn2 : 2 ≤ n) (i : Fin n) :
    ε * (v i).value R.support <
      (v i).value (cells (chosen s cells hn d ⟨n - 2, by omega⟩ i)).support :=
  h.pick_strict _ i

/-- Section 4, the partition-to-round-robin milestone of `alg:repair`:
the existing recorded partition supplies every hypothesis, and selection adds
zero queries. Output records and all earlier representations are preserved. -/
theorem run_correct {n : ℕ} (hn : 2 ≤ n) (s : RecordedState n) (R : Piece)
    (ε : ℝ) (v : Fin n → Valuation) (hs : s.Correct v) (hR : s.Compatible R)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / (6 * (n : ℝ) ^ 3))
    (hpos : ∀ i, 0 < (v i).value R.support) :
    ∃ (r : RepairPartition.Marks n) (count : ℕ) (d : Fin r.cellCount)
      (hcap : n * (n - 1) ≤ r.cellCount)
      (hd : ∀ a b, a ≠ b → Disjoint (r.cells R a).support (r.cells R b).support),
      (RepairPartition.run s R ε).Runs v r count ∧
      count ≤ n * (RepairPartition.size n ε - 1) * (n + 1) ∧
      r.state.Correct v ∧ s.TraversalRefines r.state ∧
      (select r.state (r.cells R) (by omega) d).Runs v
        (chosen r.state (r.cells R) (by omega) d) 0 ∧
      Guarantees r.state (r.cells R) (by omega) d hcap hd R ε v := by
  obtain ⟨r, count, hrun, hcost, hrs, href, hrep, _, hcover, hd, hlo, _, hcount, _, hsmall⟩ :=
    RepairPartition.run_correct hn s R ε v hs hR hε hεmax hpos
  have hsize := (RepairPartition.size_bounds n hn ε hε hεmax).2.1
  have hcap : n * (n - 1) ≤ r.cellCount := by
    have : n - 1 ≤ n := Nat.sub_le n 1
    nlinarith
  let d : Fin r.cellCount := ⟨0, by nlinarith [Nat.sub_pos_of_lt (show 1 < n by omega)]⟩
  exact ⟨r, count, d, hcap, hd, hrun, hcost, hrs, href,
    select_runs r.state (r.cells R) (by omega) d v,
    correct hn r.state (r.cells R) d hcap R v hrs hrep hd hcover ε hε hεmax hcount hpos hsmall⟩

end CakeCuttingPsomas.RepairRoundRobin
