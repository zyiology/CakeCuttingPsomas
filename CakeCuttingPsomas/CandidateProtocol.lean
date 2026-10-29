module

public import CakeCuttingPsomas.Candidate
public import CakeCuttingPsomas.SuffixProtocol
public import CakeCuttingPsomas.RecordedPreparation
public import Mathlib.Data.Nat.Choose.Basic

set_option linter.style.header false

/-! # Constructing one Section 5 candidate

Algorithm `alg:permute`, for one fixed pair of orders. All targets are computed
from inherited records; valuations occur only in the correctness theorems.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.CandidateConstruction

attribute [local instance] Classical.propDecidable

/-- State and position-indexed bundles, including unprocessed empty entries. -/
structure Result (n : ℕ) where
  state : RecordedState n
  bundles : Fin n → Piece

/-- Restore agent labels to a candidate family. Disjoint input labels are
retained even when multiple input pieces or output suffixes are empty. -/
def Result.allocation {n : ℕ} {C : Piece} (r : Result n)
    (agents pieces : Equiv.Perm (Fin n)) (inputs : Fin n → Piece)
    (hS : ∀ j, (r.bundles j).IsSuffix (inputs (pieces j)))
    (hd : ∀ i j, i ≠ j → Disjoint (inputs i).support (inputs j).support)
    (hcover : (⋃ j, (inputs j).support) = C.support) : Allocation n C where
  bundle i := r.bundles (agents.symm i)
  contained i := by
    obtain ⟨a, _, he⟩ := hS (agents.symm i)
    rw [he]
    apply (Piece.suffix_subset _ _).trans
    rw [← hcover]
    exact Set.subset_iUnion (fun j ↦ (inputs j).support) (pieces (agents.symm i))
  disjoint i j hij := by
    obtain ⟨a, _, hi⟩ := hS (agents.symm i)
    obtain ⟨b, _, hj⟩ := hS (agents.symm j)
    rw [hi, hj]
    exact (hd _ _ (fun he ↦ hij (agents.symm.injective (pieces.injective he)))).mono
      (Piece.suffix_subset _ _) (Piece.suffix_subset _ _)

/-- Apply the earlier agents' caps to one input piece, in their given order. -/
def trim {n : ℕ} : List (Fin n × Piece) → RecordedState n → Piece →
    RWProtocol n (Piece × RecordedState n)
  | [], s, P => .done (P, s)
  | (i, B) :: caps, s, P =>
    (s.capTrim i P (s.supportValue i B.support)).bind fun (a, s') ↦
      trim caps s' (P.suffixAt a)

/-- Section 5, `permute:trim`: a whole inner loop realizes the mathematical
cap sequence and preserves traversals, with one prefix cut per earlier agent. -/
theorem trim_correct {n : ℕ} (caps : List (Fin n × Piece)) (s : RecordedState n)
    (P : Piece) (v : Fin n → Valuation) (hs : s.Correct v)
    (hP : ∃ Q, s.Compatible Q ∧ P.SameTraversal Q)
    (hB : ∀ c ∈ caps, s.Represents c.2.support) :
    ∃ Q s' count, (trim caps s P).Runs v (Q, s') count ∧
      count ≤ caps.length * (n + 1) ∧ s'.Correct v ∧ s.TraversalRefines s' ∧
      CapTrimSequence P (caps.map fun c ↦ (v c.1, (v c.1).value c.2.support)) Q ∧
      (∃ T, s'.Compatible T ∧ Q.SameTraversal T) := by
  induction caps generalizing s P with
  | nil => exact ⟨P, s, 0, .done _, by simp, hs, s.traversalRefines_refl, .nil P, hP⟩
  | cons c caps ih =>
    have hv := s.supportValue_eq hs (hB c List.mem_cons_self) c.1
    have hn := (v c.1).value_nonneg c.2.measurableSet_support c.2.support_subset_unit
    obtain ⟨a, s', k, hk, hcount, hs', href, _, ht, _, _, hrem⟩ :=
      s.capTrim_runs hs c.1 P hP (s.supportValue c.1 c.2.support) (by rw [hv]; exact hn)
    obtain ⟨Q, s'', l, hl, hlc, hs'', href', hseq, hQ⟩ :=
      ih s' (P.suffixAt a) hs' hrem (fun d hd ↦
        href.refines.represents (hB d (List.mem_cons_of_mem _ hd)))
    refine ⟨Q, s'', k + l, hk.bind hl, ?_, hs'', href.trans href', ?_, hQ⟩
    · simp only [List.length_cons]
      nlinarith
    · simp only [List.map_cons]
      exact .cons (hv ▸ ht) hseq

/-- Caps for the first `k` positions, clamped to the number of inputs. -/
def earlier {n : ℕ} (agents : Equiv.Perm (Fin n)) (Y : Fin n → Piece)
    (k : ℕ) : List (Fin n × Piece) :=
  (List.finRange n).take k |>.map fun r ↦ (agents r, Y r)

/-- Process the first `k` positions. Every new piece starts whole. -/
def build {n : ℕ} (agents : Equiv.Perm (Fin n)) (inputs : Fin n → Piece) :
    ℕ → RecordedState n → RWProtocol n (Result n)
  | 0, s => .done ⟨s, fun _ ↦ Piece.empty⟩
  | k + 1, s => (build agents inputs k s).bind fun r ↦
      if h : k < n then
        (trim (earlier agents r.bundles k) r.state (inputs ⟨k, h⟩)).map fun (Q, s') ↦
          ⟨s', Function.update r.bundles ⟨k, h⟩ Q⟩
      else .done r

private theorem mem_earlier {n : ℕ} (agents : Equiv.Perm (Fin n)) (Y : Fin n → Piece)
    (k : ℕ) (c : Fin n × Piece) :
    c ∈ earlier agents Y k ↔ ∃ r : Fin n, r.val < k ∧ c = (agents r, Y r) := by
  simp only [earlier, List.mem_map, List.mem_take_iff_getElem, List.length_finRange,
    List.getElem_finRange]
  constructor
  · rintro ⟨r, ⟨i, hi, he⟩, hc⟩
    subst r
    exact ⟨⟨i, lt_of_lt_of_le hi (min_le_right _ _)⟩,
      lt_of_lt_of_le hi (min_le_left _ _), hc.symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, ⟨r.val, lt_min hr r.isLt, rfl⟩, rfl⟩

/-- Section 5, Algorithm `alg:permute`: the first k outer-loop iterations
construct their cap sequences, retaining correct records and all traversals.
The cost counts each earlier/later pair once. -/
theorem build_correct {n : ℕ} (agents : Equiv.Perm (Fin n)) (inputs : Fin n → Piece)
    (k : ℕ) (hk : k ≤ n) (s : RecordedState n) (v : Fin n → Valuation)
    (hs : s.Correct v)
    (hinputs : ∀ r, ∃ Q, s.Compatible Q ∧ (inputs r).SameTraversal Q) :
    ∃ r count, (build agents inputs k s).Runs v r count ∧
      count ≤ (n + 1) * k.choose 2 ∧ r.state.Correct v ∧ s.TraversalRefines r.state ∧
      (∀ j, ∃ Q, r.state.Compatible Q ∧ (r.bundles j).SameTraversal Q) ∧
      (∀ j : Fin n, j.val < k →
        CapTrimSequence (inputs j) (caps (v ∘ agents) r.bundles j.val) (r.bundles j)) := by
  induction k with
  | zero =>
    refine ⟨⟨s, fun _ ↦ Piece.empty⟩, 0, .done _, by simp, hs,
      s.traversalRefines_refl, ?_, ?_⟩
    · intro j
      exact ⟨Piece.empty, (fun _ h ↦ by simp [Piece.empty] at h),
        Piece.SameTraversal.refl _⟩
    · intro j hj; omega
  | succ k ih =>
    have hkn : k < n := by omega
    let t : Fin n := ⟨k, hkn⟩
    obtain ⟨r, a, ha, hca, hrs, href, halign, hseq⟩ := ih (by omega)
    have hB : ∀ c ∈ earlier agents r.bundles k, r.state.Represents c.2.support := by
      intro c hc
      obtain ⟨j, _, rfl⟩ := (mem_earlier agents r.bundles k c).mp hc
      obtain ⟨Q, hQ, he⟩ := halign j
      exact ⟨Q, hQ, he.support_eq.symm⟩
    obtain ⟨Q, s', b, hb, hcb, hs', href', htrim, hQ⟩ :=
      trim_correct (earlier agents r.bundles k) r.state (inputs t) v hrs
        (href.preserves_along (hinputs t)) hB
    let Y := Function.update r.bundles t Q
    have hsame (j : Fin n) (hj : j.val < k) : Y j = r.bundles j := by
      apply Function.update_of_ne
      intro he
      have := congrArg Fin.val he
      change j.val = k at this
      omega
    have hcaps (m : ℕ) (hm : m ≤ k) :
        caps (v ∘ agents) Y m = caps (v ∘ agents) r.bundles m :=
      caps_congr _ _ _ _ (fun j hj ↦ congrArg Piece.support (hsame j (by omega)))
    refine ⟨⟨s', Y⟩, a + b, ?_, ?_, hs', href.trans href', ?_, ?_⟩
    · change ((build agents inputs k s).bind _).Runs v _ _
      apply ha.bind
      simp only [dite_eq_left hkn]
      exact hb.map _
    · have hlen : (earlier agents r.bundles k).length = k := by
        simp [earlier, min_eq_left (show k ≤ n by omega)]
      rw [hlen] at hcb
      have he : (k + 1).choose 2 = k + k.choose 2 := by
        simpa using Nat.choose_succ_succ k 1
      rw [he]
      nlinarith
    · intro j
      by_cases hj : j = t
      · subst j
        simpa only [Y, Function.update_self] using hQ
      · simpa only [Y, Function.update_of_ne hj] using
          href'.preserves_along (halign j)
    · intro j hj
      by_cases he : j = t
      · subst j
        change CapTrimSequence (inputs t) (caps (v ∘ agents) Y k) (Y t)
        rw [hcaps k le_rfl]
        simp only [Y, Function.update_self]
        simpa only [earlier, List.map_map, Function.comp_def, caps] using htrim
      · have hjk : j.val < k := by
          have hne : j.val ≠ k := fun hjk ↦ he (Fin.ext hjk)
          omega
        change CapTrimSequence (inputs j) (caps (v ∘ agents) Y j.val) (Y j)
        rw [hcaps j.val hjk.le, hsame j hjk]
        exact hseq j hjk

/-- One guess, with positions in the two supplied permutations kept explicit. -/
def run {n : ℕ} (agents pieces : Equiv.Perm (Fin n)) (inputs : Fin n → Piece)
    (s : RecordedState n) : RWProtocol n (Result n) :=
  build agents (inputs ∘ pieces) n s

/-- Section 5, `eq:permute-caps`: a legal single-guess execution exists and
its result satisfies the record-independent candidate characterization. -/
theorem run_correct {n : ℕ} (agents pieces : Equiv.Perm (Fin n))
    (inputs : Fin n → Piece) (s : RecordedState n) (v : Fin n → Valuation)
    (hs : s.Correct v)
    (hinputs : ∀ j, ∃ Q, s.Compatible Q ∧ (inputs j).SameTraversal Q) :
    ∃ r count, (run agents pieces inputs s).Runs v r count ∧
      count ≤ (n + 1) * n.choose 2 ∧ r.state.Correct v ∧ s.TraversalRefines r.state ∧
      (∀ j, ∃ Q, r.state.Compatible Q ∧ (r.bundles j).SameTraversal Q) ∧
      IsCandidate (v ∘ agents) (inputs ∘ pieces) r.bundles := by
  obtain ⟨r, count, hr, hc, hrs, href, halign, hseq⟩ :=
    build_correct agents (inputs ∘ pieces) n le_rfl s v hs (fun j ↦ hinputs (pieces j))
  refine ⟨r, count, hr, hc, hrs, href, halign, ?_⟩
  exact ⟨fun j ↦ (sequence_characterization j (hseq j j.isLt)).1,
    fun i j hij ↦ (sequence_characterization j (hseq j j.isLt)).2.1 i hij,
    fun j ↦ (sequence_characterization j (hseq j j.isLt)).2.2⟩

/-- Section 5, Algorithm `alg:permute`: every legal execution of a single guess
has the candidate characterization and the stated query and record guarantees. -/
theorem runs_spec {n : ℕ} (agents pieces : Equiv.Perm (Fin n))
    (inputs : Fin n → Piece) {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v)
    (hinputs : ∀ j, ∃ Q, s.Compatible Q ∧ (inputs j).SameTraversal Q)
    {r : Result n} {count : ℕ} (hr : (run agents pieces inputs s).Runs v r count) :
    count ≤ (n + 1) * n.choose 2 ∧ r.state.Correct v ∧ s.TraversalRefines r.state ∧
      (∀ j, ∃ Q, r.state.Compatible Q ∧ (r.bundles j).SameTraversal Q) ∧
      IsCandidate (v ∘ agents) (inputs ∘ pieces) r.bundles := by
  obtain ⟨r', count', hr', hc, hrs, href, halign, hcandidate⟩ :=
    run_correct agents pieces inputs s v hs hinputs
  obtain ⟨rfl, rfl⟩ := hr.unique hr'
  exact ⟨hc, hrs, href, halign, hcandidate⟩

/-- Section 5, `eq:permute-caps`: the protocol realizes the mathematical
candidate, independent of how its input traversals are represented in records. -/
theorem runs_candidate_support {n : ℕ} (agents pieces : Equiv.Perm (Fin n))
    (inputs : Fin n → Piece) {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v)
    (hinputs : ∀ j, ∃ Q, s.Compatible Q ∧ (inputs j).SameTraversal Q)
    {r : Result n} {count : ℕ} (hr : (run agents pieces inputs s).Runs v r count) :
    ∀ j, (r.bundles j).support =
      (candidate (v ∘ agents) (inputs ∘ pieces) j).support := by
  have hc := (runs_spec agents pieces inputs hs hinputs hr).2.2.2.2
  exact hc.support_unique (candidate_spec _ _) (fun _ ↦ Piece.SameTraversal.refl _)

/-- Section 5's fixed candidate can be reused across guesses' refined records.
For the same valuations and orders, any two correct record states admitting the
input traversals produce identical bundle supports, even with subdivided inputs. -/
theorem record_independent {n : ℕ} (agents pieces : Equiv.Perm (Fin n))
    (inputs inputs' : Fin n → Piece) {s s' : RecordedState n}
    {v : Fin n → Valuation} (hs : s.Correct v) (hs' : s'.Correct v)
    (hinputs : ∀ j, ∃ Q, s.Compatible Q ∧ (inputs j).SameTraversal Q)
    (hinputs' : ∀ j, ∃ Q, s'.Compatible Q ∧ (inputs' j).SameTraversal Q)
    (htraversal : ∀ j, (inputs j).SameTraversal (inputs' j))
    {r r' : Result n} {count count' : ℕ}
    (hr : (run agents pieces inputs s).Runs v r count)
    (hr' : (run agents pieces inputs' s').Runs v r' count') :
    ∀ j, (r.bundles j).support = (r'.bundles j).support := by
  have hc := (runs_spec agents pieces inputs hs hinputs hr).2.2.2.2
  have hc' := (runs_spec agents pieces inputs' hs' hinputs' hr').2.2.2.2
  exact hc.support_unique hc' (fun j ↦ htraversal (pieces j))

end CakeCuttingPsomas.CandidateConstruction
