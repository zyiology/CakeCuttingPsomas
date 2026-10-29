module

public import CakeCuttingPsomas.Repair

set_option linter.style.header false

/-! # Preparing represented inputs

Section 1.3's recorded-value convention: old supports can be read and passed to
subroutines after the shared partition has been refined. No valuations occur in
these constructions, and no queries are made.
-/

@[expose] public section
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace CakeCuttingPsomas

namespace RecordedState

/-- Select the current cells contained in a support. The partition order suffices
for the ambient cake of Repair; no prefix traversal of this representation is used. -/
def represent {n : ℕ} (s : RecordedState n) (S : Set ℝ) : Piece where
  intervals := s.partition.intervals.filter (fun I ↦ decide (I.support ⊆ S))
  disjoint := s.partition.disjoint.filter _

theorem compatible_represent {n : ℕ} (s : RecordedState n) (S : Set ℝ) :
    s.Compatible (s.represent S) := by
  intro I hI
  exact (List.mem_filter.mp hI).1

/-- Section 1.3: selecting cells recovers every represented support exactly,
including empty and zero-valued pieces. -/
theorem support_represent {n : ℕ} {s : RecordedState n} {S : Set ℝ}
    (hS : s.Represents S) : (s.represent S).support = S := by
  obtain ⟨P, hP, rfl⟩ := hS
  ext x
  constructor
  · rintro ⟨I, hI, hx⟩
    exact (of_decide_eq_true (List.mem_filter.mp hI).2) hx
  · rintro ⟨I, hI, hx⟩
    exact ⟨I, List.mem_filter.mpr ⟨hP I hI, by
      simp only [decide_eq_true_eq]
      exact fun y hy ↦ ⟨I, hI, hy⟩⟩, hx⟩

/-- Choose current cells for a support whose internal traversal is not prescribed.
Invalid branches retain the input, so its support is always unchanged. -/
def alignSupport {n : ℕ} (s : RecordedState n) (P : Piece) : Piece :=
  if s.Represents P.support then s.represent P.support else P

@[simp] theorem support_alignSupport {n : ℕ} (s : RecordedState n) (P : Piece) :
    (s.alignSupport P).support = P.support := by
  classical
  unfold alignSupport
  split_ifs with h
  · exact s.support_represent h
  · rfl

theorem compatible_alignSupport {n : ℕ} {s : RecordedState n} {P : Piece}
    (h : s.Represents P.support) : s.Compatible (s.alignSupport P) := by
  classical
  simpa only [alignSupport, ite_eq_left h] using s.compatible_represent P.support

/-- Read a represented support using only the current cell table. -/
def supportValue {n : ℕ} (s : RecordedState n) (i : Fin n) (S : Set ℝ) : ℝ :=
  s.pieceValue i (s.represent S)

/-- Section 1.3: represented bundle and residue values cost no new queries. -/
theorem supportValue_eq {n : ℕ} {s : RecordedState n} {v : Fin n → Valuation}
    (hs : s.Correct v) {S : Set ℝ} (hS : s.Represents S) (i : Fin n) :
    s.supportValue i S = (v i).value S := by
  rw [supportValue, pieceValue_eq hs (compatible_represent s S), support_represent hS]

theorem Refines.represents {n : ℕ} {s s' : RecordedState n} (h : s.Refines s')
    {S : Set ℝ} (hS : s.Represents S) : s'.Represents S := by
  obtain ⟨P, hP, rfl⟩ := hS
  exact h P hP

end RecordedState

namespace Allocation

/-- Regard an allocation as an allocation of a different representation of the
same cake. Bundles retain their original traversal orders. -/
def rebase {n : ℕ} {C C' : Piece} (D : Allocation n C)
    (h : C'.support = C.support) : Allocation n C' where
  bundle := D.bundle
  contained := fun i ↦ h.symm ▸ D.contained i
  disjoint := D.disjoint

@[simp] theorem rebase_bundle {n : ℕ} {C C' : Piece} (D : Allocation n C)
    (h : C'.support = C.support) (i : Fin n) : (D.rebase h).bundle i = D.bundle i := rfl

@[simp] theorem rebase_residue {n : ℕ} {C C' : Piece} (D : Allocation n C)
    (h : C'.support = C.support) : (D.rebase h).residue = D.residue := by
  simp only [residue, allocated, rebase, h]

end Allocation

namespace RepairResult

/-- Transport Repair's output back to the original cake representation. -/
def rebase {n : ℕ} {C C' : Piece} {D : Allocation n C}
    (h : C'.support = C.support) (r : RepairResult n C' (D.rebase h)) :
    RepairResult n C D where
  allocation := r.allocation.rebase h.symm
  state := r.state
  residue := r.residue
  residue_eq := r.residue_eq.trans (r.allocation.rebase_residue h.symm).symm
  permutation := r.permutation
  addition := r.addition
  addition_subset := by simpa only [Allocation.rebase_residue] using r.addition_subset
  addition_disjoint := r.addition_disjoint
  bundle_eq := r.bundle_eq

/-- Identity output gives total behavior outside Repair's valid-input branch. -/
def unchanged {n : ℕ} {C : Piece} (s : RecordedState n) (D : Allocation n C) :
    RepairResult n C D where
  allocation := D
  state := s
  residue := D.residuePiece
  residue_eq := D.support_residuePiece
  permutation := Equiv.refl _
  addition := fun _ ↦ Piece.empty
  addition_subset := by simp
  addition_disjoint := by simp
  bundle_eq := by simp

end RepairResult

/-- Section 3, Repair call: prepare the ambient cake from refined cells, invoke
the supplied protocol, and transport its output back. Invalid inputs return an
identity output, so construction never needs a correctness proof or valuations. -/
def RepairProtocol.onRepresented (P : RepairProtocol) (n : ℕ) (hn : 2 ≤ n)
    (s : RecordedState n) (C : Piece) (D : Allocation n C) (ε : ℝ) :
    RWProtocol n (RepairResult n C D) :=
  if h : s.Represents C.support then
    (P n hn s (s.represent C.support) (D.rebase (s.support_represent h)) ε).map
      (RepairResult.rebase (s.support_represent h))
  else .done (RepairResult.unchanged s D)

/-- Section 3's `lem:repair main`: preparing represented input preserves every
guarantee and the exact query count of the supplied Repair protocol. -/
theorem RepairProtocol.onRepresented_correct (P : RepairProtocol) (hP : P.Correct)
    {n : ℕ} (hn : 2 ≤ n) (s : RecordedState n) (C : Piece)
    (D : Allocation n C) (ε : ℝ) (v : Fin n → Valuation)
    (hs : s.Correct v) (hC : s.Represents C.support)
    (hD : ∀ j, s.Represents (D.bundle j).support)
    (hε : 0 < ε) (hε' : ε ≤ 1 / (6 * (n : ℝ) ^ 3))
    (hpos : ∀ i, 0 < (v i).value D.residue)
    (hef : ∀ i j, (v i).value (D.bundle j).support - ε * (v i).value D.residue ≤
      (v i).value (D.bundle i).support) :
    ∃ r count, (P.onRepresented n hn s C D ε).Runs v r count ∧
      r.state.Correct v ∧ r.toRecordedAllocationResult.Inherits s ∧
      r.allocation.EnvyFree v ∧
      (∀ i j, (v i).value (r.addition j).support ≤
        3 * (n : ℝ) ^ 2 * ε * (v i).value D.residue) ∧
      (count : ℝ) ≤ (n : ℝ) / ε + coreQueryBound n := by
  obtain ⟨r, count, hr, hrs, hri, href, hra, hc⟩ :=
    hP n hn s (s.represent C.support) (D.rebase (s.support_represent hC)) ε v hs
      (s.compatible_represent _) hD hε hε'
      (by simpa only [Allocation.rebase_residue] using hpos)
      (by simpa only [Allocation.rebase_residue, Allocation.rebase_bundle] using hef)
  refine ⟨r.rebase (s.support_represent hC), count, ?_, hrs, hri, href, ?_, hc⟩
  · simpa only [onRepresented, dite_eq_left hC] using
      hr.map (RepairResult.rebase (s.support_represent hC))
  · simpa only [RepairResult.rebase, Allocation.rebase_residue] using hra

end CakeCuttingPsomas
