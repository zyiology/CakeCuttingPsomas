module

public import CakeCuttingPsomas.PrefixProtocol
public import CakeCuttingPsomas.RecordedPreparation

set_option linter.style.header false

/-! # Recorded equal partitioning for Core

Section 4, Line `core:cut`: n pieces of equal cutter value using n-1 prefix
cuts. All query targets are computed from inherited records.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.EqualPartition

/-- Geometry and records produced by equal partitioning; no valuations are stored. -/
structure Result (n m : ℕ) where
  state : RecordedState n
  pieces : Fin m → Piece

def prepend {n m : ℕ} (Q : Piece) (r : Result n m) : Result n (m + 1) :=
  ⟨r.state, Fin.cases Q r.pieces⟩

/-- Make k prefix cuts of a fixed recorded target, leaving the last piece whole.
Current-cell representations of the remaining support provide compatible inputs. -/
def run {n : ℕ} (c : Fin n) (target : ℝ) :
    (k : ℕ) → RecordedState n → Piece → RWProtocol n (Result n (k + 1))
  | 0, s, C => .done ⟨s, fun _ ↦ C⟩
  | k + 1, s, C => (s.prefixCut c C target).bind fun (x, s') ↦
      (run c target k s' (s'.represent (C.suffixAt x).support)).map
        (prepend (C.prefixAt x))

/-- Section 4, `core:cut`: exact equal partition, disjointness, inherited records,
and the (n+1) query cost per prefix cut, including zero targets and empty cakes. -/
theorem run_correct {n : ℕ} (c : Fin n) (target : ℝ) (k : ℕ)
    (s : RecordedState n) (C : Piece) (v : Fin n → Valuation)
    (hs : s.Correct v) (hC : s.Compatible C) (ht : 0 ≤ target)
    (hv : (v c).value C.support = (k + 1 : ℕ) * target) :
    ∃ r count, (run c target k s C).Runs v r count ∧ count ≤ k * (n + 1) ∧
      r.state.Correct v ∧ s.Refines r.state ∧
      (∀ j, r.state.Represents (r.pieces j).support) ∧
      (∀ i j, i ≠ j → Disjoint (r.pieces i).support (r.pieces j).support) ∧
      (⋃ j, (r.pieces j).support) = C.support ∧
      (∀ j, (v c).value (r.pieces j).support = target) := by
  induction k generalizing s C with
  | zero =>
    refine ⟨⟨s, fun _ ↦ C⟩, 0, .done _, by simp, hs, s.refines_refl,
      (fun _ ↦ ⟨C, hC, rfl⟩), ?_, ?_, ?_⟩
    · intro i j hij
      exact (hij (Fin.ext (by omega))).elim
    · ext y
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨0, h⟩⟩
    · intro j
      simpa using hv
  | succ k ih =>
    have htarget : target ≤ (v c).value C.support := by
      rw [hv]
      have : (1 : ℝ) ≤ (k + 1 + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ k + 1 + 1)
      nlinarith
    obtain ⟨x, s', a, ha, hca, hs', href, _hx, hval, _hmin, hp, hq⟩ :=
      RecordedState.prefixCut_runs hs c C hC target ht htarget
    have hrem : (v c).value (s'.represent (C.suffixAt x).support).support =
        (k + 1 : ℕ) * target := by
      rw [s'.support_represent hq]
      have hadd := (v c).value_prefix_add_suffix C x
      rw [hval, hv] at hadd
      push_cast at hadd ⊢
      linarith
    obtain ⟨r, b, hb, hcb, hrs, hrr, hrp, hdis, hcover, hvalues⟩ :=
      ih s' (s'.represent (C.suffixAt x).support) hs' (s'.compatible_represent _) hrem
    refine ⟨prepend (C.prefixAt x) r, a + b, ?_, ?_, hrs, href.trans hrr, ?_, ?_, ?_, ?_⟩
    · exact ha.bind (hb.map (prepend (C.prefixAt x)))
    · calc
        a + b ≤ (n + 1) + k * (n + 1) := Nat.add_le_add hca hcb
        _ = (k + 1) * (n + 1) := by ring
    · intro j
      refine Fin.cases ?_ (fun j ↦ hrp j) j
      exact hrr.represents hp
    · have hsub (j : Fin (k + 1)) : (r.pieces j).support ⊆ (C.suffixAt x).support := by
        intro y hy
        have : y ∈ ⋃ j, (r.pieces j).support := Set.mem_iUnion.mpr ⟨j, hy⟩
        rwa [hcover, s'.support_represent hq] at this
      intro i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · intro j
        refine Fin.cases ?_ (fun j _ ↦ ?_) j
        · intro hij
          exact (hij rfl).elim
        · exact (C.prefix_disjoint_suffix x).mono_right (hsub j)
      · intro j
        refine Fin.cases ?_ (fun j hij ↦ ?_) j
        · intro _
          exact ((C.prefix_disjoint_suffix x).mono_right (hsub i)).symm
        · exact hdis i j (fun h ↦ hij (congrArg Fin.succ h))
    · have hunion : (⋃ j, ((prepend (C.prefixAt x) r).pieces j).support) =
          (C.prefixAt x).support ∪ (⋃ j, (r.pieces j).support) := by
        ext y
        simp only [Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨j, hj⟩
          exact Fin.cases (fun h ↦ Or.inl h) (fun j h ↦ Or.inr ⟨j, h⟩) j hj
        · rintro (h | ⟨j, h⟩)
          · exact ⟨0, h⟩
          · exact ⟨j.succ, h⟩
      rw [hunion, hcover, s'.support_represent hq]
      exact C.prefix_union_suffix x
    · intro j
      exact Fin.cases hval hvalues j

end CakeCuttingPsomas.EqualPartition
