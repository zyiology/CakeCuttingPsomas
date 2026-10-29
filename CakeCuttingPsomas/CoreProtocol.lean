module

public import CakeCuttingPsomas.Core
public import CakeCuttingPsomas.Permute
public import CakeCuttingPsomas.EqualPartition

set_option linter.style.header false

/-! # Core from Permute

Section 4's `alg:core` and proof of `lem:core main`, conditional only on a
protocol satisfying `lem:permute`.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.CoreAssembly

/-- Section 4's query inequality for `lem:core main`. -/
theorem query_cost_le {n : ℕ} (hn : 2 ≤ n) :
    (n - 1) * (n + 1) + permuteQueryBound n ≤ coreQueryBound n := by
  have hchoose : 2 * n.choose 2 ≤ n * (n - 1) := by
    rw [Nat.choose_two_right]
    omega
  have hf : 1 ≤ (Nat.factorial n) ^ 2 := by
    have := Nat.factorial_pos n
    nlinarith
  have hpoly : (n - 1) * (n + 1) + (n + 1) * n.choose 2 ≤ n ^ 3 := by
    have hm := Nat.mul_le_mul_left (n + 1) hchoose
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have he : 2 + k - 1 = k + 1 := by omega
    simp only [he] at hm ⊢
    nlinarith [Nat.zero_le (k ^ 3)]
  calc
    (n - 1) * (n + 1) + permuteQueryBound n ≤
        ((n - 1) * (n + 1) + (n + 1) * n.choose 2) * (Nat.factorial n) ^ 2 := by
      unfold permuteQueryBound
      nlinarith [Nat.mul_le_mul_left ((n - 1) * (n + 1)) hf]
    _ ≤ n ^ 3 * (Nat.factorial n) ^ 2 := Nat.mul_le_mul_right _ hpoly
    _ = coreQueryBound n := rfl

/-- Section 4's `alg:core`: equal prefix cuts followed by the supplied Permute.
All division targets use recorded values, independently of valuations. -/
def protocol (P : PermuteProtocol) : CoreProtocol :=
  fun n hn s C c ↦ match n, hn, s, c with
  | 0, hn, _, _ => False.elim (by omega)
  | m + 1, _, s, c =>
    (EqualPartition.run c (s.pieceValue c C / (m + 1)) m s C).bind fun r ↦
      (P (m + 1) (by omega) r.state C r.pieces).map
        PermuteResult.toRecordedAllocationResult

/-- Section 4's `lem:core main`: envy-freeness forces the cutter's share to be
exactly 1/n, since a whole equal piece is allocated and every bundle is a suffix
of an equal piece. No normalization or positive-value assumptions are added. -/
theorem protocol_correct (P : PermuteProtocol) (hP : P.Correct) :
    (protocol P).Correct := by
  intro n hn s C c v hs hC
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let target : ℝ := s.pieceValue c C / (m + 1)
  have ht : target = (v c).value C.support / (m + 1 : ℕ) := by
    dsimp only [target]
    rw [s.pieceValue_eq hs hC]
    simp only [Nat.cast_add, Nat.cast_one]
  have hnonneg : 0 ≤ target := by
    rw [ht]
    exact div_nonneg ((v c).value_nonneg C.measurableSet_support C.support_subset_unit)
      (by positivity)
  have hv : (v c).value C.support = (m + 1 : ℕ) * target := by
    rw [ht]
    push_cast
    field_simp
  obtain ⟨r, a, ha, hca, hrs, href, hrp, hdis, hcover, hvalues⟩ :=
    EqualPartition.run_correct c target m s C v hs hC hnonneg hv
  obtain ⟨z, b, hb, hzs, hzi, hef, hsuffix, ⟨whole, hwhole⟩, _hindiff, hcb⟩ :=
    hP (m + 1) (by omega) r.state C r.pieces v hrs hrp hdis hcover
  refine ⟨z.toRecordedAllocationResult, a + b, ?_, hzs,
    ⟨href.refines.trans hzi.1, hzi.2⟩, hef, ?_, ?_⟩
  · change ((EqualPartition.run c target m s C).bind _).Runs v _ _
    exact ha.bind (hb.map PermuteResult.toRecordedAllocationResult)
  · have hlow : target ≤ (v c).value (z.allocation.bundle c).support := by
      have h := hef c whole
      rw [hwhole, hvalues] at h
      exact h
    have hupp : (v c).value (z.allocation.bundle c).support ≤ target := by
      obtain ⟨x, _hx, heq⟩ := hsuffix c
      have hsub : (z.allocation.bundle c).support ⊆ (r.pieces (z.assignment c)).support := by
        rw [heq]
        exact Piece.suffix_subset _ _
      have h := (v c).value_mono (z.allocation.bundle c).measurableSet_support
        (r.pieces (z.assignment c)).measurableSet_support hsub
        (r.pieces (z.assignment c)).support_subset_unit
      rwa [hvalues] at h
    exact (le_antisymm hupp hlow).trans ht
  · have hc := Nat.add_le_add hca hcb
    have hbudget := query_cost_le hn
    exact hc.trans hbudget

end CakeCuttingPsomas.CoreAssembly
