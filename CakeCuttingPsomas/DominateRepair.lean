module

public import CakeCuttingPsomas.DominateChoice
public import CakeCuttingPsomas.Repair

set_option linter.style.header false

/-! # The post-Repair advantage in Dominate

Section 3, proof of `lem: dominate` in `paper/main.tex`, paragraph
"Agent i* gains an advantage over the bundle indexed by agent j*".
These results use Repair's output guarantees; they do not assume an
implementation of Repair or construct a protocol execution.
-/

@[expose] public section

namespace CakeCuttingPsomas.DominateChoice

/-- Section 3, proof of `lem: dominate`: after Repair, the distinguished agent
has advantage at least `(n² - 1) α Vᵢ(U)` over the bundle indexed by `j*`.
The permutation maps each input bundle index to its recipient. -/
theorem Spec.postRepair_advantage {n t : ℕ} {C R : Piece}
    {X : Allocation n C} {Y : Allocation n R} {v : Fin n → Valuation}
    {a b : Fin n} {π : Equiv.Perm (Fin n)} (h : Spec X Y v t a b π)
    (hR : R.support = X.residue)
    (r : RepairResult n C (permutedCombined X Y hR π))
    (hX : X.EnvyFree v) (hW : r.allocation.EnvyFree v)
    (hadd : ∀ i j, (v i).value (r.addition j).support ≤
      3 * (n : ℝ) ^ 2 * scale n t *
        (v i).value (permutedCombined X Y hR π).residue) :
    ((n : ℝ) ^ 2 - 1) * scale n t * (v a).value Y.residue ≤
      (v a).value (r.allocation.bundle a).support -
        (v a).value (r.allocation.bundle (r.permutation b)).support := by
  have hkeep : (v a).value ((permutedCombined X Y hR π).bundle a).support ≤
      (v a).value (r.allocation.bundle a).support := by
    exact ((v a).value_mono
      ((permutedCombined X Y hR π).bundle a).measurableSet_support
      (r.allocation.bundle (r.permutation a)).measurableSet_support
      (r.old_bundle_subset a)
      (r.allocation.bundle (r.permutation a)).support_subset_unit).trans
        (hW a (r.permutation a))
  rw [permutedCombined_bundle_value] at hkeep
  have hlower : (v a).value (X.bundle a).support + (v a).value (Y.bundle a).support -
      scale n t * (v a).value Y.residue ≤
        (v a).value (r.allocation.bundle a).support := by
    linarith [h.small_loss a]
  have hupper : (v a).value (r.allocation.bundle (r.permutation b)).support ≤
      (v a).value (X.bundle a).support + (v a).value (Y.bundle a).support -
        (n : ℝ) ^ 2 * scale n t * (v a).value Y.residue := by
    rw [r.value_bundle, permutedCombined_bundle_value]
    have hz := hadd a b
    rw [permutedCombined_residue] at hz
    nlinarith [hX a b, h.large_gap]
  nlinarith

/-- Section 3, proof of `lem: dominate`: positive residue value makes the
post-Repair advantage strictly positive. In particular, `i*` cannot be the
recipient of the bundle indexed by `j*`. -/
theorem Spec.postRepair_strict_advantage {n t : ℕ} {C R : Piece}
    {X : Allocation n C} {Y : Allocation n R} {v : Fin n → Valuation}
    {a b : Fin n} {π : Equiv.Perm (Fin n)} (h : Spec X Y v t a b π)
    (hn : 3 ≤ n) (hR : R.support = X.residue)
    (r : RepairResult n C (permutedCombined X Y hR π))
    (hX : X.EnvyFree v) (hW : r.allocation.EnvyFree v)
    (hadd : ∀ i j, (v i).value (r.addition j).support ≤
      3 * (n : ℝ) ^ 2 * scale n t *
        (v i).value (permutedCombined X Y hR π).residue)
    (hpos : 0 < (v a).value Y.residue) :
    0 < (v a).value (r.allocation.bundle a).support -
      (v a).value (r.allocation.bundle (r.permutation b)).support ∧
      a ≠ r.permutation b := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hfactor : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hα := (scale_repair_bounds hn h.exponent_lower).1
  have hgap := (mul_pos (mul_pos hfactor hα) hpos).trans_le
    (h.postRepair_advantage hR r hX hW hadd)
  refine ⟨hgap, ?_⟩
  intro heq
  rw [heq, sub_self] at hgap
  exact (lt_irrefl 0) hgap

end CakeCuttingPsomas.DominateChoice
