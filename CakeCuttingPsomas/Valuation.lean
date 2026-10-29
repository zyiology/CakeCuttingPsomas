module

public import CakeCuttingPsomas.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Basic valuation properties on the unit cake -/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas.Valuation

open MeasureTheory

theorem integrableOn (v : Valuation) {S : Set ℝ} (hS : S ⊆ Set.Icc 0 1) :
    IntegrableOn v.density S :=
  v.integrable.mono_set hS

theorem value_nonneg (v : Valuation) {S : Set ℝ} (hS : MeasurableSet S)
    (hSc : S ⊆ Set.Icc 0 1) : 0 ≤ v.value S :=
  setIntegral_nonneg hS fun x hx ↦ v.nonneg x (hSc hx)

theorem value_mono (v : Valuation) {S T : Set ℝ} (_hS : MeasurableSet S)
    (hT : MeasurableSet T) (hST : S ⊆ T) (hTc : T ⊆ Set.Icc 0 1) :
    v.value S ≤ v.value T := by
  apply setIntegral_mono_set (v.integrableOn hTc)
  · exact (ae_restrict_iff' hT).mpr (Filter.Eventually.of_forall fun x hx ↦
      v.nonneg x (hTc hx))
  · exact Filter.Eventually.of_forall hST

theorem value_union (v : Valuation) {S T : Set ℝ}
    (_hS : MeasurableSet S) (hT : MeasurableSet T)
    (hSc : S ⊆ Set.Icc 0 1) (hTc : T ⊆ Set.Icc 0 1) (hST : Disjoint S T) :
    v.value (S ∪ T) = v.value S + v.value T :=
  setIntegral_union hST hT (v.integrableOn hSc) (v.integrableOn hTc)

@[simp]
theorem value_empty (v : Valuation) : v.value ∅ = 0 := by
  simp [value]

end CakeCuttingPsomas.Valuation
