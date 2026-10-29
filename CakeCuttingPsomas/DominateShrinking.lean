module

public import CakeCuttingPsomas.DominateProgress
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

set_option linter.style.header false

/-! # The shrinking loop in Section 3

The repeated Core calls in the proof of `lem: dominate` in `paper/main.tex`.
All protocol guarantees are conditional on Core's contract.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas

namespace RecordedAllocationResult

/-- Section 3, proof of `lem: dominate`: append Core's allocation of the current
residue without changing agent indices, retaining its records and residue. -/
def appendCore {n : ℕ} {C : Piece} (w : RecordedAllocationResult n C)
    (f : RecordedAllocationResult n w.residue) : RecordedAllocationResult n C where
  allocation := DominateChoice.permutedCombined w.allocation f.allocation w.residue_eq
    (Equiv.refl _)
  state := f.state
  residue := f.residue
  residue_eq := f.residue_eq.trans
    (DominateChoice.permutedCombined_residue _ _ _ _).symm

@[simp] theorem appendCore_bundle {n : ℕ} {C : Piece}
    (w : RecordedAllocationResult n C) (f : RecordedAllocationResult n w.residue)
    (i : Fin n) :
    ((w.appendCore f).allocation.bundle i).support =
      (w.allocation.bundle i).support ∪ (f.allocation.bundle i).support :=
  DominateChoice.permutedCombined_bundle_support _ _ w.residue_eq _ _

@[simp] theorem appendCore_value {n : ℕ} {C : Piece}
    (w : RecordedAllocationResult n C) (f : RecordedAllocationResult n w.residue)
    (v : Valuation) (i : Fin n) :
    v.value ((w.appendCore f).allocation.bundle i).support =
      v.value (w.allocation.bundle i).support + v.value (f.allocation.bundle i).support :=
  DominateChoice.permutedCombined_bundle_value _ _ w.residue_eq _ _ _

/-- Section 3, proof of `lem: dominate`: one Core call preserves envy-freeness
and every bundle advantage. -/
theorem appendCore_envyFree_advantage {n : ℕ} {C : Piece}
    (w : RecordedAllocationResult n C) (f : RecordedAllocationResult n w.residue)
    (v : Fin n → Valuation) (hw : w.allocation.EnvyFree v)
    (hf : f.allocation.EnvyFree v) :
    (w.appendCore f).allocation.EnvyFree v ∧
    ∀ i j, (v i).value (w.allocation.bundle i).support -
      (v i).value (w.allocation.bundle j).support ≤
      (v i).value ((w.appendCore f).allocation.bundle i).support -
        (v i).value ((w.appendCore f).allocation.bundle j).support := by
  constructor
  · intro i j
    simp only [appendCore_value]
    exact add_le_add (hw i j) (hf i j)
  · intro i j
    simp only [appendCore_value]
    linarith [hf i j]

theorem appendCore_inherits {n : ℕ} {C : Piece}
    (w : RecordedAllocationResult n C) (f : RecordedAllocationResult n w.residue)
    {s : RecordedState n} (hw : w.Inherits s) (hf : f.Inherits w.state) :
    (w.appendCore f).Inherits s := by
  refine ⟨hw.1.trans hf.1, ?_, hf.2.2⟩
  intro i
  rw [appendCore_bundle]
  obtain ⟨P, hP, heq⟩ := hw.2.1 i
  have hold : f.state.Represents (w.allocation.bundle i).support := heq ▸ hf.1 P hP
  apply hold.union (hf.2.1 i)
  exact (w.allocation.disjoint_bundle_residue i).mono_right
    ((f.allocation.contained i).trans w.residue_eq.subset)

end RecordedAllocationResult

namespace DominateShrinking

/-- Section 3, proof of `lem: dominate`: maximum number of shrinking Core calls. -/
def budget (n : ℕ) (α : ℝ) : ℕ := ⌈(n : ℝ) * Real.log (1 / α)⌉₊

/-- Section 3, proof of `lem: dominate`: the geometric residue factor is bounded
by the exponential used in the paper's stopping estimate. -/
theorem contraction_exp {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (1 - 1 / (n : ℝ)) ^ k ≤ Real.exp (-(k : ℝ) / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hq : 0 ≤ 1 - 1 / (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    rw [sub_nonneg, div_le_one hnpos]
    exact this
  have he : 1 - 1 / (n : ℝ) ≤ Real.exp (-(1 / (n : ℝ))) := by
    linarith [Real.add_one_le_exp (-(1 / (n : ℝ)))]
  have h := pow_le_pow_left₀ hq he k
  calc
    _ ≤ Real.exp (-(1 / (n : ℝ))) ^ k := h
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Section 3, proof of `lem: dominate`: the ceiling budget suffices for the
exponential contraction to reach the threshold, including `α = 1`. -/
theorem exp_budget {n : ℕ} (hn : 2 ≤ n) {α : ℝ} (hα : 0 < α)
    {k : ℕ} (hk : budget n α ≤ k) : Real.exp (-(k : ℝ) / n) ≤ α := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb : (n : ℝ) * Real.log (1 / α) ≤ k :=
    (Nat.le_ceil _).trans (by exact_mod_cast hk)
  rw [one_div, Real.log_inv] at hb
  have he : -(k : ℝ) / n ≤ Real.log α := by
    apply (div_le_iff₀ hnpos).mpr
    nlinarith
  exact (Real.exp_le_exp.mpr he).trans_eq (Real.exp_log hα)

/-- Section 3, proof of `lem: dominate`: extension by envy-free additions from
an allocation's residue, preserving all bundle advantages. -/
structure Extension {n : ℕ} {C : Piece} (w z : RecordedAllocationResult n C)
    (v : Fin n → Valuation) : Prop where
  envyFree : z.allocation.EnvyFree v
  keep : ∀ i, (w.allocation.bundle i).support ⊆ (z.allocation.bundle i).support
  upper : ∀ i, (z.allocation.bundle i).support ⊆
    (w.allocation.bundle i).support ∪ w.allocation.residue
  gap : ∀ i j, (v i).value (w.allocation.bundle i).support -
    (v i).value (w.allocation.bundle j).support ≤
    (v i).value (z.allocation.bundle i).support -
      (v i).value (z.allocation.bundle j).support

theorem Extension.refl {n : ℕ} {C : Piece} (w : RecordedAllocationResult n C)
    (v : Fin n → Valuation) (hw : w.allocation.EnvyFree v) : Extension w w v :=
  ⟨hw, fun _ ↦ Set.Subset.refl _, fun _ ↦ Set.subset_union_left, fun _ _ ↦ le_rfl⟩

theorem Extension.residue_subset {n : ℕ} {C : Piece}
    {w z : RecordedAllocationResult n C} {v : Fin n → Valuation}
    (h : Extension w z v) : z.allocation.residue ⊆ w.allocation.residue :=
  Allocation.residue_subset_of_permuted_containment _ _ (Equiv.refl _) h.keep

theorem Extension.trans {n : ℕ} {C : Piece}
    {w z u : RecordedAllocationResult n C} {v : Fin n → Valuation}
    (h : Extension w z v) (g : Extension z u v) : Extension w u v := by
  refine ⟨g.envyFree, fun i ↦ (h.keep i).trans (g.keep i), ?_,
    fun i j ↦ (h.gap i j).trans (g.gap i j)⟩
  intro i x hx
  exact (g.upper i hx).elim (fun hx ↦ h.upper i hx) (fun hx ↦ Or.inr (h.residue_subset hx))

theorem appendCore_extension {n : ℕ} {C : Piece}
    (w : RecordedAllocationResult n C) (f : RecordedAllocationResult n w.residue)
    (v : Fin n → Valuation) (hw : w.allocation.EnvyFree v)
    (hf : f.allocation.EnvyFree v) : Extension w (w.appendCore f) v := by
  obtain ⟨hef, hgap⟩ := w.appendCore_envyFree_advantage f v hw hf
  refine ⟨hef, ?_, ?_, hgap⟩
  · intro i
    rw [RecordedAllocationResult.appendCore_bundle]
    exact Set.subset_union_left
  · intro i
    rw [RecordedAllocationResult.appendCore_bundle]
    exact Set.union_subset Set.subset_union_left
      (fun _ hx ↦ Or.inr (w.residue_eq.subset (f.allocation.contained i hx)))

/-- Section 3, algorithm `alg:dominate`, inner loop: test the residue using
recorded values, and call Core with the distinguished cutter while fuel remains.
The second output counts actual Core calls, independently of query counts. -/
def run {C : Piece} (K : CoreProtocol) (n : ℕ) (hn : 2 ≤ n) (a : Fin n) (threshold : ℝ) :
    ℕ → (w : RecordedAllocationResult n C) →
      RWProtocol n (RecordedAllocationResult n C × ℕ)
  | 0, w => .done (w, 0)
  | fuel + 1, w =>
    if w.state.pieceValue a w.residue ≤ threshold then .done (w, 0)
    else (K n hn w.state w.residue a).bind fun f ↦
      (run K n hn a threshold fuel (w.appendCore f)).map
        (fun out ↦ (out.1, out.2 + 1))

/-- Section 3, proof of `lem: dominate`: bounded shrinking preserves the
extension and inherited records and contracts geometrically in the actual number
of Core calls. Either the threshold holds or all supplied fuel was used. -/
theorem run_correct (K : CoreProtocol) (hK : K.Correct)
    {n : ℕ} (hn : 2 ≤ n) (a : Fin n) (threshold : ℝ)
    (fuel : ℕ) {C : Piece} (w : RecordedAllocationResult n C)
    (v : Fin n → Valuation) {s : RecordedState n}
    (hs : w.state.Correct v) (hi : w.Inherits s) (hw : w.allocation.EnvyFree v) :
    ∃ z k count, (run K n hn a threshold fuel w).Runs v (z, k) count ∧
      z.state.Correct v ∧ z.Inherits s ∧ Extension w z v ∧ k ≤ fuel ∧
      count ≤ k * coreQueryBound n ∧
      (v a).value z.residue.support ≤
        (1 - 1 / (n : ℝ)) ^ k * (v a).value w.residue.support ∧
      (k = fuel ∨ (v a).value z.residue.support ≤ threshold) := by
  induction fuel generalizing w with
  | zero =>
    exact ⟨w, 0, 0, .done _, hs, hi, Extension.refl w v hw,
      le_rfl, by simp, by simp, Or.inl rfl⟩
  | succ fuel ih =>
    by_cases hstop : w.state.pieceValue a w.residue ≤ threshold
    · refine ⟨w, 0, 0, ?_, hs, hi, Extension.refl w v hw, by omega,
        by simp, by simp, Or.inr ?_⟩
      · simpa only [run, ite_eq_left hstop] using (RWProtocol.Runs.done (v := v) (w, 0))
      · rwa [RecordedState.pieceValue_eq hs hi.2.2] at hstop
    · obtain ⟨f, c, hrun, hfs, hfi, hfef, hshare, hc⟩ :=
        hK n hn w.state w.residue a v hs hi.2.2
      have he := appendCore_extension w f v hw hfef
      obtain ⟨z, k, d, hzrun, hzs, hzi, hzext, hk, hd, hcontract, hfinish⟩ :=
        ih (w.appendCore f) hfs (w.appendCore_inherits f hi hfi) he.envyFree
      refine ⟨z, k + 1, c + d, ?_, hzs, hzi, he.trans hzext, by omega, ?_, ?_, ?_⟩
      · simp only [run, ite_eq_right hstop]
        exact hrun.bind (hzrun.map (fun out ↦ (out.1, out.2 + 1)))
      · calc
          c + d ≤ coreQueryBound n + k * coreQueryBound n := Nat.add_le_add hc hd
          _ = (k + 1) * coreQueryBound n := by ring
      · have hq : 0 ≤ 1 - 1 / (n : ℝ) := by
          rw [sub_nonneg, div_le_one (by exact_mod_cast (by omega : 0 < n))]
          exact_mod_cast (by omega : 1 ≤ n)
        have hstep := f.cutter_residue_le hn v a hshare
        have hid : ((n : ℝ) - 1) / n = 1 - 1 / (n : ℝ) := by
          field_simp
        rw [hid] at hstep
        exact hcontract.trans (by
          simpa only [RecordedAllocationResult.appendCore, pow_succ, mul_assoc] using
            mul_le_mul_of_nonneg_left hstep (pow_nonneg hq k))
      · exact hfinish.elim (fun h ↦ Or.inl (by omega)) Or.inr

/-- Section 3, proof of `lem: dominate`: the shrinking loop reaches the stopping
threshold within the ceiling budget, preserving records and all extension facts.
The reference value may be zero; no positivity of residue values is needed. -/
theorem shrink_correct (K : CoreProtocol) (hK : K.Correct)
    {n : ℕ} (hn : 2 ≤ n) (a : Fin n) {α u : ℝ} (hα : 0 < α) (hu : 0 ≤ u)
    {C : Piece} (w : RecordedAllocationResult n C) (v : Fin n → Valuation)
    {s : RecordedState n} (hs : w.state.Correct v) (hi : w.Inherits s)
    (hw : w.allocation.EnvyFree v) (hinit : (v a).value w.residue.support ≤ u) :
    ∃ z k count, (run K n hn a (α * u) (budget n α) w).Runs v (z, k) count ∧
      z.state.Correct v ∧ z.Inherits s ∧ Extension w z v ∧
      k ≤ budget n α ∧ count ≤ k * coreQueryBound n ∧
      (v a).value z.residue.support ≤ (1 - 1 / (n : ℝ)) ^ k * u ∧
      (v a).value z.residue.support ≤ α * u := by
  obtain ⟨z, k, count, hr, hs', hi', he, hk, hc, hg, hf⟩ :=
    run_correct K hK hn a (α * u) (budget n α) w v hs hi hw
  have hq : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one (by exact_mod_cast (by omega : 0 < n))]
    exact_mod_cast (by omega : 1 ≤ n)
  have hg' := hg.trans (mul_le_mul_of_nonneg_left hinit (pow_nonneg hq k))
  refine ⟨z, k, count, hr, hs', hi', he, hk, hc, hg', ?_⟩
  rcases hf with hf | hf
  · exact hg'.trans (mul_le_mul_of_nonneg_right
      ((contraction_exp hn k).trans (exp_budget hn hα (by omega))) hu)
  · exact hf

/-- Section 3, proof of `lem: dominate`: the finite geometric choices give the
uniform shrinking budget used in the paper's query accounting. -/
theorem budget_scale_le {n t : ℕ} (hn : 3 ≤ n) (ht : t ≤ n + 1) :
    budget n (DominateChoice.scale n t) ≤
      ⌈(n : ℝ) * (n + 1) * Real.log (4 * (n : ℝ) ^ 2)⌉₊ := by
  apply Nat.ceil_mono
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 0 ≤ Real.log (4 * (n : ℝ) ^ 2) :=
    Real.log_nonneg (by nlinarith)
  simp only [DominateChoice.scale, one_div, inv_pow, inv_inv, Real.log_pow]
  have ht' : (t : ℝ) ≤ n + 1 := by exact_mod_cast ht
  nlinarith [mul_le_mul_of_nonneg_right ht' hb]

end DominateShrinking

namespace DominateChoice

/-- Section 3, proof of `lem: dominate`: any shrinking extension with the
stopping bound supplies the hypotheses for strict domination-count progress. -/
theorem Spec.progress_of_extension {n t : ℕ} {C R : Piece}
    {X : Allocation n C} {Y : Allocation n R} {v : Fin n → Valuation}
    {a b : Fin n} {π : Equiv.Perm (Fin n)} (h : Spec X Y v t a b π)
    (hn : 3 ≤ n) (hR : R.support = X.residue)
    (r : RepairResult n C (permutedCombined X Y hR π))
    (z : RecordedAllocationResult n C)
    (hX : X.EnvyFree v) (hr : r.allocation.EnvyFree v)
    (hadd : ∀ i j, (v i).value (r.addition j).support ≤
      3 * (n : ℝ) ^ 2 * scale n t *
        (v i).value (permutedCombined X Y hR π).residue)
    (he : DominateShrinking.Extension r.toRecordedAllocationResult z v)
    (hres : (v a).value z.residue.support ≤ scale n t * (v a).value Y.residue) :
    (∀ i j, X.Dominates v i j → z.allocation.Dominates v i (r.permutation j)) ∧
      (∀ i, X.dominationCount v i ≤ z.allocation.dominationCount v i) ∧
      X.dominationCount v a + 1 ≤ z.allocation.dominationCount v a ∧
      X.totalDominationCount v + 1 ≤ z.allocation.totalDominationCount v := by
  have hkeep : ∀ j, (X.bundle j).support ⊆
      (z.allocation.bundle (r.permutation j)).support := by
    intro j
    exact (Set.subset_union_left.trans
      ((permutedCombined_bundle_support X Y hR π j).symm.subset)).trans
      ((r.old_bundle_subset j).trans (he.keep _))
  have hupper : ∀ j, (z.allocation.bundle (r.permutation j)).support ⊆
      (X.bundle j).support ∪ (X.residue \ z.allocation.residue) := by
    intro j x hx
    have hnot : x ∉ z.allocation.residue :=
      fun hres ↦ Set.disjoint_left.mp (z.allocation.disjoint_bundle_residue _) hx hres
    rcases he.upper (r.permutation j) hx with hx | hx
    · rw [r.bundle_eq, permutedCombined_bundle_support] at hx
      rcases hx with (hx | hx) | hx
      · exact Or.inl hx
      · exact Or.inr ⟨hR.subset (Y.contained _ hx), hnot⟩
      · have hsub : (permutedCombined X Y hR π).residue ⊆ X.residue := by
          rw [permutedCombined_residue]
          exact Y.residue_subset.trans hR.subset
        exact Or.inr ⟨hsub (r.addition_subset j hx), hnot⟩
    · have hx' : x ∈ Y.residue := by
        rw [← r.residue_eq, r.residue_removed, permutedCombined_residue] at hx
        exact hx.1
      exact Or.inr ⟨hR.subset (Y.residue_subset hx'), hnot⟩
  exact h.progress_after_shrinking hn hR r z.allocation hX hr hadd
    he.envyFree hkeep hupper (he.gap a (r.permutation b)) (by rwa [← z.residue_eq])

/-- Section 3, proof of `lem: dominate`: the inner loop supplies all extension
hypotheses needed for strict domination-count progress after Repair. -/
theorem Spec.shrinking_progress {n t : ℕ} {C R : Piece}
    {X : Allocation n C} {Y : Allocation n R} {v : Fin n → Valuation}
    {a b : Fin n} {π : Equiv.Perm (Fin n)} (h : Spec X Y v t a b π)
    (K : CoreProtocol) (hK : K.Correct) (hn : 3 ≤ n)
    (hR : R.support = X.residue)
    (r : RepairResult n C (permutedCombined X Y hR π))
    (hX : X.EnvyFree v) (hr : r.allocation.EnvyFree v)
    (hadd : ∀ i j, (v i).value (r.addition j).support ≤
      3 * (n : ℝ) ^ 2 * scale n t *
        (v i).value (permutedCombined X Y hR π).residue)
    {s : RecordedState n} (hs : r.state.Correct v)
    (hi : r.toRecordedAllocationResult.Inherits s) :
    ∃ z k count,
      (DominateShrinking.run K n (by omega) a
        (scale n t * (v a).value Y.residue)
        (DominateShrinking.budget n (scale n t)) r.toRecordedAllocationResult).Runs
          v (z, k) count ∧
      z.state.Correct v ∧ z.Inherits s ∧ z.allocation.EnvyFree v ∧
      k ≤ DominateShrinking.budget n (scale n t) ∧
      count ≤ k * coreQueryBound n ∧
      (v a).value z.residue.support ≤ scale n t * (v a).value Y.residue ∧
      (∀ i j, X.Dominates v i j → z.allocation.Dominates v i (r.permutation j)) ∧
      (∀ i, X.dominationCount v i ≤ z.allocation.dominationCount v i) ∧
      X.dominationCount v a + 1 ≤ z.allocation.dominationCount v a ∧
      X.totalDominationCount v + 1 ≤ z.allocation.totalDominationCount v := by
  have hinit : (v a).value r.residue.support ≤ (v a).value Y.residue := by
    apply (v a).value_mono r.residue.measurableSet_support Y.measurableSet_residue
      _ Y.residue_subset_unit
    rw [r.residue_removed, permutedCombined_residue]
    exact Set.sdiff_subset
  obtain ⟨z, k, count, hz, hzs, hzi, he, hk, hc, _hg, hres⟩ :=
    DominateShrinking.shrink_correct K hK (by omega) a
      (scale_repair_bounds hn h.exponent_lower).1
      ((v a).value_nonneg Y.measurableSet_residue Y.residue_subset_unit)
      r.toRecordedAllocationResult v hs hi hr hinit
  have hp := h.progress_of_extension hn hR r z hX hr hadd he hres
  exact ⟨z, k, count, hz, hzs, hzi, he.envyFree, hk, hc, hres, hp⟩

end DominateChoice
end CakeCuttingPsomas

