module

public import CakeCuttingPsomas.DominateRepair

set_option linter.style.header false

/-! # Progress after shrinking in Dominate

Section 3, proof of `lem: dominate` in `paper/main.tex`: old dominations transfer
through the bundle permutation, and shrinking creates one additional domination.
The extension hypotheses describe a completed shrinking loop; its construction,
termination, and query accounting are separate obligations.
-/

@[expose] public section

noncomputable section

namespace CakeCuttingPsomas

namespace Allocation

variable {n : ℕ} {C : Piece}

/-- Section 3's `Domᵢ(X,R)` in the proof of `lem: dominate`. This includes the
self-index exactly when the domination inequality holds, as in the paper. -/
def dominatedAgents (X : Allocation n C) (v : Fin n → Valuation) (i : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (X.Dominates v i)

@[simp]
theorem mem_dominatedAgents (X : Allocation n C) (v : Fin n → Valuation) (i j : Fin n) :
    j ∈ X.dominatedAgents v i ↔ X.Dominates v i j := by
  classical
  simp [dominatedAgents]

/-- Section 3, proof of `lem: dominate`: the number of indices dominated by `i`. -/
def dominationCount (X : Allocation n C) (v : Fin n → Valuation) (i : Fin n) : ℕ :=
  (X.dominatedAgents v i).card

/-- Section 3's bounded progress measure in the proof of `lem: dominate`. -/
def totalDominationCount (X : Allocation n C) (v : Fin n → Valuation) : ℕ :=
  ∑ i, X.dominationCount v i

/-- Section 3, proof of `lem: dominate`: preserving all old bundles through a
permutation makes the final residue a subset of the old residue. -/
theorem residue_subset_of_permuted_containment (X W : Allocation n C)
    (σ : Equiv.Perm (Fin n))
    (hkeep : ∀ j, (X.bundle j).support ⊆ (W.bundle (σ j)).support) :
    W.residue ⊆ X.residue := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro hxold
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxold
  exact hx.2 (Set.mem_iUnion.mpr ⟨σ j, hkeep j hj⟩)

/-- Section 3, proof of `lem: dominate`, inheritance of old dominations:
an envy-free final extension transfers domination of `j` to domination of `σ j`.
The upper containment records that additions came from the old residue. -/
theorem dominates_of_permuted_extension (X W : Allocation n C)
    (v : Fin n → Valuation) (σ : Equiv.Perm (Fin n))
    (hW : W.EnvyFree v)
    (hkeep : ∀ j, (X.bundle j).support ⊆ (W.bundle (σ j)).support)
    (hupper : ∀ j, (W.bundle (σ j)).support ⊆
      (X.bundle j).support ∪ (X.residue \ W.residue))
    (i j : Fin n) (hdom : X.Dominates v i j) : W.Dominates v i (σ j) := by
  have hres := residue_subset_of_permuted_containment X W σ hkeep
  have hown : (v i).value (X.bundle i).support ≤ (v i).value (W.bundle i).support :=
    ((v i).value_mono (X.bundle i).measurableSet_support
      (W.bundle (σ i)).measurableSet_support (hkeep i)
      (W.bundle (σ i)).support_subset_unit).trans (hW i (σ i))
  have hsubset : (W.bundle (σ j)).support ∪ W.residue ⊆
      (X.bundle j).support ∪ X.residue := by
    intro x hx
    rcases hx with hx | hx
    · exact (hupper j hx).elim Or.inl (fun hr ↦ Or.inr hr.1)
    · exact Or.inr (hres hx)
  have hbudget := (v i).value_mono
    ((W.bundle (σ j)).measurableSet_support.union W.measurableSet_residue)
    ((X.bundle j).measurableSet_support.union X.measurableSet_residue)
    hsubset (Set.union_subset (X.bundle j).support_subset_unit X.residue_subset_unit)
  rw [(v i).value_union (W.bundle (σ j)).measurableSet_support W.measurableSet_residue
    (W.bundle (σ j)).support_subset_unit W.residue_subset_unit (W.disjoint_bundle_residue _),
    (v i).value_union (X.bundle j).measurableSet_support X.measurableSet_residue
    (X.bundle j).support_subset_unit X.residue_subset_unit (X.disjoint_bundle_residue _)]
    at hbudget
  exact hbudget.trans (hdom.trans hown)

/-- Section 3, proof of `lem: dominate`: the permutation embeds every old
dominated set into the corresponding final dominated set. -/
theorem dominatedAgents_image_subset (X W : Allocation n C) (v : Fin n → Valuation)
    (σ : Equiv.Perm (Fin n))
    (htransfer : ∀ i j, X.Dominates v i j → W.Dominates v i (σ j)) (i : Fin n) :
    (X.dominatedAgents v i).image σ ⊆ W.dominatedAgents v i := by
  classical
  intro k hk
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
  exact (W.mem_dominatedAgents v i _).mpr
    (htransfer i j ((X.mem_dominatedAgents v i j).mp hj))

/-- Section 3, proof of `lem: dominate`: transferring old dominations through
a permutation makes every agent's domination count nondecreasing. -/
theorem dominationCount_le_of_transfer (X W : Allocation n C) (v : Fin n → Valuation)
    (σ : Equiv.Perm (Fin n))
    (htransfer : ∀ i j, X.Dominates v i j → W.Dominates v i (σ j)) (i : Fin n) :
    X.dominationCount v i ≤ W.dominationCount v i := by
  classical
  have hc := Finset.card_le_card (dominatedAgents_image_subset X W v σ htransfer i)
  simpa [dominationCount, Finset.card_image_of_injective _ σ.injective] using hc

/-- Section 3, proof of `lem: dominate`: a newly dominated image outside the
old dominated set increases the distinguished count by at least one. -/
theorem dominationCount_succ_le_of_transfer (X W : Allocation n C)
    (v : Fin n → Valuation) (σ : Equiv.Perm (Fin n))
    (htransfer : ∀ i j, X.Dominates v i j → W.Dominates v i (σ j))
    (a b : Fin n) (hold : ¬ X.Dominates v a b) (hnew : W.Dominates v a (σ b)) :
    X.dominationCount v a + 1 ≤ W.dominationCount v a := by
  classical
  have hnot : σ b ∉ (X.dominatedAgents v a).image σ := by
    intro hb
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hb
    have hjb := σ.injective heq
    subst j
    exact hold ((X.mem_dominatedAgents v a b).mp hj)
  have hsub : insert (σ b) ((X.dominatedAgents v a).image σ) ⊆
      W.dominatedAgents v a :=
    Finset.insert_subset ((W.mem_dominatedAgents v a _).mpr hnew)
      (dominatedAgents_image_subset X W v σ htransfer a)
  have hc := Finset.card_le_card hsub
  simpa [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ σ.injective,
    dominationCount] using hc

/-- Section 3, proof of `lem: dominate`: nondecreasing counts and one strict
increase make the sum increase by at least one. -/
theorem totalDominationCount_succ_le (X W : Allocation n C) (v : Fin n → Valuation)
    (hcounts : ∀ i, X.dominationCount v i ≤ W.dominationCount v i)
    (a : Fin n) (ha : X.dominationCount v a + 1 ≤ W.dominationCount v a) :
    X.totalDominationCount v + 1 ≤ W.totalDominationCount v := by
  have hlt : X.totalDominationCount v < W.totalDominationCount v := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hcounts i
    · exact ⟨a, Finset.mem_univ a, by omega⟩
  omega

/-- Section 3, proof of `lem: dominate`, termination measure: the sum of all
domination counts is at most `n²`, including possible self-dominations. -/
theorem totalDominationCount_le_sq (X : Allocation n C) (v : Fin n → Valuation) :
    X.totalDominationCount v ≤ n ^ 2 := by
  have hc : ∀ i, X.dominationCount v i ≤ n := by
    intro i
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  calc
    X.totalDominationCount v ≤ ∑ _i : Fin n, n := Finset.sum_le_sum (fun i _ ↦ hc i)
    _ = n ^ 2 := by simp [pow_two]

end Allocation

namespace DominateChoice

/-- Section 3, proof of `lem: dominate`, inequality `eq: i dominates sigma j`:
the preserved post-Repair advantage and final residue bound create domination. -/
theorem Spec.dominates_after_shrinking {n t : ℕ} {C R : Piece}
    {X : Allocation n C} {Y : Allocation n R} {v : Fin n → Valuation}
    {a b : Fin n} {π : Equiv.Perm (Fin n)} (h : Spec X Y v t a b π)
    (hn : 3 ≤ n) (hR : R.support = X.residue)
    (r : RepairResult n C (permutedCombined X Y hR π)) (W : Allocation n C)
    (hX : X.EnvyFree v) (hr : r.allocation.EnvyFree v)
    (hadd : ∀ i j, (v i).value (r.addition j).support ≤
      3 * (n : ℝ) ^ 2 * scale n t *
        (v i).value (permutedCombined X Y hR π).residue)
    (hgap : (v a).value (r.allocation.bundle a).support -
      (v a).value (r.allocation.bundle (r.permutation b)).support ≤
        (v a).value (W.bundle a).support -
          (v a).value (W.bundle (r.permutation b)).support)
    (hres : (v a).value W.residue ≤ scale n t * (v a).value Y.residue) :
    W.Dominates v a (r.permutation b) := by
  have hbound := (h.postRepair_advantage hR r hX hr hadd).trans hgap
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hfactor : 1 ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
  have hα := (scale_repair_bounds hn h.exponent_lower).1.le
  have hu := (v a).value_nonneg Y.measurableSet_residue Y.residue_subset_unit
  have hscale := mul_le_mul_of_nonneg_right hfactor (mul_nonneg hα hu)
  unfold Allocation.Dominates
  nlinarith

/-- Section 3, proof of `lem: dominate`, progress after shrinking: all old
dominations transfer through Repair's permutation, every count is nondecreasing,
and the distinguished count and the total increase by at least one. -/
theorem Spec.progress_after_shrinking {n t : ℕ} {C R : Piece}
    {X : Allocation n C} {Y : Allocation n R} {v : Fin n → Valuation}
    {a b : Fin n} {π : Equiv.Perm (Fin n)} (h : Spec X Y v t a b π)
    (hn : 3 ≤ n) (hR : R.support = X.residue)
    (r : RepairResult n C (permutedCombined X Y hR π)) (W : Allocation n C)
    (hX : X.EnvyFree v) (hr : r.allocation.EnvyFree v)
    (hadd : ∀ i j, (v i).value (r.addition j).support ≤
      3 * (n : ℝ) ^ 2 * scale n t *
        (v i).value (permutedCombined X Y hR π).residue)
    (hW : W.EnvyFree v)
    (hkeep : ∀ j, (X.bundle j).support ⊆ (W.bundle (r.permutation j)).support)
    (hupper : ∀ j, (W.bundle (r.permutation j)).support ⊆
      (X.bundle j).support ∪ (X.residue \ W.residue))
    (hgap : (v a).value (r.allocation.bundle a).support -
      (v a).value (r.allocation.bundle (r.permutation b)).support ≤
        (v a).value (W.bundle a).support -
          (v a).value (W.bundle (r.permutation b)).support)
    (hres : (v a).value W.residue ≤ scale n t * (v a).value Y.residue) :
    (∀ i j, X.Dominates v i j → W.Dominates v i (r.permutation j)) ∧
      (∀ i, X.dominationCount v i ≤ W.dominationCount v i) ∧
      X.dominationCount v a + 1 ≤ W.dominationCount v a ∧
      X.totalDominationCount v + 1 ≤ W.totalDominationCount v := by
  have htransfer := Allocation.dominates_of_permuted_extension X W v r.permutation
    hW hkeep hupper
  have hcounts := Allocation.dominationCount_le_of_transfer X W v r.permutation htransfer
  have hnew := h.dominates_after_shrinking hn hR r W hX hr hadd hgap hres
  have hstrict := Allocation.dominationCount_succ_le_of_transfer X W v r.permutation
    htransfer a b h.not_dominates hnew
  exact ⟨htransfer, hcounts, hstrict,
    Allocation.totalDominationCount_succ_le X W v hcounts a hstrict⟩

end DominateChoice

end CakeCuttingPsomas
