module

public import CakeCuttingPsomas.RepairLevels
public import CakeCuttingPsomas.CoreProtocol

set_option linter.style.header false

/-! # Repair from Permute

Section 4's `alg:repair` and `lem:repair main`, conditional only on the
contract of `lem:permute`.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas

namespace RecordedState

/-- Section 1.3: the union of recorded disjoint bundles is recorded. -/
theorem represents_allocated {n : ℕ} {C : Piece} {s : RecordedState n}
    (D : Allocation n C) (hD : ∀ i, s.Represents (D.bundle i).support) :
    s.Represents D.allocated := by
  have h := RepairRoundRobin.join_represents s D.bundle D.disjoint hD
    (List.ofFn id) (List.nodup_ofFn.mpr Function.injective_id)
  rw [(RepairRoundRobin.join _ _ _ _).support_eq] at h
  simpa [Allocation.allocated] using h

end RecordedState

namespace RepairAssembly

open RepairLevels
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {C : Piece} {D : Allocation n C}

/-- Algorithm `alg:repair`: retain Permute's bundles on the original cake,
including the unchosen residue outside the Permute call. -/
def transport (p : Picks D) (W : Allocation n p.cake) : Allocation n C where
  bundle := W.bundle
  contained i := (W.contained i).trans p.cake_contained
  disjoint := W.disjoint

/-- The retained part of the chosen cells, indexed by old bundle labels. -/
def addition (p : Picks D) (r : PermuteResult n p.cake) (j : Fin n) : Piece :=
  (r.allocation.bundle (r.assignment.symm j)).diff (D.bundle j)

/-- Section 4, `lem:repair main`: a retained addition lies in its chosen cells. -/
theorem addition_subset (p : Picks D) (r : PermuteResult n p.cake)
    (hsub : ∀ i, (r.allocation.bundle i).support ⊆ (p.input (r.assignment i)).support)
    (j : Fin n) : (addition p r j).support ⊆ (p.added j 0).support := by
  rw [addition, Piece.support_diff]
  intro x hx
  have h := hsub (r.assignment.symm j) hx.1
  simp only [Equiv.apply_symm_apply, Picks.input, Picks.tail, Piece.support_append] at h
  exact h.resolve_right hx.2

/-- Package an intact Permute output with the inverse assignment and a residue
represented in the final records. -/
def result (p : Picks D) (r : PermuteResult n p.cake)
    (hsub : ∀ i, (r.allocation.bundle i).support ⊆ (p.input (r.assignment i)).support)
    (hold : ∀ j, (D.bundle j).support ⊆ (r.allocation.bundle (r.assignment.symm j)).support)
    (hres : r.state.Represents (transport p r.allocation).residue) :
    RepairResult n C D where
  allocation := transport p r.allocation
  state := r.state
  residue := r.state.represent (transport p r.allocation).residue
  residue_eq := r.state.support_represent hres
  permutation := r.assignment.symm
  addition := addition p r
  addition_subset j := (addition_subset p r hsub j).trans (p.added_subset j 0)
  addition_disjoint j k hjk := by
    apply (r.allocation.disjoint _ _ (r.assignment.symm.injective.ne hjk)).mono
    · rw [addition, Piece.support_diff]; exact Set.sdiff_subset
    · rw [addition, Piece.support_diff]; exact Set.sdiff_subset
  bundle_eq j := by
    change (r.allocation.bundle (r.assignment.symm j)).support = _
    rw [addition, Piece.support_diff]
    exact (Set.union_sdiff_cancel (hold j)).symm

/-- Convert the geometric guarantees to a Repair output; arbitrary invalid
answer branches return the unchanged allocation. -/
def finish (p : Picks D) (r : PermuteResult n p.cake) : RepairResult n C D :=
  if hsub : ∀ i, (r.allocation.bundle i).support ⊆ (p.input (r.assignment i)).support then
    if hold : ∀ j, (D.bundle j).support ⊆ (r.allocation.bundle (r.assignment.symm j)).support then
      if hres : r.state.Represents (transport p r.allocation).residue then
        result p r hsub hold hres
      else RepairResult.unchanged r.state D
    else RepairResult.unchanged r.state D
  else RepairResult.unchanged r.state D

/-- Section 4's `alg:repair`: pooled marks, recorded round robin, and Permute.
All guards are geometric conditions independent of valuations. -/
def protocol (P : PermuteProtocol) : RepairProtocol := fun n hn s C D ε ↦
  let R := s.represent D.residue
  (RepairPartition.run s R ε).bind fun marks ↦
    if hR : R.support = D.residue then
      if hcap : n * (n - 1) ≤ marks.cellCount then
        if hd : ∀ a b, a ≠ b → Disjoint (marks.cells R a).support (marks.cells R b).support then
          if hsub : ∀ a, (marks.cells R a).support ⊆ D.residue then
            let d : Fin marks.cellCount := ⟨0, by
              have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
              omega⟩
            let p := ofRoundRobin marks.state (marks.cells R) (by omega) d hcap hd hsub
            (P n (by omega) marks.state p.cake p.input).map (finish p)
          else .done (RepairResult.unchanged marks.state D)
        else .done (RepairResult.unchanged marks.state D)
      else .done (RepairResult.unchanged marks.state D)
    else .done (RepairResult.unchanged marks.state D)

/-- Section 4, query accounting in `lem:repair main`, without rounding the
real budget `n/ε` up to an integer. -/
theorem query_cost_le (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ((n * (RepairPartition.size n ε - 1) * (n + 1) : ℕ) : ℝ) +
      permuteQueryBound n ≤ (n : ℝ) / ε + coreQueryBound n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : 0 < 1 / (3 * (n : ℝ) * ε) := by positivity
  have hm : 0 < RepairPartition.size n ε := Nat.ceil_pos.mpr hx
  have hceil : (RepairPartition.size n ε : ℝ) < 1 / (3 * (n : ℝ) * ε) + 1 :=
    Nat.ceil_lt_add_one hx.le
  have hsub : ((RepairPartition.size n ε - 1 : ℕ) : ℝ) =
      (RepairPartition.size n ε : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ RepairPartition.size n ε)]; norm_num
  have hcancel : (n : ℝ) * (1 / (3 * (n : ℝ) * ε)) = 1 / (3 * ε) := by
    field_simp
  have hmarks : (n : ℝ) * (RepairPartition.size n ε - 1 : ℕ) < 1 / (3 * ε) := by
    rw [hsub]
    nlinarith
  have hcost : ((n * (RepairPartition.size n ε - 1) * (n + 1) : ℕ) : ℝ) ≤
      (n : ℝ) / ε := by
    push_cast
    have h := mul_lt_mul_of_pos_right hmarks (show 0 < (n : ℝ) + 1 by positivity)
    have hdiv : (1 / (3 * ε)) * ((n : ℝ) + 1) ≤ (n : ℝ) / ε := by
      apply (le_div_iff₀ hε).mpr
      have he : (1 / (3 * ε)) * ε = (1 : ℝ) / 3 := by field_simp
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    exact h.le.trans hdiv
  have hp : permuteQueryBound n ≤ coreQueryBound n :=
    (Nat.le_add_left _ _).trans (CoreAssembly.query_cost_le hn)
  exact add_le_add hcost (by exact_mod_cast hp)

/-- Section 4's `alg:repair` and `lem:repair main`: Repair satisfies its full
inherited-record contract conditional only on `lem:permute`. -/
theorem protocol_correct (P : PermuteProtocol) (hP : P.Correct) :
    (protocol P).Correct := by
  intro n hn s C D ε v hs hC hD hε hεmax hpos halmost
  have hRrep : s.Represents D.residue :=
    (show s.Represents C.support from ⟨C, hC, rfl⟩).diff (s.represents_allocated D hD)
  let R := s.represent D.residue
  have hR : R.support = D.residue := s.support_represent hRrep
  obtain ⟨marks, a, ha, hca, hms, href, hrep, _, hcover, hd, hlo, _, hcount, _, hsmall⟩ :=
    RepairPartition.run_correct hn s R ε v hs (s.compatible_represent _) hε hεmax
      (by simpa only [hR] using hpos)
  have hsize := (RepairPartition.size_bounds n hn ε hε hεmax).2.1
  have hcap : n * (n - 1) ≤ marks.cellCount := by
    nlinarith [Nat.sub_le n 1]
  let d : Fin marks.cellCount := ⟨0, by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    omega⟩
  have g := RepairRoundRobin.correct hn marks.state (marks.cells R) d hcap R v hms
    hrep hd hcover ε hε hεmax hcount (by simpa only [hR] using hpos) hsmall
  have hsub : ∀ c, (marks.cells R c).support ⊆ D.residue := by
    intro c
    rw [← hR, ← hcover]
    exact Set.subset_iUnion_of_subset c Set.Subset.rfl
  let p := ofRoundRobin marks.state (marks.cells R) (by omega) d hcap hd hsub
  have hDm : ∀ j, marks.state.Represents (D.bundle j).support :=
    fun j ↦ href.refines.represents (hD j)
  obtain ⟨z, b, hb, hzs, hzi, hef, hsuffix, hold, hcb⟩ :=
    roundRobin_permute_preserves hn marks.state (marks.cells R) d hcap hd hsub
      R hR ε hε v hpos g halmost P hP hms hDm
  have hzsub : ∀ i, (z.allocation.bundle i).support ⊆ (p.input (z.assignment i)).support := by
    intro i
    obtain ⟨x, _, heq⟩ := hsuffix i
    rw [heq]
    exact Piece.suffix_subset _ _
  have hCz : z.state.Represents C.support :=
    (href.refines.trans hzi.1) C hC
  have hres : z.state.Represents (transport p z.allocation).residue :=
    hCz.diff (z.state.represents_allocated (transport p z.allocation) hzi.2.1)
  let out := result p z hzsub hold hres
  have hfinish : finish p z = out := by
    simp only [finish, dite_eq_left hzsub, dite_eq_left hold, dite_eq_left hres, out]
  refine ⟨out, a + b, ?_, hzs, ?_, hef, ?_, ?_⟩
  · change ((RepairPartition.run s R ε).bind _).Runs v out (a + b)
    apply ha.bind
    dsimp only
    rw [dite_eq_left hR, dite_eq_left hcap, dite_eq_left hd, dite_eq_left hsub]
    simpa only [hfinish] using hb.map (finish p)
  · exact ⟨href.refines.trans hzi.1, hzi.2.1, z.state.compatible_represent _⟩
  · intro i j
    have hZ := addition_subset p z hzsub j
    rw [ofRoundRobin_added] at hZ
    have hbound := RepairRoundRobin.retained_value_le marks.state (marks.cells R)
      (by omega) d hcap hd R ε hε.le (v i) (hsmall i) j (out.addition j) hZ
    simpa only [hR] using hbound
  · have hc := query_cost_le n hn ε hε
    have hcaR : (a : ℝ) ≤ ((n * (RepairPartition.size n ε - 1) * (n + 1) : ℕ) : ℝ) := by
      exact_mod_cast hca
    have hcbR : (b : ℝ) ≤ permuteQueryBound n := by exact_mod_cast hcb
    push_cast
    linarith

end RepairAssembly
end CakeCuttingPsomas
