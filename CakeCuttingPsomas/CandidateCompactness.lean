module

public import CakeCuttingPsomas.CandidateExtension
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Lattice

set_option linter.style.header false

/-! # Some candidate succeeds by compactness

Section 5, proof of `lem:permute`, “Some candidate is envy-free”. Extensions
form a compact box of traversal positions. A failed candidate has strictly
positive minimum extension envy, contradicting arbitrarily accurate extensions
once the minimum is taken over all guesses. These are proof-only constructions.
-/

@[expose] public section
noncomputable section

namespace CakeCuttingPsomas.CandidateCompactness

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- All positions whose suffixes extend the specified suffix family. -/
def extensionBox (P Y : Fin n → Piece) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun r ↦ Set.Icc 0 ((P r).length - (Y r).length))

theorem mem_extensionBox {P Y : Fin n → Piece} {t : Fin n → ℝ} :
    t ∈ extensionBox P Y ↔ ∀ r, t r ∈ Set.Icc 0 ((P r).length - (Y r).length) := by
  change (∀ r ∈ Set.univ, t r ∈ Set.Icc 0 ((P r).length - (Y r).length)) ↔ _
  simp only [Set.mem_univ, forall_const]

theorem isCompact_extensionBox (P Y : Fin n → Piece) : IsCompact (extensionBox P Y) :=
  isCompact_univ_pi fun _ ↦ isCompact_Icc

theorem extensionBox_nonempty {P Y : Fin n → Piece}
    (hY : ∀ r, (Y r).IsSuffix (P r)) : (extensionBox P Y).Nonempty := by
  refine ⟨fun _ ↦ 0, mem_extensionBox.mpr fun r ↦ ⟨le_rfl, ?_⟩⟩
  exact (hY r).position_mem.1

theorem box_suffix_extension {P Y : Fin n → Piece}
    (hY : ∀ r, (Y r).IsSuffix (P r)) {t : Fin n → ℝ}
    (ht : t ∈ extensionBox P Y) :
    (∀ r, ((P r).suffixAt (t r)).IsSuffix (P r)) ∧
      (∀ r, (Y r).support ⊆ ((P r).suffixAt (t r)).support) := by
  have hm := mem_extensionBox.mp ht
  have hp r : t r ∈ Set.Icc 0 (P r).length :=
    ⟨(hm r).1, (hm r).2.trans (hY r).position_mem.2⟩
  refine ⟨fun r ↦ (P r).suffix_isSuffix (hp r), fun r ↦ ?_⟩
  rw [(hY r).eq_suffixAt_length_sub_length]
  exact (P r).suffix_antitone (hm r).2

theorem extension_coordinates {P Y Z : Fin n → Piece}
    (hY : ∀ r, (Y r).IsSuffix (P r)) (hZ : ∀ r, (Z r).IsSuffix (P r))
    (hext : ∀ r, (Y r).support ⊆ (Z r).support) :
    ∃ t ∈ extensionBox P Y, ∀ r, Z r = (P r).suffixAt (t r) := by
  refine ⟨fun r ↦ (P r).length - (Z r).length, mem_extensionBox.mpr ?_,
    fun r ↦ (hZ r).eq_suffixAt_length_sub_length⟩
  intro r
  refine ⟨(hZ r).position_mem.1, ?_⟩
  apply ((P r).suffix_subset_suffix_iff (hZ r).position_mem (hY r).position_mem).mp
  simpa only [← (hY r).eq_suffixAt_length_sub_length,
    ← (hZ r).eq_suffixAt_length_sub_length] using hext r

/-- The paper's maximum envy, including the zero diagonal terms. -/
def maxEnvy (hn : 0 < n) (v : Fin n → Valuation) (Z : Fin n → Piece) : ℝ :=
  (Finset.univ : Finset (Fin n × Fin n)).sup'
    ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
    (fun p ↦ (v p.1).value (Z p.2).support - (v p.1).value (Z p.1).support)

theorem maxEnvy_le_iff (hn : 0 < n) (v : Fin n → Valuation) (Z : Fin n → Piece)
    (δ : ℝ) : maxEnvy hn v Z ≤ δ ↔
      ∀ s r, (v s).value (Z r).support ≤ (v s).value (Z s).support + δ := by
  unfold maxEnvy
  erw [Finset.sup'_le_iff]
  simp only [Finset.mem_univ, true_implies, Prod.forall, sub_le_iff_le_add, add_comm δ]

theorem maxEnvy_nonneg (hn : 0 < n) (v : Fin n → Valuation) (Z : Fin n → Piece) :
    0 ≤ maxEnvy hn v Z := by
  have h := (maxEnvy_le_iff hn v Z (maxEnvy hn v Z)).mp le_rfl ⟨0, hn⟩ ⟨0, hn⟩
  linarith

theorem maxEnvy_eq_zero_iff (hn : 0 < n) (v : Fin n → Valuation)
    (Z : Fin n → Piece) : maxEnvy hn v Z = 0 ↔
      ∀ s r, (v s).value (Z r).support ≤ (v s).value (Z s).support := by
  constructor
  · intro h
    simpa only [add_zero] using (maxEnvy_le_iff hn v Z 0).mp h.le
  · intro h
    apply le_antisymm _ (maxEnvy_nonneg hn v Z)
    exact (maxEnvy_le_iff hn v Z 0).mpr (by simpa only [add_zero] using h)

/-- Section 5, `lem:permute`, “Some candidate is envy-free”: maximum envy
varies continuously with the vector of suffix traversal positions. -/
theorem continuous_maxEnvy (hn : 0 < n) (v : Fin n → Valuation) (P : Fin n → Piece) :
    Continuous (fun t : Fin n → ℝ ↦ maxEnvy hn v (fun r ↦ (P r).suffixAt (t r))) := by
  apply Continuous.finset_sup'_apply
  intro p _
  exact ((v p.1).continuous_value_suffix (P p.2) |>.comp (continuous_apply p.2)).sub
    ((v p.1).continuous_value_suffix (P p.1) |>.comp (continuous_apply p.1))

/-- Section 5, `lem:permute`, “Some candidate is envy-free”: a failed
candidate has strictly positive minimum envy among all its suffix extensions. -/
theorem exists_positive_extension_bound (hn : 0 < n) {v : Fin n → Valuation}
    {P Y : Fin n → Piece} (hY : IsCandidate v P Y)
    (hfail : ¬ ∀ s r, (v s).value (Y r).support ≤ (v s).value (Y s).support) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ Z : Fin n → Piece,
      (∀ r, (Z r).IsSuffix (P r)) →
      (∀ r, (Y r).support ⊆ (Z r).support) → γ ≤ maxEnvy hn v Z := by
  obtain ⟨t, ht, hmin⟩ := (isCompact_extensionBox P Y).exists_isMinOn
    (extensionBox_nonempty hY.suffix) (continuous_maxEnvy hn v P).continuousOn
  have hext := box_suffix_extension hY.suffix ht
  have hpos : 0 < maxEnvy hn v (fun r ↦ (P r).suffixAt (t r)) := by
    apply lt_of_le_of_ne (maxEnvy_nonneg hn v _)
    intro he
    have hef := (maxEnvy_eq_zero_iff hn v _).mp he.symm
    have heq := hY.extension_eq hext.1 hext.2 hef
    apply hfail
    intro s r
    simpa only [heq] using hef s r
  refine ⟨_, hpos, fun Z hZ hext ↦ ?_⟩
  obtain ⟨u, hu, heq⟩ := extension_coordinates hY.suffix hZ hext
  have hle : maxEnvy hn v (fun r ↦ (P r).suffixAt (t r)) ≤
      maxEnvy hn v (fun r ↦ (P r).suffixAt (u r)) := hmin hu
  simpa only [← heq] using hle

end CakeCuttingPsomas.CandidateCompactness

namespace CakeCuttingPsomas.CandidateConstruction

/-- Section 5, `lem:permute`, “Some candidate is envy-free”: among the finitely
many pairs of agent and input-label orders, some mathematical candidate is
envy-free. Compactness gives a common positive envy bound if all guesses fail,
contradicting the approximate extensions of `exists_candidate_delta_extension`.
No normalization, positive values, or nonempty-agent assumptions are needed. -/
theorem exists_envyFree_guess {n : ℕ} (v : Fin n → Valuation) (C : Piece)
    (P : Fin n → Piece)
    (hdis : ∀ j k, j ≠ k → Disjoint (P j).support (P k).support)
    (hcover : (⋃ j, (P j).support) = C.support) :
    ∃ agents pieces : Equiv.Perm (Fin n),
      let Y := candidate (v ∘ agents) (P ∘ pieces)
      ∀ s r, (v (agents s)).value (Y r).support ≤ (v (agents s)).value (Y s).support := by
  classical
  by_cases hn : 0 < n
  · by_contra hfail
    let Guess := Equiv.Perm (Fin n) × Equiv.Perm (Fin n)
    let Y (g : Guess) := candidate (v ∘ g.1) (P ∘ g.2)
    have hb : ∀ g : Guess, ∃ γ : ℝ, 0 < γ ∧ ∀ Z : Fin n → Piece,
        (∀ r, (Z r).IsSuffix (P (g.2 r))) →
        (∀ r, (Y g r).support ⊆ (Z r).support) →
        γ ≤ CandidateCompactness.maxEnvy hn (v ∘ g.1) Z := by
      intro g
      apply CandidateCompactness.exists_positive_extension_bound hn (candidate_spec _ _)
      intro hef
      exact hfail ⟨g.1, g.2, hef⟩
    choose γ hγ hbound using hb
    let γmin := (Finset.univ : Finset Guess).inf' Finset.univ_nonempty γ
    have hpos : 0 < γmin := (Finset.lt_inf'_iff _).mpr (fun g _ ↦ hγ g)
    obtain ⟨agents, pieces, W, A, hW, hsuffix, hext, hδ⟩ :=
      EnvyCycle.exists_candidate_delta_extension v C P hdis hcover (γmin / 2) (by positivity)
    let g : Guess := (agents, pieces)
    have hsame : ∀ r, (Y g r).support = (W r).support :=
      (candidate_spec (v ∘ agents) (P ∘ pieces)).support_unique hW
        (fun _ ↦ Piece.SameTraversal.refl _)
    have hext' : ∀ r, (Y g r).support ⊆ (A.bundle (agents r)).support := by
      intro r
      rw [hsame r]
      exact hext r
    have hlower := hbound g (fun r ↦ A.bundle (agents r)) hsuffix hext'
    have hupper : CandidateCompactness.maxEnvy hn (v ∘ agents)
        (fun r ↦ A.bundle (agents r)) ≤ γmin / 2 :=
      (CandidateCompactness.maxEnvy_le_iff hn _ _ _).mpr
        (fun s r ↦ hδ (agents s) (agents r))
    have hminle : γmin ≤ γ g := Finset.inf'_le γ (Finset.mem_univ g)
    change γ g ≤ CandidateCompactness.maxEnvy hn (v ∘ agents)
      (fun r ↦ A.bundle (agents r)) at hlower
    linarith
  · have he : n = 0 := by omega
    subst n
    exact ⟨Equiv.refl _, Equiv.refl _, fun s ↦ Fin.elim0 s⟩

end CakeCuttingPsomas.CandidateConstruction
