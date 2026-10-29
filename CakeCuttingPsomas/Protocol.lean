module

public import CakeCuttingPsomas.Basic

/-! # Robertson–Webb queries and their execution semantics -/

@[expose] public section

namespace CakeCuttingPsomas

/-- The only ways a protocol can ask for valuation information. -/
inductive RWQuery (n : ℕ) where
  | eval (agent : Fin n) (left right : ℝ)
  | cut (agent : Fin n) (left target : ℝ)

/-- A legal query and its correct answer, following the introduction.
Closed intervals give the same values as the paper's half-open intervals because
the valuations are integrable densities. A cut must return the smallest answer. -/
def RWQuery.AnswerValid {n : ℕ} (v : Fin n → Valuation) : RWQuery n → ℝ → Prop
  | .eval i a b, answer =>
      0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ answer = (v i).value (Set.Icc a b)
  | .cut i a target, answer =>
      0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ target ∧ target ≤ (v i).value (Set.Icc a 1) ∧
      a ≤ answer ∧ answer ≤ 1 ∧ (v i).value (Set.Icc a answer) = target ∧
      ∀ y, a ≤ y → y ≤ 1 → (v i).value (Set.Icc a y) = target → answer ≤ y

/-- An abstract query protocol. Each next query or output depends only on the
answers already received. As in the Robertson–Webb model, internal computation
is not charged; this type does not assert machine computability. -/
inductive RWProtocol (n : ℕ) (α : Type) where
  | done (result : α)
  | ask (query : RWQuery n) (next : ℝ → RWProtocol n α)

/-- A terminating execution with legal queries and correct answers.
Every `ask` costs one query; producing the final result costs zero. -/
inductive RWProtocol.Runs {n : ℕ} {α : Type} (v : Fin n → Valuation) :
    RWProtocol n α → α → ℕ → Prop where
  | done (result : α) : Runs v (.done result) result 0
  | ask {query : RWQuery n} {next : ℝ → RWProtocol n α}
      {answer : ℝ} {result : α} {count : ℕ}
      (valid : query.AnswerValid v answer)
      (rest : Runs v (next answer) result count) :
      Runs v (.ask query next) result (count + 1)

namespace RWQuery

/-- Legal answers are unique, including flat regions: Cut selects the smallest point. -/
theorem AnswerValid.unique {n : ℕ} {v : Fin n → Valuation} {q : RWQuery n}
    {a b : ℝ} (ha : q.AnswerValid v a) (hb : q.AnswerValid v b) : a = b := by
  cases q with
  | eval i l r => exact ha.2.2.2.trans hb.2.2.2.symm
  | cut i l t =>
    obtain ⟨_, _, _, _, hal, har, hav, ham⟩ := ha
    obtain ⟨_, _, _, _, hbl, hbr, hbv, hbm⟩ := hb
    exact le_antisymm (ham b hbl hbr hbv) (hbm a hal har hav)

/-- Relabel participating agents without changing the requested information. -/
def relabel {m n : ℕ} (f : Fin m → Fin n) : RWQuery m → RWQuery n
  | .eval i a b => .eval (f i) a b
  | .cut i a t => .cut (f i) a t

@[simp]
theorem answerValid_relabel {m n : ℕ} (v : Fin n → Valuation)
    (f : Fin m → Fin n) (q : RWQuery m) (a : ℝ) :
    (q.relabel f).AnswerValid v a ↔ q.AnswerValid (v ∘ f) a := by
  cases q <;> rfl

end RWQuery

namespace RWProtocol

/-- A protocol's legal executions have the same result and exact query count. -/
theorem Runs.unique {n : ℕ} {α : Type} {v : Fin n → Valuation}
    {p : RWProtocol n α} {a b : α} {c d : ℕ}
    (ha : p.Runs v a c) (hb : p.Runs v b d) : a = b ∧ c = d := by
  induction ha generalizing b d with
  | done a => cases hb; exact ⟨rfl, rfl⟩
  | @ask q next answer result count valid rest ih =>
    cases hb with
    | ask valid' rest' =>
      obtain rfl := valid.unique valid'
      obtain ⟨hr, hc⟩ := ih rest'
      exact ⟨hr, congrArg (· + 1) hc⟩

/-- Sequence protocols; the continuation uses only the first protocol's result. -/
def bind {n : ℕ} {α β : Type} : RWProtocol n α → (α → RWProtocol n β) → RWProtocol n β
  | .done a, f => f a
  | .ask q k, f => .ask q (fun a ↦ (k a).bind f)

/-- Apply free internal computation to a protocol's result. -/
def map {n : ℕ} {α β : Type} (f : α → β) (p : RWProtocol n α) : RWProtocol n β :=
  p.bind (fun a ↦ .done (f a))

/-- Run a subprotocol on the indicated agents of a larger profile.
For Section 2's recursive calls use the inclusion induced by `Fin m ≃ E`. -/
def relabel {m n : ℕ} {α : Type} (f : Fin m → Fin n) :
    RWProtocol m α → RWProtocol n α
  | .done a => .done a
  | .ask q k => .ask (q.relabel f) (fun a ↦ (k a).relabel f)

@[simp]
theorem bind_done {n : ℕ} {α : Type} (p : RWProtocol n α) : p.bind .done = p := by
  induction p with
  | done a => rfl
  | ask q k ih => simp only [bind]; exact congrArg (ask q) (funext ih)

theorem bind_assoc {n : ℕ} {α β γ : Type} (p : RWProtocol n α)
    (f : α → RWProtocol n β) (g : β → RWProtocol n γ) :
    (p.bind f).bind g = p.bind (fun a ↦ (f a).bind g) := by
  induction p with
  | done a => rfl
  | ask q k ih => simp only [bind]; exact congrArg (ask q) (funext ih)

/-- Sequencing adds the actual query counts of the executions. -/
theorem Runs.bind {n : ℕ} {α β : Type} {v : Fin n → Valuation}
    {p : RWProtocol n α} {f : α → RWProtocol n β} {a : α} {b : β} {c d : ℕ}
    (hp : p.Runs v a c) (hf : (f a).Runs v b d) :
    (p.bind f).Runs v b (c + d) := by
  induction hp with
  | done => simpa [RWProtocol.bind] using hf
  | @ask query next answer result count valid rest ih =>
    have h := Runs.ask (next := fun x ↦ (next x).bind f) valid (ih hf)
    simpa only [RWProtocol.bind, Nat.add_assoc, Nat.add_right_comm, Nat.add_comm] using h

/-- Every execution of a sequence splits into executions with additive counts. -/
theorem runs_bind_iff {n : ℕ} {α β : Type} {v : Fin n → Valuation}
    (p : RWProtocol n α) (f : α → RWProtocol n β) (b : β) (c : ℕ) :
    (p.bind f).Runs v b c ↔
      ∃ a s t, p.Runs v a s ∧ (f a).Runs v b t ∧ c = s + t := by
  constructor
  · induction p generalizing c with
    | done a => intro h; exact ⟨a, 0, c, .done a, h, by simp⟩
    | ask q k ih =>
      intro h
      cases h with
      | ask valid rest =>
        obtain ⟨a, s, t, hs, ht, hc⟩ := ih _ _ rest
        exact ⟨a, s + 1, t, .ask valid hs, ht, by omega⟩
  · rintro ⟨a, s, t, hs, ht, rfl⟩
    exact hs.bind ht

/-- Result computation costs no queries. -/
theorem Runs.map {n : ℕ} {α β : Type} {v : Fin n → Valuation}
    {p : RWProtocol n α} {a : α} {c : ℕ} (h : p.Runs v a c) (f : α → β) :
    (p.map f).Runs v (f a) c := by
  simpa [RWProtocol.map] using h.bind (f := fun x ↦ .done (f x)) (Runs.done (v := v) (f a))

/-- Agent relabeling preserves executions and their exact query counts. -/
theorem runs_relabel_iff {m n : ℕ} {α : Type} (v : Fin n → Valuation)
    (f : Fin m → Fin n) (p : RWProtocol m α) (a : α) (c : ℕ) :
    (p.relabel f).Runs v a c ↔ p.Runs (v ∘ f) a c := by
  induction p generalizing c with
  | done b => constructor <;> intro h <;> cases h <;> constructor
  | ask q k ih =>
    constructor
    · intro h
      cases h with
      | ask valid rest =>
        exact .ask ((q.answerValid_relabel v f _).mp valid) ((ih _ _).mp rest)
    · intro h
      cases h with
      | ask valid rest =>
        exact .ask ((q.answerValid_relabel v f _).mpr valid) ((ih _ _).mpr rest)

/-- Mapping changes only the result, retaining the exact execution count. -/
theorem runs_map_iff {n : ℕ} {α β : Type} (v : Fin n → Valuation)
    (f : α → β) (p : RWProtocol n α) (b : β) (c : ℕ) :
    (p.map f).Runs v b c ↔ ∃ a, p.Runs v a c ∧ f a = b := by
  rw [RWProtocol.map, runs_bind_iff]
  constructor
  · rintro ⟨a, s, t, hp, hf, hc⟩
    cases hf
    exact ⟨a, by simpa only [hc, Nat.add_zero] using hp, rfl⟩
  · rintro ⟨a, hp, rfl⟩
    exact ⟨a, c, 0, hp, .done _, by omega⟩

/-- Embed a subroutine execution in the original agent profile at no query cost. -/
theorem Runs.relabel {m n : ℕ} {α : Type} {v : Fin n → Valuation}
    {f : Fin m → Fin n} {p : RWProtocol m α} {a : α} {c : ℕ}
    (h : p.Runs (v ∘ f) a c) : (p.relabel f).Runs v a c :=
  (runs_relabel_iff v f p a c).mpr h

/-- Relabeling a sequence is the sequence of its relabeled subroutines. -/
theorem relabel_bind {m n : ℕ} {α β : Type} (f : Fin m → Fin n)
    (p : RWProtocol m α) (k : α → RWProtocol m β) :
    (p.bind k).relabel f = (p.relabel f).bind (fun a ↦ (k a).relabel f) := by
  induction p with
  | done a => rfl
  | ask q next ih =>
    simp only [bind, relabel]
    exact congrArg (ask (q.relabel f)) (funext ih)

end RWProtocol

end CakeCuttingPsomas
