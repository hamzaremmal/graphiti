/-
Copyright (c) 2025-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas
import Graphiti.Projects.Flushability.DeterministicModule
import Graphiti.Projects.Flushability.RuleSwapping
import Graphiti.Projects.Flushability.ModuleProperties
import Mathlib.Tactic

namespace Graphiti

variable {Ident S: Type _}
variable [DecidableEq Ident]
variable (mod: Module Ident S)

section Confluence

class DiamondConfluent: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂ → (mod.inputs.getIO ident).snd s₁ v s₃
    → ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄
  internals: ∀ s₁ s₂ s₃, ∀ r₁ ∈ mod.internals, ∀ r₂ ∈ mod.internals,
    r₁ s₁ s₂ → r₂ s₁ s₃
    → ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂ → (mod.outputs.getIO ident).snd s₁ v s₃
    → ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄

class StronglyConfluent: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂ → (mod.inputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, (existSR mod.internals s₂ s₄ ∧ ∃ r ∈ mod.internals, r s₃ s₄)
          ∨ (existSR mod.internals s₃ s₄ ∧ ∃ r ∈ mod.internals, r s₂ s₄)
  internals: ∀ s₁ s₂ s₃, ∀ r₁ ∈ mod.internals, ∀ r₂ ∈ mod.internals,
    r₁ s₁ s₂
    → r₂ s₁ s₃
    → ∃ s₄, (existSR mod.internals s₂ s₄ ∧ ∃ r ∈ mod.internals, r s₃ s₄)
          ∨ (existSR mod.internals s₃ s₄ ∧ ∃ r ∈ mod.internals, r s₂ s₄)
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂ → (mod.outputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, (existSR mod.internals s₂ s₄ ∧ ∃ r ∈ mod.internals, r s₃ s₄)
          ∨ (existSR mod.internals s₃ s₄ ∧ ∃ r ∈ mod.internals, r s₂ s₄)

---------------------------------------------------------------------------------------------------
---------------------------------------- GLOBAL-CONFLUENCE ----------------------------------------
---------------------------------------------------------------------------------------------------

class InternallyGlobalyConfluent: Prop where
  internals: ∀ s₁ s₂ s₃,
    existSR mod.internals s₁ s₂ → existSR mod.internals s₁ s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄

class GloballyConfluent: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂ → (mod.inputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  internals: ∀ s₁ s₂ s₃,
    existSR mod.internals s₁ s₂ → existSR mod.internals s₁ s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂ → (mod.outputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄

---------------------------------------------------------------------------------------------------
---------------------------------------- QUASI-CONFLUENCE -----------------------------------------
---------------------------------------------------------------------------------------------------

class InternallyQuasiConfluent: Prop where
  internals: ∀ s₁ s₂ s₃, ∀ r ∈ mod.internals,
    r s₁ s₂ → existSR mod.internals s₁ s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄

class QuasiConfluent: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂ → (mod.inputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  internals: ∀ s₁ s₂ s₃, ∀ r ∈ mod.internals,
    r s₁ s₂ → existSR mod.internals s₁ s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂ → (mod.outputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄

class LocallyConfluent: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂ → (mod.inputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  internals: ∀ s₁ s₂ s₃, ∀ r₁ ∈ mod.internals, ∀ r₂ ∈ mod.internals,
    r₁ s₁ s₂ → r₂ s₁ s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂ → (mod.outputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄

end Confluence

section ConfluenceDerivation

instance diamond_is_strong [dm: DiamondConfluent mod] : StronglyConfluent mod :=
by
  constructor
  . intros _ _ _ s₂ s₃ _ _
    have: ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄ := by
      apply dm.inputs <;> assumption
    obtain ⟨r₃, _, r₄, _, s₄, _, _⟩ := this
    use s₄
    left <;> and_intros
    . apply existSR_single_step _ _ _ r₃ <;> assumption
    . use r₄
  . intros _ s₂ s₃ r₁ _ r₂ _ _ _
    have: ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄ := by
      apply dm.internals _ s₂ s₃ r₁ _ r₂ <;> assumption
    obtain ⟨r₃, _, r₄, _, s₄, _, _⟩ := this
    use s₄
    left <;> and_intros
    . apply existSR_single_step _ _ _ r₃ <;> assumption
    . use r₄
  . intros _ _ _ s₂ s₃ _ _
    have: ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄ := by
      apply dm.outputs <;> assumption
    obtain ⟨r₃, _, r₄, _, s₄, _, _⟩ := this
    use s₄
    left <;> and_intros
    . apply existSR_single_step _ _ _ r₃ <;> assumption
    . use r₄

instance strong_is_global [sc: StronglyConfluent mod] : GloballyConfluent mod :=
by
  constructor
  . intros _ s₁ _ s₂ s₃ _ _
    have: ∃ s₄, (existSR mod.internals s₂ s₄ ∧ ∃ r ∈ mod.internals, r s₃ s₄) ∨ (existSR mod.internals s₃ s₄ ∧ ∃ r ∈ mod.internals, r s₂ s₄) := by
      apply sc.inputs <;> assumption
    obtain ⟨s₄, h⟩ := this <;> use s₄
    rcases h with h | h <;> obtain ⟨_, _⟩ := h
    . and_intros
      . assumption
      . apply existSR_single_step' <;> assumption
    . and_intros
      . apply existSR_single_step' <;> assumption
      . assumption
  . intro s₁ s₂ s₃ h₁ h₂
    induction h₁ generalizing s₃ with
    | done =>
      use s₃ <;> and_intros
      . exact h₂
      . exact existSR_reflexive
    | step init₁ mid₁ final₁ r₁ _ h₁ _ ih₁ =>
      induction h₂ generalizing s₁ s₂ mid₁ final₁ r₁ with
      | done init =>
        use final₁ <;> and_intros
        . exact existSR_reflexive
        . apply existSR_transitive _ _ mid₁ _
          . apply existSR_single_step <;> assumption
          . assumption
      | step i₁ i₂ i₃ r₂ _ _ _ ih₂ =>
        have ⟨s₅, h⟩ := sc.internals i₁ mid₁ i₂ r₁ (by assumption) r₂ (by assumption) (by assumption) (by assumption)
        cases h with
        | inl h =>
          obtain ⟨_, ⟨r, _, _⟩⟩ := h
          have ⟨s₆, _, _⟩ := ih₁ s₅ (by assumption)
          have: ∀ (s₃ : S), existSR mod.internals s₅ s₃ → ∃ s₄, existSR mod.internals s₆ s₄ ∧ existSR mod.internals s₃ s₄ := by
            intro ss hhh
            have: existSR mod.internals mid₁ ss := by sorry
            specialize ih₁ ss this
            obtain ⟨sss, _, _⟩ := ih₁
            use ss <;> and_intros
            . sorry
            . sorry
          specialize ih₂ s₁ s₂ s₅ final₁ r (by assumption) (by assumption)
          sorry
        | inr h =>
          sorry
  . intros _ s₁ _ s₂ s₃ _ _
    have: ∃ s₄, (existSR mod.internals s₂ s₄ ∧ ∃ r ∈ mod.internals, r s₃ s₄) ∨ (existSR mod.internals s₃ s₄ ∧ ∃ r ∈ mod.internals, r s₂ s₄) := by
      apply sc.outputs <;> assumption
    obtain ⟨s₄, h⟩ := this <;> use s₄
    rcases h with h | h <;> obtain ⟨_, _⟩ := h
    . and_intros
      . assumption
      . apply existSR_single_step' <;> assumption
    . and_intros
      . apply existSR_single_step' <;> assumption
      . assumption

instance global_is_quasi [gc: GloballyConfluent mod] : QuasiConfluent mod :=
by
  constructor
  . exact gc.inputs
  . intros s₁ s₂ s₃ r₁ _ _ h
    cases h with
    | done =>
      use s₂ <;> and_intros
      . apply existSR_reflexive
      . apply existSR_single_step <;> assumption
    | step  _ mid =>
      have: existSR mod.internals s₁ s₃ := by
        have: existSR mod.internals s₁ mid := by
          apply existSR_single_step <;> assumption
        apply existSR_transitive <;> assumption
      have: existSR mod.internals s₁ s₂ := by
        apply existSR_single_step _ _ _ r₁ <;> assumption
      apply gc.internals <;> assumption
  . exact gc.outputs

instance quasi_is_local [qc: QuasiConfluent mod] : LocallyConfluent mod :=
by
  constructor
  . exact qc.inputs
  . intros s₁ _ s₃ r₁ _ _ _ _ _
    have: existSR mod.internals s₁ s₃ := by
      apply existSR_single_step <;> assumption
    apply qc.internals _ _ _ r₁ <;> assumption
  . exact qc.outputs

end ConfluenceDerivation

section Determinism

private theorem bla {α : Type _} {a c : α} (b : List α) :
  a ∈ b → c ∈ b → b.length = 1 → a = c :=
by
  intros <;> cases b with
  | nil => exfalso; contradiction
  | cons x xs => grind

instance [dm: Deterministic mod] [sr: SingleInternal mod]: GloballyConfluent mod := {
  inputs    := by
    intros _ _ _ s₂ s₃ _ _
    use s₂
    and_intros
    . exact existSR_reflexive
    . have: s₂ = s₃ := by apply dm.input_deterministic <;> assumption
      subst this
      exact existSR_reflexive
  internals := by
    intros s₁ s₂ s₃ h₁ h₂
    induction h₁ with
    | done =>
      use s₃ <;> and_intros
      . exact h₂
      . exact existSR_reflexive
    | step init mid final rule hᵣ _ h₁ ih =>
      cases h₂ with
      | done =>
        use final <;> and_intros
        . exact existSR_reflexive
        . apply existSR_transitive mod.internals _ mid _
          . apply existSR_single_step <;> assumption
          . exact h₁
      | step _ mid' _ rule' hᵣ' _ h₂ =>
        have: rule = rule' := bla mod.internals hᵣ hᵣ' sr.prop
        subst this
        have: mid = mid' := by apply dm.internal_deterministic rule hᵣ init mid mid' _ _ <;> assumption
        subst this
        exact ih h₂
  outputs   := by
    intros _ _ _ s₂ s₃ _ _
    use s₂ <;> and_intros
    . exact existSR_reflexive
    . have: s₂ = s₃ := by apply dm.output_deterministic <;> assumption
      subst this
      exact existSR_reflexive
}

-- TODO: Maybe even quasi-confluent here?
instance [dm: Deterministic mod] [sr: SwapDistinctRules mod]: LocallyConfluent mod where
  inputs := by
    intros _ _ _ s₂ s₃ _ _
    use s₂
    and_intros
    . exact existSR_reflexive
    . have: s₂ = s₃ := by apply dm.input_deterministic <;> assumption
      subst this
      exact existSR_reflexive
  internals := by
    intro s₁ s₂ s₃ r₁ hr₁ r₂ hr₂ h₁ h₂
    by_cases h: r₁ = r₂
    . subst h
      have: s₂ = s₃ := by apply dm.internal_deterministic <;> assumption
      subst this
      refine ⟨s₂, existSR_reflexive, existSR_reflexive⟩
    . have ⟨s₄, _, _⟩ := sr.swap r₁ hr₁ r₂ hr₂ s₁ s₂ s₃ h h₁ h₂
      use s₄ <;> and_intros
      . apply existSR_single_step _ _ _ r₂ <;> assumption
      . apply existSR_single_step _ _ _ r₁ <;> assumption
  outputs := by
    intros _ _ _ s₂ s₃ _ _
    use s₂ <;> and_intros
    . exact existSR_reflexive
    . have: s₂ = s₃ := by apply dm.output_deterministic <;> assumption
      subst this
      exact existSR_reflexive


end Determinism

end Graphiti
