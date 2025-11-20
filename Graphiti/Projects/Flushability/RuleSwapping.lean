/-
Copyright (c) 2025-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Mathlib.Tactic

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas

namespace Graphiti

variable {Ident S : Type _}

variable (mod: Module Ident S)
variable [DecidableEq Ident]

class DistinctActionStronglySwaps': Prop where
  inputs: ∀ ident₁ ident₂ s₁ v₂ (s': (mod.inputs.getIO ident₁).fst → S) s₃,
    ident₁ ≠ ident₂ →
    (∀ v₁, (mod.inputs.getIO ident₁).snd s₁ v₁ (s' v₁)) →
    (mod.inputs.getIO ident₂).snd s₁ v₂ s₃ →
    ∃ s'': (mod.inputs.getIO ident₁).fst → S, ∀ v₁, (mod.inputs.getIO ident₂).snd (s' v₁) v₂ (s'' v₁) ∧ (mod.inputs.getIO ident₁).snd s₃ v₁ (s'' v₁)
  in_out: ∀ ident₁ ident₂ s₁ v₂ (s': (mod.inputs.getIO ident₁).fst → S) s₃,
    (∀ v₁, (mod.inputs.getIO ident₁).snd s₁ v₁ (s' v₁)) →
    (mod.outputs.getIO ident₂).snd s₁ v₂ s₃ →
    ∃ s'': (mod.inputs.getIO ident₁).fst → S, ∀ v₁, (mod.inputs.getIO ident₁).snd s₃ v₁ (s'' v₁) ∧ (mod.outputs.getIO ident₂).snd (s' v₁) v₂ (s'' v₁)
  in_int: ∀ ident s₁ (s': (mod.inputs.getIO ident).fst → S) s₃, ∀ rule ∈ mod.internals,
    (∀ v₁, (mod.inputs.getIO ident).snd s₁ v₁ (s' v₁)) →
    rule s₁ s₃ →
    ∃ s'': (mod.inputs.getIO ident).fst → S, ∀ (v : (mod.inputs.getIO ident).fst), (mod.inputs.getIO ident).snd s₃ v (s'' v) ∧ rule (s' v) (s'' v)

-- TODO: DEFINE MY OWN CUSTOM THING SKOLEMIZED...
class DistinctActionSwaps': Prop where
  inputs: ∀ ident₁ ident₂ s₁ v₂ (s': (mod.inputs.getIO ident₁).fst → S) s₃,
    ident₁ ≠ ident₂ →
    (∀ v₁, (mod.inputs.getIO ident₁).snd s₁ v₁ (s' v₁)) →
    (mod.inputs.getIO ident₂).snd s₁ v₂ s₃ →
    ∃ s'': (mod.inputs.getIO ident₁).fst → S, ∀ v₁, (mod.inputs.getIO ident₂).snd (s' v₁) v₂ (s'' v₁) ∧ (mod.inputs.getIO ident₁).snd s₃ v₁ (s'' v₁)
  /-outputs: ∀ ident₁ ident₂ s₁ v₂ (s': (mod.outputs.getIO ident₁).fst → S) s₃,
    ident₁ ≠ ident₂ →
    (∀ v₁, (mod.outputs.getIO ident₁).snd s₁ v₁ (s' v₁)) →
    (mod.outputs.getIO ident₂).snd s₁ v₂ s₃ →
    ∃ s'': (mod.outputs.getIO ident₁).fst → S, ∀ v₁, (mod.outputs.getIO ident₂).snd (s' v₁) v₂ (s'' v₁) ∧ (mod.outputs.getIO ident₁).snd s₃ v₁ (s'' v₁)-/
  in_out: ∀ ident₁ ident₂ s₁ v₂ (s': (mod.inputs.getIO ident₁).fst → S) s₃,
    (∀ v₁, (mod.inputs.getIO ident₁).snd s₁ v₁ (s' v₁)) →
    (mod.outputs.getIO ident₂).snd s₁ v₂ s₃ →
    ∃ s'': (mod.inputs.getIO ident₁).fst → S, ∀ v₁, (mod.inputs.getIO ident₁).snd s₃ v₁ (s'' v₁) ∧ (mod.outputs.getIO ident₂).snd (s' v₁) v₂ (s'' v₁)
  /-out_in: ∀ ident₁ ident₂ s₁ v₂ (s': (mod.outputs.getIO ident₁).fst → S) s₃,
    (∀ v₁, (mod.outputs.getIO ident₁).snd s₁ v₁ (s' v₁)) →
    (mod.inputs.getIO ident₂).snd s₁ v₂ s₃ →
    ∃ s'': (mod.outputs.getIO ident₁).fst → S, ∀ v₁, (mod.outputs.getIO ident₁).snd s₃ v₁ (s'' v₁) ∧ (mod.inputs.getIO ident₂).snd (s' v₁) v₂ (s'' v₁)-/
  in_int: ∀ ident s₁ (s': (mod.inputs.getIO ident).fst → S) s₃,
    (∀ v₁, (mod.inputs.getIO ident).snd s₁ v₁ (s' v₁)) →
    existSR mod.internals s₁ s₃ →
    ∃ s'': (mod.inputs.getIO ident).fst → S, ∀ (v : (mod.inputs.getIO ident).fst), (mod.inputs.getIO ident).snd s₃ v (s'' v) ∧ existSR mod.internals (s' v) (s'' v)
  /-out_int: ∀ ident s₁ (s': (mod.outputs.getIO ident).fst → S) s₃,
    (∀ v₁, (mod.outputs.getIO ident).snd s₁ v₁ (s' v₁)) →
    existSR mod.internals s₁ s₃ →
    ∃ s'': (mod.outputs.getIO ident).fst → S, ∀ (v : (mod.outputs.getIO ident).fst), (mod.outputs.getIO ident).snd s₃ v (s'' v) ∧ existSR mod.internals (s' v) (s'' v)-/

instance [dass: DistinctActionStronglySwaps' mod]: DistinctActionSwaps' mod where
  inputs := dass.inputs
  in_out := dass.in_out
  in_int := by
    intro ident s₁ s' s₃ h₁ h₂
    induction h₂ generalizing s' with
    | done =>
      use s'
      intro v <;> specialize h₁ v
      refine ⟨h₁, existSR_reflexive⟩
    | step init mid final rule _ h₂ h₃ ih =>
      have ⟨s'', h⟩ := dass.in_int ident init s' mid rule (by assumption) h₁ h₂
      rewrite [forall_and] at h <;> obtain ⟨h, h''⟩ := h
      specialize ih s'' h
      obtain ⟨s''', h⟩  := ih
      use s'''
      intro v <;> specialize h v
      obtain ⟨_, _⟩ := h
      and_intros
      . assumption
      . specialize h'' v
        apply existSR_transitive _ _ (s'' v)
        . apply existSR_single_step <;> assumption
        . assumption

class SwapDistinctRules: Prop where
  swap: ∀ rule₁ ∈ mod.internals, ∀ rule₂ ∈ mod.internals, ∀ s₁ s₂ s₃,
    rule₁ ≠ rule₂ →
    rule₁ s₁ s₂ →
    rule₂ s₁ s₃ →
    ∃ s₄, rule₁ s₃ s₄ ∧ rule₂ s₂ s₄

class DistinctActionStronglySwaps: Prop where
  inputs: ∀ ident₁ ident₂ s₁ v₁ v₂ s₂ s₃,
    ident₁ ≠ ident₂ →
    (mod.inputs.getIO ident₁).snd s₁ v₁ s₂ →
    (mod.inputs.getIO ident₂).snd s₁ v₂ s₃ →
    ∃ s₄, (mod.inputs.getIO ident₂).snd s₂ v₂ s₄ ∧ (mod.inputs.getIO ident₁).snd s₃ v₁ s₄
  internals: ∀ rule₁ ∈ mod.internals, ∀ rule₂ ∈ mod.internals, ∀ s₁ s₂ s₃,
    -- NOTE: LOCAL CONFLUENCE DOESN'T REQUIRE DISTINCT RULES
    rule₁ ≠ rule₂ →
    rule₁ s₁ s₂ →
    rule₂ s₁ s₃ →
    ∃ s₄, rule₁ s₃ s₄ ∧ rule₂ s₂ s₄
  outputs: ∀ ident₁ ident₂ s₁ v₁ v₂ s₂ s₃,
    ident₁ ≠ ident₂ →
    (mod.outputs.getIO ident₁).snd s₁ v₁ s₂ →
    (mod.outputs.getIO ident₂).snd s₁ v₂ s₃ →
    ∃ s₄, (mod.outputs.getIO ident₂).snd s₂ v₂ s₄ ∧ (mod.outputs.getIO ident₁).snd s₃ v₁ s₄

-- I ALSO NEED SWAPPING BETWEEN INPUTS AND OUTPUTS.

class RuleSwapWithMethods: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂
    → existSR mod.internals s₁ s₃
    → ∃ s₄, (mod.inputs.getIO ident).snd s₃ v s₄ ∧ existSR mod.internals s₂ s₄
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂
    → existSR mod.internals s₁ s₃
    → ∃ s₄, (mod.outputs.getIO ident).snd s₃ v s₄ ∧ existSR mod.internals s₂ s₄

class RuleStronglySwapWithMethods: Prop where
  inputs: ∀ ident s₁ v s₂ s₃, ∀ rule ∈ mod.internals,
    (mod.inputs.getIO ident).snd s₁ v s₂ →
    rule s₁ s₃ →
    ∃ s₄, (mod.inputs.getIO ident).snd s₃ v s₄ ∧ rule s₂ s₄
  outputs: ∀ ident s₁ v s₂ s₃, ∀ rule ∈ mod.internals,
    (mod.outputs.getIO ident).snd s₁ v s₂ →
    rule s₁ s₃ →
    ∃ s₄, (mod.outputs.getIO ident).snd s₃ v s₄ ∧ rule s₂ s₄

instance [rmss: RuleStronglySwapWithMethods mod]: RuleSwapWithMethods mod where
  inputs  := by
    intros ident s₁ v s₂ s₃ h₁ h₂
    induction h₂ generalizing s₂ with
    | done =>
      use s₂ <;> and_intros
      . exact h₁
      . apply existSR_reflexive
    | step init mid final rule hᵣ h₂ h₃ ih =>
      obtain ⟨rmss, a⟩ := rmss <;> clear a h₃
      specialize rmss ident init v s₂ mid rule hᵣ h₁ h₂
      clear h₁ h₂
      obtain ⟨s₄, h₁, a⟩ := rmss
      specialize ih s₄ h₁ <;> clear h₁
      obtain ⟨w, _, a⟩ := ih
      use w <;> and_intros
      . assumption
      . apply existSR_transitive mod.internals _ s₄ _ _ a
        apply existSR_single_step <;> assumption
  outputs := by
    intros ident s₁ v s₂ s₃ h₁ h₂
    induction h₂ generalizing s₂ with
    | done =>
      use s₂ <;> and_intros
      . exact h₁
      . apply existSR_reflexive
    | step init mid final rule hᵣ h₂ h₃ ih =>
      obtain ⟨a, rmss⟩ := rmss <;> clear a h₃
      specialize rmss ident init v s₂ mid rule hᵣ h₁ h₂
      clear h₁ h₂
      obtain ⟨s₄, h₁, a⟩ := rmss
      specialize ih s₄ h₁ <;> clear h₁
      obtain ⟨w, _, a⟩ := ih
      use w <;> and_intros
      . assumption
      . apply existSR_transitive  mod.internals _ s₄ _ _ a
        apply existSR_single_step <;> assumption

end Graphiti

-- TODO: bring it closer to Confluence definitions and merge them?
