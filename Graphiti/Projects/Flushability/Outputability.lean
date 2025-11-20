/-
Copyright (c) 2025-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas

import Graphiti.Projects.Flushability.SimulationRelation

namespace Graphiti

variable {Ident S₁ S₂ : Type _}
variable [DecidableEq Ident]
variable (mod₁ : Module Ident S₁) (mod₂ : Module Ident S₂)
variable [mm: MatchInterface mod₁ mod₂]

section Outputability

variable {Ident S: Type _}
variable [DecidableEq Ident]

inductive direct_outputable: (Module Ident S) → S → InternalPort Ident → Prop where
| mk: ∀ mod ident s, (∃ v s', (mod.outputs.getIO ident).snd s v s') → direct_outputable mod s ident

inductive indirect_outputable: (Module Ident S) → S → InternalPort Ident → Prop where
| mk: ∀ mod ident s, (∃ v s₁ s₂, existSR (mod.internals) s s₁ ∧ (mod.outputs.getIO ident).snd s₁ v s₂) → indirect_outputable mod s ident

-- TODO: Add wrt to port?
inductive outputable: (Module Ident S) → S → InternalPort Ident → Prop where
| direct:   ∀ mod ident s, direct_outputable mod s ident   → outputable mod s ident
| indirect: ∀ mod ident s, indirect_outputable mod s ident → outputable mod s ident

-- TODO: If this theorem holds, we reduce the reasoning to only prove that the
--       state if `outputable` (in practice, we should only prove `indirect_outputable`)
--       The question remains how hard it is to define the pattern of
--       `indirect_outputable` states
-- TODO: In out running example, a non-direct, indirect outputable state has a single pattern
--       Can we derive that a state in rhs follows that pattern easily?
--theorem n:
--  ∀ (mod: Module Ident S) ident s, outputable mod ident s ∧ /- pf mod s -/ → direct_outputable mod ident s :=
--by
--  sorry

-- If a state is flushable and outputable, then it is direct_outputable

--variable (mod: Module Ident S) in
--example: direct_outputable mod sorry sorry := by
--  sorry

end Outputability

section Indistinguishability

variable (ψ : S₁ → S₂ → Prop)

/-
This could be made even more flexible by passing a custom type comparison
function for the inputs and outputs.  For now this might be general enough
though.
-/
structure indistinguishable (init_i : S₁) (init_s : S₂) : Prop where
  inputs_indistinguishable : ∀ (ident : InternalPort Ident) new_i v,
    (mod₁.inputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (mod₂.inputs.getIO ident).2 init_s ((mm.input_types ident).mp v) new_s
  outputs_indistinguishable : ∀ ident new_i v,
    (mod₁.outputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (mod₂.outputs.getIO ident).2 init_s ((mm.output_types ident).mp v) new_s

class Indistinguishable: Prop where
  prop: ∀ i₁ s₁, ψ i₁ s₁ → indistinguishable mod₁ mod₂ i₁ s₁

end Indistinguishability

section Composition

variable (ψ₁: S₁ → S₂ → Prop) (ψ₂: S₁ → S₂ → Prop)

instance [ind: Indistinguishable mod₁ mod₂ ψ₁]: Indistinguishable mod₁ mod₂ (ψ₁ ∧ ψ₂) := by
  constructor
  intro i₁ s₁ ⟨h, _⟩
  apply ind.prop
  exact h

instance [ind: Indistinguishable mod₁ mod₂ ψ₂]: Indistinguishable mod₁ mod₂ (ψ₁ ∧ ψ₂) := by
  constructor
  intro i₁ s₁ ⟨_, h⟩
  apply ind.prop
  exact h

instance [ind₁: Indistinguishable mod₁ mod₂ ψ₁] [ind₂: Indistinguishable mod₁ mod₂ ψ₂]: Indistinguishable mod₁ mod₂ (ψ₁ ∨ ψ₂) := by
  constructor
  intro i₁ s₁ h
  rcases h with h | h
  . apply ind₁.prop <;> exact h
  . apply ind₂.prop <;> exact h

end Composition

end Graphiti
