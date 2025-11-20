
import Graphiti.Core.Module
import Graphiti.Projects.Flushability.FlushedModule

namespace Graphiti

section FlushableModules

variable {S₁ S₂: Type _}
variable {Ident: Type _}
variable (mod₁: Module Ident S₁) (mod₂: Module Ident S₂)
variable [DecidableEq Ident]
variable [fl₁: Flushable mod₁] [fl₂: Flushable mod₂]

def φ₁ (s₁: S₁)(s₂: S₂): Prop := pf mod₁ s₁ ∧ pf mod₂ s₂

instance [MatchInterface mod₁ mod₂]: WeakSimulationRelation (φ₁ mod₁ mod₂) mod₁ mod₂ := {
  inputs_preserved := by
    intro ident i₁ i₂ v s₁ s₂
    obtain ⟨i₃, hi₃⟩ := fl₁.flushable i₂
    obtain ⟨s₃, hs₃⟩ := fl₂.flushable s₂
    use i₃, s₃
    intros
    and_intros
    . apply flushesTo_implies_pf <;> assumption
    . apply flushesTo_implies_pf <;> assumption
  internals_preserved := by
    intros i₁ s₁
    obtain ⟨i₂, hi₂⟩ := fl₁.flushable i₁
    obtain ⟨s₂, hs₂⟩ := fl₂.flushable s₁
    use i₂, s₂
    intros
    and_intros
    . apply flushesTo_implies_pf <;> assumption
    . apply flushesTo_implies_pf <;> assumption
  outputs_preserved := by
    intro ident i₁ i₂ v s₁ s₂
    obtain ⟨i₃, hi₃⟩ := fl₁.flushable i₂
    obtain ⟨s₃, hs₃⟩ := fl₂.flushable s₂
    use i₃, s₃
    intros
    and_intros
    . apply flushesTo_implies_pf <;> assumption
    . apply flushesTo_implies_pf <;> assumption
  initial_state_preserves := by
    sorry -- Wellformness of the module should solve this
}

end FlushableModules

section SimulationRelation

variable {S₁ S₂: Type _}
variable {Ident: Type _}
variable [DecidableEq Ident]
variable {mod₁: Module Ident S₁}
variable {mod₂: Module Ident S₂}
variable {φ: S₁ → S₂ → Prop}
variable [MatchInterface mod₁ mod₂]

instance [sr: SimulationRelation φ mod₁ mod₂]: SimulationRelation φ (flushed mod₁) (flushed mod₂) := {
  inputs_preserved    := by
    intros ident i₁ i₂ v s₁ s₂ h₁ h₂ h₃
    rw [flushed_inputs_are_rflushed] at h₂
    rw [flushed_inputs_are_rflushed] at h₃
    obtain ⟨w₁, _, _, _⟩ := h₂
    obtain ⟨w₂, _, _, _⟩ := h₃
    simp at *
    have: φ w₁ w₂ := by
      apply sr.inputs_preserved <;> simpa
    apply sr.internals_preserved <;> assumption
  internals_preserved := by
    intros i₁ i₂ s₁ s₂ h₁ h₂ h₃
    dsimp [flushed] at h₂ h₃
    apply existSR_norules at h₂ <;> subst h₂
    apply existSR_norules at h₃ <;> subst h₃
    exact h₁
  outputs_preserved   := by
    intros ident i₁ i₂ v s₁ s₂ h₁ h₂ h₃
    dsimp [flushed] at h₂ h₃
    apply sr.outputs_preserved <;> assumption
  initial_state_preserves := by
    intros i s h₁ h₂
    dsimp [flushed, isflushed] at *
    apply sr.initial_state_preserves <;> assumption
}

-- TODO: pf mod s is a (weak) simulation relation between any two flushable modules
--       A weak simulation relation allows arbitrary operations after inputing and outputing and in the initial states
end SimulationRelation

end Graphiti
