/-
Copyright (c) 2025-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas
import Graphiti.Projects.Flushability.FlushedModule
import Graphiti.Projects.Flushability.Outputability
import Graphiti.Projects.Flushability.ModuleWellformeness

namespace Graphiti

variable {I : Type _}
variable {S : Type _}
variable {Ident : Type _}
variable [DecidableEq Ident]

section

variable {imod : Module Ident I}
variable {smod : Module Ident S}

variable [mm : MatchInterface imod smod]

set_option quotPrecheck false in
infix:60 " ≺ " => (indistinguishable imod smod)

inductive φᵢ {φ₀: I → S → Prop}: I → S → Prop where
| base {rhs lhs}:
  φ₀ rhs lhs →
  φᵢ rhs lhs
| input i s ident (i': (imod.inputs.getIO ident).fst → I) (s': (smod.inputs.getIO ident).fst → S):
  i ≺ s →
  (∀ v, φᵢ (i' v) (s' ((mm.input_types ident).mp v))) →
  (∀ v, (imod.inputs.getIO ident).snd i v (i' v)) →
  (∀ v, (smod.inputs.getIO ident).snd s v (s' v)) →
  φᵢ i s
/-| output i s ident (i': (imod.outputs.getIO ident).fst → I) (s': (smod.outputs.getIO ident).fst → S):
  i ≺ s →
  (∀ v, φᵢ (i' v) (s' ((mm.output_types ident).mp v))) →
  (∀ v, (imod.outputs.getIO ident).snd i v (i' v)) →
  (∀ v, (smod.outputs.getIO ident).snd s v (s' v)) →
  φᵢ i s-/
| internal i s {i'}:
  i ≺ s →
  φᵢ i' s →
  existSR imod.internals i i' →
  φᵢ i s

---------------------------------------------------------------------------------------------------
-------------------------------------- INDISTINGUISHABILITY ---------------------------------------
---------------------------------------------------------------------------------------------------

instance φᵢ.ind {φ₀: I → S → Prop} [Flushable smod] [Indistinguishable imod smod φ₀]: Indistinguishable imod (flushed smod) (@φᵢ I S Ident _ imod (flushed smod) _ φ₀) := by
  constructor
  intros i₁ s₁ φₕ
  cases φₕ with
  | base φₕ =>
    have ind: Indistinguishable imod (flushed smod) φ₀ := by infer_instance
    exact ind.prop i₁ s₁ φₕ
  | input _ _ ident _ _ ind =>
    exact ind
  /-| output _ _ ident _ _ ind =>
    exact ind-/
  | internal _ _ ind =>
    exact ind

private theorem input_preserves_ind [dass: DistinctActionSwaps' imod]: ∀ i s ident (i': (imod.inputs.getIO ident).fst → I) (s': ((flushed smod).inputs.getIO ident).fst → S),
  (∀ v, indistinguishable imod (flushed smod) (i' v) (s' (coe_in.mp v))) →
  (∀ v, (imod.inputs.getIO ident).snd i v (i' v)) →
  (∀ v, ((flushed smod).inputs.getIO ident).snd s v (s' v)) →
  indistinguishable imod (flushed smod) i s :=
by
  intro i s ident₁ i' s' ind hᵢ hₛ
  constructor
  . intro ident₂ mid_i v h₁
    by_cases h: ident₁ = ident₂
    . subst h
      specialize hₛ (coe_in.mp v)
      refine ⟨_, hₛ⟩
    . obtain ⟨i'', hᵢ'⟩:= dass.inputs ident₁ ident₂ i v i' mid_i h hᵢ h₁
      rewrite [forall_and] at hᵢ' <;> obtain ⟨hᵢ', a⟩ := hᵢ' <;> clear a
      have hₛ' : ∀ x: (imod.inputs.getIO ident₁).fst, ∃ s₄, ((flushed smod).inputs.getIO ident₂).snd (s' (coe_in.mp x)) (coe_in.mp v) s₄ := by
        intro v
        specialize ind v
        specialize hᵢ' (coe_in.mp v)
        exact ind.inputs_indistinguishable _ _ _ hᵢ'
      sorry
  . intro ident₂ mid_i v h₁
    sorry

theorem internal_preserves_ind [rms: RuleSwapWithMethods imod]: ∀ i s i',
  indistinguishable imod smod i' s → existSR imod.internals i i' → indistinguishable imod smod i s :=
by
  intro i s i' ind h
  constructor
  . intros ident new_i v hᵢ
    have ⟨new_i', h, _⟩ := rms.inputs ident i v new_i i' hᵢ h
    apply ind.inputs_indistinguishable
    exact h
  . intros ident new_i v hᵢ
    have ⟨new_i', h, _⟩ := rms.outputs ident i v new_i i' hᵢ h
    apply ind.outputs_indistinguishable
    exact h

/-private theorem output_preserves_ind [dass: DistinctActionStronglySwaps' imod]: ∀ i s ident (i': (imod.outputs.getIO ident).fst → I) (s': ((flushed smod).outputs.getIO ident).fst → S),
  (∀ v, indistinguishable imod (flushed smod) (i' v) (s' (coe_out.mp v))) →
  (∀ v, (imod.outputs.getIO ident).snd i v (i' v)) →
  (∀ v, ((flushed smod).outputs.getIO ident).snd s v (s' v)) →
  indistinguishable imod (flushed smod) i s :=
by
  intro i s ident₁ i' s' ind hᵢ hₛ
  constructor
  . sorry
  . intro ident₂ mid_i v h₁
    by_cases h: ident₁ = ident₂
    . subst h
      specialize hₛ (coe_out.mp v)
      refine ⟨_, hₛ⟩
    . sorry-/

---------------------------------------------------------------------------------------------------

end

section

variable (imod : Module Ident I)
variable (smod : Module Ident S)

variable [mm : MatchInterface imod smod]

structure comp_refinesᵢ (φ : I → S → Prop) (init_i : I) (init_s : S) : Prop where
  inputs :
    ∀ ident mid_i v, (imod.inputs.getIO ident).2 init_i v mid_i →
      ∃ mid_s, (smod.inputs.getIO ident).2 init_s ((mm.input_types ident).mp v) mid_s ∧ φ mid_i mid_s
  outputs :
    ∀ ident mid_i v, (imod.outputs.getIO ident).2 init_i v mid_i →
      ∃ mid_s, (smod.outputs.getIO ident).2 init_s ((mm.output_types ident).mp v) mid_s ∧ φ mid_i mid_s
  internals :
    ∀ mid_i, existSR imod.internals init_i mid_i → φ mid_i init_s

def refines_φᵢ (φ : I → S → Prop) :=
  ∀ (init_i : I) (init_s : S),
    φ init_i init_s →
     @comp_refinesᵢ I S Ident _ imod smod _ φ init_i init_s

notation:35 imod " ⊑ᵢ_{" φ₀:35 "} " smod:34 =>
  refines_φᵢ imod (flushed smod) (@φᵢ _ _ _ _ imod (flushed smod) _ φ₀)

private theorem refᵢ_imp_ref: ∀ φ,
  imod ⊑ᵢ_{φ} smod → imod ⊑_{(@φᵢ _ _ _ _ imod (flushed smod) _ φ)} (flushed smod) :=
by
  intros φ h
  unfold Module.refines_φ
  intros init_i init_s φₕ
  specialize h init_i init_s φₕ
  constructor
  . intros ident mid_i v hᵢ
    have ⟨mid_s, hₛ, φₕ⟩ := h.inputs ident mid_i v hᵢ
    use mid_s, mid_s <;> and_intros
    . exact hₛ
    . exact existSR_reflexive
    . exact φₕ
  . intros ident mid_i v hᵢ
    have ⟨mid_s, hₛ, φₕ⟩ := h.outputs ident mid_i v hᵢ
    use init_s, mid_s <;> and_intros
    . exact existSR_reflexive
    . exact hₛ
    . exact φₕ
  . intros rule mid_i h₁ h₂
    use init_s <;> and_intros
    . exact existSR_reflexive
    . apply h.internals
      exact existSR_single_step imod.internals init_i mid_i rule h₁ h₂

-- TODO: Get rid of these axioms??
/--
info: '_private.Graphiti.Projects.Flushability.InductiveRefinement.0.Graphiti.refᵢ_imp_ref' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms refᵢ_imp_ref

---------------------------------------------------------------------------------------------------

class CanProveWithInduction (φ₀: I → S → Prop): Prop where
  input: ∀ ident i s v mid_i mid_s,
    φ₀ i s →
    (imod.inputs.getIO ident).snd i v mid_i →
    ((flushed smod).inputs.getIO ident).snd s (coe_in.mp v) mid_s →
    (@φᵢ I S Ident _ imod (flushed smod) _ φ₀) mid_i mid_s
  internal: ∀ i s i',
    φ₀ i s →
    existSR imod.internals i i' →
    (@φᵢ I S Ident _ imod (flushed smod) _ φ₀) i' s
  output: ∀ ident i s v mid_i mid_s,
    φ₀ i s →
    (imod.outputs.getIO ident).snd i v mid_i →
    ((flushed smod).outputs.getIO ident).snd s (coe_out.mp v) mid_s →
    (@φᵢ I S Ident _ imod (flushed smod) _ φ₀) mid_i mid_s
  initial:
    Module.refines_initial imod smod φ₀

end

section

variable (imod : Module Ident I)
variable (smod : Module Ident S)

def refinesᵢ :=
  ∃ (mm : MatchInterface imod smod) (φ : I → S → Prop),
    (imod ⊑ᵢ_{φ} smod) ∧ Module.refines_initial imod (flushed smod) (@φᵢ _ _ _ _ imod (flushed smod) _ φ)

notation:35 imod:34 " ⊑ᵢ " smod:34 => refinesᵢ imod smod


/--
info: 'Graphiti.refinesᵢ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms refinesᵢ

end

section

-- TODO: Rename this theorem properly
theorem bla_bla_bla {imod : Module Ident I} {smod : Module Ident S}:
  imod ⊑ᵢ smod → imod ⊑ (flushed smod) :=
by
  intro h
  unfold Module.refines
  obtain ⟨mm, φ, h₁, h₂⟩ := h
  use (by infer_instance), (@φᵢ _ _ _ _ imod (flushed smod) _ φ) <;> and_intros
  . exact refᵢ_imp_ref imod smod φ h₁
  . exact h₂

/--
info: 'Graphiti.bla_bla_bla' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms bla_bla_bla

-- TODO: Rename this theorem properly
theorem bla_bla {imod : Module Ident I} {smod : Module Ident S}:
  imod ⊑ᵢ smod → imod ⊑ smod :=
by
  intros h
  apply bla_bla_bla at h
  apply Module.refines_transitive (flushed smod)
  . exact h
  . exact flushed_refines_nonflushed smod

/--
info: 'Graphiti.bla_bla' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms bla_bla

end

section

variable (imod : Module Ident I)
variable (smod : Module Ident S)
variable (φ₀   : I → S → Prop)

/- PROPERTIES THE IMPLEMENTATION MUST SATISFY -/
variable [mm  : MatchInterface imod smod]
variable [igc : GloballyConfluent imod]
variable [irms: RuleSwapWithMethods imod] -- TODO: DO WE ACTUALLY NEED THIS?? DOESN'T DistinctActionStronglySwaps' imply it??
variable [iswaps: DistinctActionSwaps' imod]

/- PROPERTIES THE SPECIFICATION MUST SATISFY -/
variable [Flushable smod]
variable [GloballyConfluent smod]
-- TODO: WE CAN GET RID IF THIS DETERMINISM HERE AND HAVE CONFLUENCE IF WE ALLOW
--       INTERNAL RULES AFTER OUTPUT IT WAS NOT DONE SO FAR TO EASILY HANDLE CONNECTIONS
variable [sdt : DeterministicOutputs smod]
-- TODO: REMOVED FLUSHED FROM HERE...
-- NOTE: When removing flushed, make sure we don't prove useless things like swaping internal rules with universes.
variable [sswaps: DistinctActionSwaps' (flushed smod)]

/- PROPERTIES MUST φ₀ SATISFY -/
variable [Indistinguishable imod smod φ₀]
variable [cpwi: CanProveWithInduction imod smod φ₀]

set_option quotPrecheck false in
infix:60 " ≺ " => (indistinguishable imod (flushed smod))

include φ₀ in private theorem global_refinesᵢ: imod ⊑ᵢ smod := by
  unfold refinesᵢ
  use mm, φ₀ <;> and_intros
  . unfold refines_φᵢ
    intro init_i init_s Hφ
    induction Hφ with
    | @base i s φₕ =>
      clear init_i init_s
      apply comp_refinesᵢ.mk
      . intros ident mid_i v hᵢ
        have ⟨mid_s, hₛ⟩ : ∃ x, ((flushed smod).inputs.getIO ident).snd s (coe_in.mp v) x := by
          apply φᵢ.base at φₕ
          exact (φᵢ.ind.prop i s φₕ).inputs_indistinguishable ident mid_i v hᵢ
        refine ⟨mid_s, hₛ, cpwi.input ident i s v mid_i mid_s φₕ hᵢ hₛ⟩
      . intros ident mid_i v hᵢ
        have ⟨mid_s, hₛ⟩ : ∃ mid_s, ((flushed smod).outputs.getIO ident).snd s (coe_out.mp v) mid_s := by
          apply φᵢ.base at φₕ
          exact (φᵢ.ind.prop i s φₕ).outputs_indistinguishable ident mid_i v hᵢ
        refine ⟨mid_s, hₛ, cpwi.output ident i s v mid_i mid_s φₕ hᵢ hₛ⟩
      . intros mid_i h
        exact cpwi.internal i s mid_i φₕ h
    | @input i s ident₁ i' s' ind φₕ h₁ h₂ ih =>
      clear init_i init_s
      apply comp_refinesᵢ.mk
      . intros ident₂ mid_i v₁ hᵢ
        by_cases h: ident₁ = ident₂
        . subst h
          specialize h₂ (coe_in.mp v₁)
          use (s' (coe_in.mp v₁)) <;> and_intros
          . exact h₂
          . dsimp at *
            specialize ih v₁ <;> obtain ⟨a, b, ih⟩ := ih <;> clear a b
            specialize h₁ v₁
            have ⟨s₄, _, _⟩ := igc.inputs ident₁ i v₁ mid_i (i' v₁) hᵢ h₁
            specialize ih s₄ (by assumption)
            apply φᵢ.internal mid_i (s' (coe_in.mp v₁)) _ ih (by assumption)
            apply φᵢ.ind.prop at ih
            apply internal_preserves_ind _ _ s₄ <;> assumption
        . have ⟨mid_s, hₛ⟩ := ind.inputs_indistinguishable ident₂ mid_i v₁ hᵢ
          use mid_s <;> and_intros
          . exact hₛ
          . have ⟨i'', hᵢ'⟩ := iswaps.inputs ident₁ ident₂ i v₁ i' mid_i h h₁ hᵢ
            have ⟨s'', hₛ'⟩ := sswaps.inputs ident₁ ident₂ s (coe_in.mp v₁) s' mid_s h h₂ hₛ
            dsimp at hₛ'
            have φₕ: ∀ v, @φᵢ _ _ _ _ imod (flushed smod) _ φ₀ (i'' v) (s'' (coe_in.mp v)) := by
              dsimp at ⊢
              intro v
              specialize ih v
              obtain ⟨ih, a, b⟩ := ih <;> clear a b
              specialize hᵢ' v <;> obtain ⟨hᵢ', a⟩ := hᵢ' <;> clear a
              specialize hₛ' (coe_in.mp v) <;> obtain ⟨hₛ', a⟩ := hₛ' <;> clear a
              specialize ih ident₂ (i'' v) v₁ hᵢ'
              obtain ⟨mid_s, h, φₕ⟩ := ih
              have: (s'' (coe_in.mp v)) = mid_s :=
                have sdt: DeterministicInputs (flushed smod) := by infer_instance
                sdt.input_deterministic ident₂ (s' (coe_in.mp v)) (coe_in.mp v₁) (s'' (coe_in.mp v)) mid_s hₛ' h
              subst_vars <;> dsimp at *
              exact φₕ
            rewrite [forall_and] at hᵢ' <;> obtain ⟨a, hᵢ'⟩ := hᵢ' <;> clear a
            rewrite [forall_and] at hₛ' <;> obtain ⟨a, hₛ'⟩ := hₛ' <;> clear a
            apply φᵢ.input mid_i mid_s ident₁ i'' s'' _ φₕ hᵢ' hₛ'
            apply input_preserves_ind _ _ _ i'' s'' _ hᵢ' hₛ'
            intro v
            specialize φₕ v
            apply φᵢ.ind.prop _ _ φₕ
      . intro ident₂ mid_i v₁ hᵢ
        have ⟨mid_s, hₛ⟩ := ind.outputs_indistinguishable ident₂ mid_i v₁ hᵢ
        use mid_s <;> and_intros
        . exact hₛ
        . have ⟨i'', hᵢ'⟩ := iswaps.in_out ident₁ ident₂ i v₁ i' mid_i h₁ hᵢ
          have ⟨s'', hₛ'⟩ := sswaps.in_out ident₁ ident₂ s (coe_out.mp v₁) s' mid_s h₂ hₛ
          have φₕ: ∀ v, @φᵢ _ _ _ _ imod (flushed smod) _ φ₀ (i'' v) (s'' (coe_in.mp v)) := by
            dsimp at ⊢ hₛ'
            intro v
            specialize ih v
            obtain ⟨a, ih, b⟩ := ih <;> clear a b
            specialize hᵢ' v
            obtain ⟨a, hᵢ'⟩ := hᵢ' <;> clear a
            specialize ih ident₂ (i'' v) v₁ hᵢ'
            obtain ⟨mid_s, h, φₕ⟩ := ih
            have: (s'' (coe_in.mp v)) = mid_s := by
              specialize hₛ' (coe_in.mp v) <;> obtain ⟨a, hₛ'⟩ := hₛ' <;> clear a
              dsimp at hₛ' h
              apply sdt.output_deterministic <;> assumption
            subst_vars
            exact φₕ
          rewrite [forall_and] at hₛ'
          obtain ⟨hₛ', a⟩ := hₛ' <;> clear a
          rewrite [forall_and] at hᵢ'
          obtain ⟨hᵢ', a⟩ := hᵢ' <;> clear a
          apply φᵢ.input mid_i mid_s ident₁ i'' s'' _ φₕ hᵢ' hₛ'
          apply input_preserves_ind _ _ _ i'' s'' _ hᵢ' hₛ'
          intro v <;> specialize φₕ v <;> exact φᵢ.ind.prop _ _ φₕ
      . intros mid_i h'₁
        have ⟨i'', hᵢ''⟩ := iswaps.in_int ident₁ i i' mid_i h₁ h'₁
        have φₕ: ∀ v, @φᵢ _ _ _ _ imod (flushed smod) _ φ₀ (i'' v) (s' (coe_in.mp v)) := by
          dsimp <;> intro v
          specialize ih v
          specialize hᵢ'' v <;> obtain ⟨a, hᵢ''⟩ := hᵢ'' <;> clear a
          obtain ⟨a, b, ih⟩ := ih <;> clear a b
          specialize ih (i'' v) hᵢ''
          exact ih
        rewrite [forall_and] at hᵢ'' <;> obtain ⟨hᵢ'', a⟩ := hᵢ'' <;> clear a
        apply φᵢ.input mid_i s ident₁ i'' s' _ φₕ hᵢ'' h₂
        apply input_preserves_ind _ _ _ i'' s' _ hᵢ'' h₂
        intro v <;> specialize φₕ v <;> exact φᵢ.ind.prop _ _ φₕ
    /-| @output i s ident₁ i' s' ind φₕ h₁ h₂ ih =>
      clear init_i init_s
      apply comp_refinesᵢ.mk
      . intro ident₂ mid_i v₁ hᵢ
        have ⟨mid_s, hₛ⟩ := ind.inputs_indistinguishable ident₂ mid_i v₁ hᵢ
        use mid_s <;> and_intros
        . exact hₛ
        . have ⟨i'', hᵢ'⟩ := iswaps.out_in ident₁ ident₂ i v₁ i' mid_i h₁ hᵢ
          have ⟨s'', hₛ'⟩ := sswaps.out_in ident₁ ident₂ s (coe_in.mp v₁) s' mid_s h₂ hₛ
          have φₕ: ∀ v, @φᵢ _ _ _ _ imod (flushed smod) _ φ₀ (i'' v) (s'' (coe_out.mp v)) := by
            dsimp at ⊢ hₛ'
            intro v
            specialize ih v
            obtain ⟨ih, a, b⟩ := ih <;> clear a b
            specialize hᵢ' v
            obtain ⟨a, hᵢ'⟩ := hᵢ' <;> clear a
            specialize ih ident₂ (i'' v) v₁ hᵢ'
            obtain ⟨mid_s, h, φₕ⟩ := ih
            have: (s'' (coe_out.mp v)) = mid_s := by
              have sdt: DeterministicInputs (flushed smod) := by infer_instance
              specialize hₛ' (coe_out.mp v) <;> obtain ⟨a, hₛ'⟩ := hₛ' <;> clear a
              dsimp at hₛ' h
              apply sdt.input_deterministic <;> assumption
            subst_vars
            exact φₕ
          rewrite [forall_and] at hₛ' <;> obtain ⟨hₛ', a⟩ := hₛ' <;> clear a
          rewrite [forall_and] at hᵢ' <;> obtain ⟨hᵢ', a⟩ := hᵢ' <;> clear a
          apply φᵢ.output mid_i mid_s ident₁ i'' s'' _ φₕ hᵢ' hₛ'
          apply output_preserves_ind _ _ _ i'' s'' _ hᵢ' hₛ'
          intro v <;> specialize φₕ v <;> exact φᵢ.ind.prop _ _ φₕ
      . intros ident₂ mid_i v₁ hᵢ
        by_cases h: ident₁ = ident₂
        . subst h
          specialize h₂ (coe_out.mp v₁)
          use (s' (coe_out.mp v₁)) <;> and_intros
          . exact h₂
          . dsimp at *
            specialize ih v₁
            obtain ⟨a, b, ih⟩ := ih <;> clear a b
            specialize h₁ v₁
            have ⟨s₄, _, _⟩ := igc.outputs ident₁ i v₁ mid_i (i' v₁) hᵢ h₁
            specialize ih s₄ (by assumption)
            apply φᵢ.internal mid_i (s' (coe_out.mp v₁)) _ ih (by assumption)
            apply φᵢ.ind.prop at ih
            apply internal_preserves_ind _ _ s₄ <;> assumption
        . have ⟨mid_s, hₛ⟩ := ind.outputs_indistinguishable ident₂ mid_i v₁ hᵢ
          use mid_s <;> and_intros
          . exact hₛ
          . have ⟨i'', hᵢ'⟩ := iswaps.outputs ident₁ ident₂ i v₁ i' mid_i h h₁ hᵢ
            have ⟨s'', hₛ'⟩ := sswaps.outputs ident₁ ident₂ s (coe_out.mp v₁) s' mid_s h h₂ hₛ
            have φₕ: ∀ v, @φᵢ _ _ _ _ imod (flushed smod) _ φ₀ (i'' v) (s'' (coe_out.mp v)) := by
              dsimp at ⊢
              intro v
              specialize ih v
              obtain ⟨a, ih, b⟩ := ih <;> clear a b
              specialize hᵢ' v <;> obtain ⟨hᵢ', a⟩ := hᵢ' <;> clear a
              specialize hₛ' (coe_out.mp v) <;> obtain ⟨hₛ', a⟩ := hₛ' <;> clear a
              specialize ih ident₂ (i'' v) v₁ hᵢ'
              obtain ⟨mid_s, h, φₕ⟩ := ih
              have: (s'' (coe_out.mp v)) = mid_s := by
                apply sdt.output_deterministic <;> assumption
              subst_vars <;> dsimp at *
              exact φₕ
            rewrite [forall_and] at hᵢ' <;> obtain ⟨a, hᵢ'⟩ := hᵢ' <;> clear a
            rewrite [forall_and] at hₛ' <;> obtain ⟨a, hₛ'⟩ := hₛ' <;> clear a
            apply φᵢ.output mid_i mid_s ident₁ i'' s'' _ φₕ hᵢ' hₛ'
            apply output_preserves_ind _ _ _ i'' s'' _ hᵢ' hₛ'
            intro v
            specialize φₕ v
            apply φᵢ.ind.prop _ _ φₕ
      . intros mid_i h'₁
        have ⟨i'', hᵢ''⟩ := iswaps.out_int ident₁ i i' mid_i h₁ h'₁
        have φₕ: ∀ v, @φᵢ _ _ _ _ imod (flushed smod) _ φ₀ (i'' v) (s' (coe_out.mp v)) := by
          dsimp <;> intro v
          specialize ih v
          specialize hᵢ'' v <;> obtain ⟨a, hᵢ''⟩ := hᵢ'' <;> clear a
          obtain ⟨a, b, ih⟩ := ih <;> clear a b
          specialize ih (i'' v) hᵢ''
          exact ih
        rewrite [forall_and] at hᵢ'' <;> obtain ⟨hᵢ'', a⟩ := hᵢ'' <;> clear a
        apply φᵢ.output mid_i s ident₁ i'' s' _ φₕ hᵢ'' h₂
        apply output_preserves_ind _ _ _ i'' s' _ hᵢ'' h₂
        intro v <;> specialize φₕ v <;> exact φᵢ.ind.prop _ _ φₕ-/
    | @internal i s i₁ ind φₕ hᵢ ih =>
      clear init_i init_s
      apply comp_refinesᵢ.mk
      . intros ident mid_i v hᵢ'
        have ⟨mid_i', h₁, h₂⟩ := irms.inputs ident i v mid_i i₁ hᵢ' hᵢ
        obtain ⟨ih, a, b⟩ := ih <;> clear a b
        specialize ih ident mid_i' v h₁
        obtain ⟨mid_s, hₛ, φₕ⟩ := ih
        have ind: mid_i ≺ mid_s := by
          apply φᵢ.ind.prop at φₕ
          exact internal_preserves_ind _ _ _ φₕ h₂
        refine ⟨mid_s, hₛ, φᵢ.internal mid_i mid_s ind φₕ h₂⟩
      . intros ident mid_i v hᵢ'
        have ⟨mid_i', h₁, h₂⟩ := irms.outputs ident i v mid_i i₁ hᵢ' hᵢ
        obtain ⟨a, ih, b⟩ := ih <;> clear a b
        specialize ih ident mid_i' v h₁
        obtain ⟨mid_s, hₛ, φₕ⟩ := ih
        have ind: mid_i ≺ mid_s := by
          apply φᵢ.ind.prop at φₕ
          apply internal_preserves_ind <;> assumption
        refine ⟨mid_s, hₛ, φᵢ.internal mid_i mid_s ind φₕ h₂⟩
      . intros i₂ hᵢ'
        have ⟨i₃, h₃, h⟩ := igc.internals i i₁ i₂ hᵢ hᵢ'
        obtain ⟨a, b, ih⟩ := ih <;> clear a b
        specialize ih i₃ h₃ <;> clear h₃
        have ind: i₂ ≺ s := by
          apply φᵢ.ind.prop at ih
          apply internal_preserves_ind <;> assumption
        exact φᵢ.internal i₂ s ind ih h
  . unfold Module.refines_initial
    intros i hᵢ
    apply cpwi.initial at hᵢ
    obtain ⟨s, hₛ, φₕ⟩ := hᵢ
    refine ⟨s, hₛ, φᵢ.base φₕ⟩

/--
info: '_private.Graphiti.Projects.Flushability.InductiveRefinement.0.Graphiti.global_refinesᵢ' depends on axioms: [propext,
 sorryAx,
 Quot.sound]
-/
#guard_msgs in
#print axioms global_refinesᵢ

include φ₀ in theorem inductively_refines: imod ⊑ smod := by
  have h : imod ⊑ᵢ smod := global_refinesᵢ imod smod φ₀
  exact bla_bla h

/--
info: 'Graphiti.inductively_refines' depends on axioms: [propext, sorryAx, Quot.sound]
-/
#guard_msgs in
#print axioms inductively_refines

end

end Graphiti
