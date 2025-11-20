/-
Copyright (c) 2024-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Hamza Remmal
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq
import Mathlib.Tactic

import Graphiti.Core.Simp
import Graphiti.Core.Module
import Graphiti.Core.ModuleReduction
import Graphiti.Core.ExprLow
import Graphiti.Core.Component
import Graphiti.Core.KernelRefl
import Graphiti.Core.Reduce
import Graphiti.Core.List
import Graphiti.Core.ExprHighLemmas
import Graphiti.Core.Tactic
import Graphiti.Core.Rewrites.JoinRewrite

import Graphiti.Projects.Flushability.ModuleProperties
import Graphiti.Projects.Flushability.ModuleWellformeness
import Graphiti.Projects.Flushability.SimulationRelation
import Graphiti.Projects.Flushability.DeterministicModule
import Graphiti.Projects.Flushability.ConfluentModule
import Graphiti.Projects.Flushability.FlushedModule
import Graphiti.Projects.Flushability.Outputability
import Graphiti.Projects.Flushability.Lemmas
import Graphiti.Projects.Flushability.Coe
import Graphiti.Projects.Flushability.InductiveRefinement

--set_option profiler true

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace Graphiti.JoinRewrite

open StringModule

abbrev Ident := Nat

variable {T₁ T₂ T₃ : Type}
variable (S₁ S₂ S₃ : String)

@[drunfold_defs]
def rewriteLhsRhs := rewrite.rewrite [S₁, S₂, S₃] |>.get rfl

def environmentLhs : IdentMap String (TModule1 String) := lhs T₁ T₂ T₃ S₁ S₂ S₃ |>.snd
def environmentRhs : IdentMap String (TModule1 String) := rhs T₁ T₂ T₃ S₁ S₂ S₃ |>.snd

@[drenv] theorem find?_join1_data : (Batteries.AssocList.find? ("join " ++ S₁ ++ " " ++ S₂) (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₁ T₂⟩ := by
  dsimp [environmentLhs, lhs]
  have : ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃ == "join " ++ S₁ ++ " " ++ S₂) = false := by
    sorry
  rw [Batteries.AssocList.find?.eq_2]; (rw [this]; clear this); dsimp
  have : ("join " ++ S₁ ++ " " ++ S₂ == "join " ++ S₁ ++ " " ++ S₂) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_join2_data : (Batteries.AssocList.find? ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃) (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join (T₁ × T₂) T₃⟩ := by
  dsimp [environmentLhs, lhs]
  rw [Batteries.AssocList.find?.eq_2]
  simp

@[drenv] theorem find?_join1_data2 : (Batteries.AssocList.find? ("join " ++ S₂ ++ " " ++ S₃) (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₂ T₃⟩ := by
  sorry
  --dsimp [environmentRhs, rhs]
  --simp only [toString]
  --have : ("join " ++ S₂ ++ " " ++ S₃ == "join " ++ S₂ ++ " " ++ S₃) = true := by simp
  --rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_join2_data2 : (Batteries.AssocList.find? ("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₁ (T₂ × T₃)⟩ := by
  sorry
  --dsimp [environmentRhs, rhs]
  --have : ("join " ++ S₂ ++ " " ++ S₃ == "join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") = false := by
  --  sorry
  --rw [Batteries.AssocList.find?.eq_2]; (rw [this]; clear this); dsimp
  --have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == ("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")")) = true := by simp
  --rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_pure_data2 : (Batteries.AssocList.find? ("pure (" ++ S₁ ++ "×(" ++ S₂ ++ "×" ++ S₃ ++ ")) ((" ++ S₁ ++ "×" ++ S₂ ++ ")×" ++ S₃ ++ ")") (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, pure λ ((a, b, c) : T₁ × (T₂ × T₃)) => ((a, b), c)⟩ := by
  sorry
  --dsimp [environmentRhs, rhs]
  --have : ("join " ++ S₂ ++ " " ++ S₃ == "pure (" ++ S₁ ++ "×(" ++ S₂ ++ "×" ++ S₃ ++ ")) ((" ++ S₁ ++ "×" ++ S₂ ++ ")×" ++ S₃ ++ ")") = false := by
  --  sorry
  --rw [Batteries.AssocList.find?.eq_2]; (rw [this]; clear this); dsimp
  --have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == "pure (" ++ S₁ ++ "×(" ++ S₂ ++ "×" ++ S₃ ++ ")) ((" ++ S₁ ++ "×" ++ S₂ ++ ")×" ++ S₃ ++ ")") = false := by
  --  sorry
  --rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  --have : (s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})" == "pure (" ++ S₁ ++ "×(" ++ S₂ ++ "×" ++ S₃ ++ ")) ((" ++ S₁ ++ "×" ++ S₂ ++ ")×" ++ S₃ ++ ")") = true := by sorry
  --rw [Batteries.AssocList.find?.eq_2]; rw [this]

seal environmentLhs in
def_module lhsModuleType (T₁ T₂ T₃: Type): Type :=
  [T| (rewriteLhsRhs S₁ S₂ S₃).input_expr, (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃).find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [find?_join1_data, find?_join2_data]
  dsimp

seal environmentLhs in
def_module lhsModule (T₁ T₂ T₃: Type) : StringModule (lhsModuleType T₁ T₂ T₃) :=
  [e| (rewriteLhsRhs S₁ S₂ S₃).input_expr, (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃).find? ]

seal environmentRhs in
def_module rhsModuleType (T₁ T₂ T₃: Type) : Type :=
  [T| (rewriteLhsRhs S₁ S₂ S₃).output_expr, (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃).find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [find?_pure_data2, find?_join2_data2, find?_join2_data, find?_join1_data, find?_join1_data2]
  dsimp

seal environmentRhs in
def_module rhsModule (T₁ T₂ T₃: Type) : StringModule (rhsModuleType T₁ T₂ T₃) :=
  [e| (rewriteLhsRhs S₁ S₂ S₃).output_expr, (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃).find? ]

---------------------------------------------------------------------------------------------------
--------------
---------------------------------------------------------------------------------------------------

instance : MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by
  dsimp [rhsModule, lhsModule]
  solve_match_interface

instance: SingleInternal (lhsModule T₁ T₂ T₃) where
  prop := by dsimp [lhsModule]

---------------------------------------------------------------------------------------------------
-----------
---------------------------------------------------------------------------------------------------

section Flushability

private inductive partially_flushed: lhsModuleType T₁ T₂ T₃ -> Prop where
| lhs: ∀ lower arb, partially_flushed ⟨lower, [], arb⟩
| rhs: ∀ lower arb, partially_flushed ⟨lower, arb, []⟩

private theorem pf_iff_partially_flushed:
  ∀ s, pf (lhsModule T₁ T₂ T₃) s ↔ partially_flushed s :=
by
  intro s
  constructor
  . obtain ⟨s1, s2, s3⟩ := s
    intros hr; dsimp [lhsModuleType, lhsModule] at *
    specialize hr ?r (by simp; rfl)
    cases s2 <;> cases s3 <;> try constructor
    exfalso
    apply hr ⟨⟨_, _⟩, ⟨_, _⟩⟩
    dsimp
    iterate 5 (apply Exists.intro _)
    and_intros <;> rfl
  . intro  h
    cases h
    all_goals
      unfold pf
      intros rule hᵣ _ h
      simp [lhsModule] at hᵣ <;> subst hᵣ
      simp at h

instance: Flushable (lhsModule T₁ T₂ T₃) := by
  constructor
  intro ⟨⟨l1, l2⟩, ⟨l3, l4⟩⟩
  induction l3 generalizing l1 l2 l4 with
  | nil =>
    apply pf_is_flushable
    rewrite [pf_iff_partially_flushed]
    constructor
  | cons x xs ih =>
    cases l4 with
    | nil =>
      apply pf_is_flushable
      rewrite [pf_iff_partially_flushed]
      constructor
    | cons head tail =>
      specialize ih (l1 ++ [(x, head)]) l2 tail
      obtain ⟨s, hᵣ, hpf⟩ := ih
      use s <;> constructor
      . apply existSR_transitive _ _ ((l1 ++ [(x, head)], l2), xs, tail) _
        . apply existSR_single_step' <;> simp [lhsModule]
        . exact hᵣ
      . exact hpf

---------------------------------------------------------------------------------------------------
-- TODO: PROVE THAT RHS IS ALSO FLUSHABLE IN CASE WE CAN USE IT TO PROVE GLOBAL CONFLUENCE
--instance: Flushable (rhsModule T₁ T₂ T₃) := by
--  sorry

---------------------------------------------------------------------------------------------------
instance: OutputPreservesFlushability (lhsModule T₁ T₂ T₃) := by
  constructor
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ hpf h
  rewrite [pf_iff_partially_flushed] at ⊢ hpf
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [lhsModule] at HContains <;> subst HContains
    dsimp [lhsModule] at h
    rw [PortMap.rw_rule_execution] at h
    repeat
      cases ‹_ ∧ _›; simp at *
    subst_vars
    cases hpf <;> constructor
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

end Flushability

section SimulationRelation

def ψ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  let ⟨⟨j2l, j2r⟩, ⟨j1l, j1r⟩⟩ := lhs
  let ⟨⟨j2l', j2r'⟩, ⟨⟨j1l', j1r'⟩, p⟩⟩ := rhs
  (j2l.map Prod.fst ++ j1l = p.map (Prod.fst ∘ Prod.fst) ++ j2l') ∧
  (j2l.map Prod.snd ++ j1r = p.map ((Prod.snd ∘ Prod.fst)) ++ j2r'.map Prod.fst ++ j1l') ∧
  (j2r = p.map Prod.snd ++ j2r'.map Prod.snd ++ j1r')

private theorem ψ_holds_over_internals_spec:
  ∀ i s s', ψ i s → existSR (lhsModule T₁ T₂ T₃).internals s s' → ψ i s' :=
by
  intro ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ s s' Hψ E
  induction E
  . assumption
  . rename_i init mid _ rule Hrule c _ Himpl
    apply Himpl; clear Himpl
    unfold lhsModule at Hrule; simp at Hrule
    subst_vars
    obtain ⟨_, _, _, _, _, _, _, _⟩ := c
    let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
    let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
    rename_i a _ _ _ _ _ b; simp at a b
    obtain ⟨ ⟨_, _⟩, ⟨_, _⟩⟩ := a
    obtain ⟨ ⟨_, _⟩ , ⟨_, _⟩⟩ := b
    unfold ψ at *; simp at *
    subst_vars
    obtain ⟨ _, ⟨_, _⟩ ⟩ := Hψ
    simp; and_intros <;> simp_all
    grind [ψ]

private theorem ψ_holds_over_internals_impl:
  ∀ i i' s, ψ i s → existSR (rhsModule T₁ T₂ T₃).internals i i' → ψ i' s :=
by
  intro i i' ⟨⟨_, _⟩, ⟨_, _⟩⟩ Hψ E
  induction E
  . assumption
  . rename_i init mid _ rule Hrule c _ Himpl
    apply Himpl; clear Himpl
    unfold rhsModule at Hrule; simp at Hrule
    cases Hrule <;> subst_vars
    . let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
      unfold ψ at *; simp at *
      rename_i synth1 synth2;
      obtain ⟨_, _⟩ := synth1
      obtain ⟨_, _, _⟩ := Hψ
      and_intros <;> subst_vars <;> try simp <;> grind
      grind
    . obtain ⟨_, _, _, _, _, _, _, _, ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩⟩ := c
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
      unfold ψ at *; simp at *
      rename_i synth1 synth2;
      obtain ⟨_, _⟩ := synth1
      obtain ⟨_, _⟩ := synth2
      obtain ⟨_, _, _⟩ := Hψ
      and_intros <;> subst_vars <;> simp
      . assumption
      . assumption

private theorem internals_preserves_ψ: ∀ i i' s s',
  ψ i s → existSR (rhsModule T₁ T₂ T₃).internals i i' → existSR (lhsModule T₁ T₂ T₃).internals s s' → ψ i' s' :=
by
  intros i i' s s' _ _ _
  have: ψ i s' := by
    apply ψ_holds_over_internals_spec <;> assumption
  apply ψ_holds_over_internals_impl <;> assumption

private theorem inputs_preserves_ψ: ∀ ident i₁ i₂ v s₁ s₂,
  ψ i₁ s₁
  → ((rhsModule T₁ T₂ T₃).inputs.getIO ident).snd i₁ v i₂
  → ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ (coe_in.mp v) s₂
  → ψ i₂ s₂ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩  h₁ h₂ h₃
  by_cases HContains: (rhsModule T₁ T₂ T₃).inputs.contains ident
  . simp [rhsModule] at HContains
    rcases HContains with h | h | h <;> subst h
    . --
      unfold lhsModule at h₃
      rw [PortMap.rw_rule_execution] at h₃
      simp at h₃
      obtain ⟨⟨_, _⟩, _, _⟩ := h₃
      --
      unfold rhsModule at h₂
      rw [PortMap.rw_rule_execution] at h₂
      simp at h₂
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := h₂
      --
      obtain ⟨_, _, _⟩ := h₁
      --
      subst_vars
      --
      dsimp [ψ]
      and_intros
      . rw [<- List.append_assoc, <- List.append_assoc]
        congr
      . assumption
      . rfl
    . --
      unfold lhsModule at h₃
      rw [PortMap.rw_rule_execution] at h₃
      simp at h₃
      obtain ⟨⟨_, _⟩, _, _⟩ := h₃
      --
      --
      unfold rhsModule at h₂
      rw [PortMap.rw_rule_execution] at h₂
      simp at h₂
      obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := h₂
      --
      obtain ⟨_, _, _⟩ := h₁
      subst_vars
      dsimp [ψ]
      and_intros
      . assumption
      . rw [<- List.append_assoc, <- List.append_assoc]
        congr
      . rfl
    . --
      unfold lhsModule at h₃
      rw [PortMap.rw_rule_execution] at h₃
      simp at h₃
      obtain ⟨⟨_, _⟩, _, _⟩ := h₃
      --
      --
      unfold rhsModule at h₂
      rw [PortMap.rw_rule_execution] at h₂
      simp at h₂
      obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := h₂
      --
      obtain ⟨_, _, _⟩ := h₁
      --
      subst_vars
      --
      dsimp [ψ]
      and_intros
      . assumption
      . assumption
      . simp
  . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains)

private theorem outputs_preserves_ψ: ∀ ident i₁ i₂ v s₁ s₂,
  ψ i₁ s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ ↑v i₂
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ (coe_out.mp v) s₂
  → ψ i₂ s₂ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [rhsModule] at HContains; subst HContains
    unfold rhsModule at h₂
    rw [PortMap.rw_rule_execution] at h₂; simp at h₂
    repeat
      cases ‹_ ∧ _›
    simp at *
    cases ‹_ ∧ _›
    subst_vars

    dsimp [ψ]
    and_intros <;> simp at * <;> assumption
  . exfalso; exact (PortMap.getIO_not_contained_false h₃ HContains)

instance: SimulationRelation ψ (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := {
  inputs_preserved    := inputs_preserves_ψ
  internals_preserved := internals_preserves_ψ
  outputs_preserved   := outputs_preserves_ψ
  initial_state_preserves := by
    intro ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂
    obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := h₁
    obtain ⟨⟨_, _⟩, _, _⟩ := h₂
    trivial
}

end SimulationRelation

section Determinism

instance: Deterministic (lhsModule T₁ T₂ T₃) where
  input_deterministic := by
    intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
    by_cases HContains: ((lhsModule T₁ T₂ T₃).inputs.contains ident)
    . simp [lhsModule] at HContains
      rcases HContains with h | h | h <;> subst h
      all_goals
        dsimp [lhsModule] at h₁ h₂
        rw [PortMap.rw_rule_execution] at h₁ h₂
        dsimp at h₁ h₂
        repeat
          cases ‹_ ∧ _›
          try simp at *
          try subst_vars
        rfl
    . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)
  internal_deterministic := by
    intro _ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
    simp [lhsModule] at *
    subst_vars
    dsimp at h₁ h₂
    obtain ⟨_, _, _, _, _, _, _⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _⟩ := h₂
    repeat
      cases ‹_ ∧ _›
      try simp at *
      try subst_vars
    rfl
  output_deterministic := by
    intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
    by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
    . simp [lhsModule] at HContains; subst HContains
      dsimp [lhsModule] at h₁ h₂
      rw [PortMap.rw_rule_execution] at h₁ h₂
      dsimp at h₁ h₂
      repeat
        cases ‹_ ∧ _›
        try simp at *
        try subst_vars
      rfl
    . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains)

-- TODO: THIS PROOF IS VERY SLOW, WE SHOULD IMPROVE ITS PERFORMANCE
-- NOTE: THIS IS VERY MECHANICAL, WE CAN BUILD TACTICS TO SOLVE THINGS HERE
instance: Deterministic (rhsModule T₁ T₂ T₃) where
  input_deterministic := by
    intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩, _⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩, _⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩, _⟩ h₁ h₂
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . simp [rhsModule] at HContains <;> rcases HContains with h | h | h <;> subst h
      . simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
        obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := h₁ <;> subst_vars
        simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
        obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := h₂ <;> subst_vars
        rfl
      . simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
        obtain ⟨⟨⟨_, _⟩, _⟩, _, _⟩ := h₁ <;> subst_vars
        simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
        obtain ⟨⟨⟨_, _⟩, _⟩, _, _⟩ := h₂ <;> subst_vars
        rfl
      . simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
        obtain ⟨⟨⟨_, _⟩, _⟩, _, _⟩ := h₁ <;> subst_vars
        simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
        obtain ⟨⟨⟨_, _⟩, _⟩, _, _⟩ := h₂ <;> subst_vars
        rfl
    . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains)
  internal_deterministic := by
    intro _ hᵣ ⟨⟨_ , _⟩, ⟨_ , _⟩, _⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩, _⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩, _⟩ h₁ h₂
    simp [rhsModule] at hᵣ <;> cases hᵣ <;> subst_vars
    . simp at h₁ <;> obtain ⟨_, _, ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩⟩ := h₁ <;> subst_vars
      simp at h₂ <;> obtain ⟨_, _, ⟨_, _⟩, _⟩ := h₂ <;> subst_vars
      rfl
    . simp at h₁ <;> obtain ⟨_, _, _, ⟨⟨_, _⟩, ⟨_, _, _⟩⟩⟩ := h₁ <;> subst_vars
      simp at h₂ <;> obtain ⟨⟨_, _, _⟩, _, _⟩ := h₂ <;> subst_vars
      rfl
  output_deterministic := by
    intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩, _⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩, _⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩, _⟩ h₁ h₂
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . simp [rhsModule] at HContains; subst HContains
      simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
      obtain ⟨⟨_, _, _⟩, _, _⟩ := h₁ <;> subst_vars
      simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
      obtain ⟨⟨_, _, _⟩, _, _⟩ := h₂ <;> subst_vars
      rfl
    . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains)

end Determinism

section Confluence

-- TODO: BETTER PROVE LOCAL CONFLUENCE AND FLUSHABILITY? IS IT TRUE OR NOT
--instance: LocallyConfluent (lhsModule T₁ T₂ T₃) := by sorry
instance gcl: GloballyConfluent (lhsModule T₁ T₂ T₃) := by infer_instance

/--
info: 'Graphiti.JoinRewrite.gcl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms gcl

-- TODO: BETTER PROVE LOCAL CONFLUENCE AND FLUSHABILITY?
--instance: LocallyConfluent (rhsModule T₁ T₂ T₃) := by sorry
instance gcr: GloballyConfluent (rhsModule T₁ T₂ T₃) := by
  sorry

/--
info: 'Graphiti.JoinRewrite.gcr' depends on axioms: [sorryAx]
-/
#guard_msgs in
#print axioms gcr

end Confluence

section RuleSwapping

instance: RuleStronglySwapWithMethods (lhsModule T₁ T₂ T₃) where
  inputs  := by
    intros ident s₁ v s₂ s₃ rule hᵣ h₁ h₂
    by_cases HContains: ((lhsModule T₁ T₂ T₃).inputs.contains ident)
    . simp [lhsModule] at HContains <;> rcases HContains with h | h | h <;> subst h
      . obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩⟩ := s₁
        obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩⟩ := s₂
        obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩⟩ := s₃
        simp [lhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
        obtain ⟨⟨_, _⟩, _, _⟩ := h₁ <;> subst_vars
        -- WE CHECK NOW IF WE CAN SWAP IT WITH EACH INTERNAL RULE
        simp [lhsModule] at hᵣ <;> subst hᵣ <;> simp at ⊢ h₂
        obtain ⟨v₁, v₂, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩ := h₂ <;> subst_vars
        reduce at v -- TODO: GET RID OF IT
        use ((q₁s₂ ++ [(v₁, v₂)], q₂s₃ ++ [v]), q₃s₃, q₄s₃) <;> apply And.intro
        . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
        . simp
      . obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩⟩ := s₁
        obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩⟩ := s₂
        obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩⟩ := s₃
        simp [lhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
        obtain ⟨⟨_, _⟩, _, _⟩ := h₁ <;> subst_vars
        -- WE CHECK NOW IF WE CAN SWAP IT WITH EACH INTERNAL RULE
        simp [lhsModule] at hᵣ <;> subst hᵣ <;> simp at ⊢ h₂
        obtain ⟨v₁, v₂, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩ := h₂ <;> subst_vars
        reduce at v -- TODO: GET RID OF IT
        use ((q₁s₂ ++ [(v₁, v₂)], q₂s₃), q₃s₃ ++ [v], q₄s₃) <;> apply And.intro
        . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
        . simp
      . obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩⟩ := s₁
        obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩⟩ := s₂
        obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩⟩ := s₃
        simp [lhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
        obtain ⟨⟨_, _⟩, _, _⟩ := h₁ <;> subst_vars
        -- WE CHECK NOW IF WE CAN SWAP IT WITH EACH INTERNAL RULE
        simp [lhsModule] at hᵣ <;> subst hᵣ <;> simp at ⊢ h₂
        obtain ⟨v₁, v₂, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩ := h₂ <;> subst_vars
        reduce at v -- TODO: GET RID OF IT
        use ((q₁s₂ ++ [(v₁, v₂)], q₂s₃), q₃s₃, q₄s₃ ++ [v]) <;> apply And.intro
        . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
        . simp
    . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains)
  outputs := by
    intros ident s₁ v s₂ s₃ rule hᵣ h₁ h₂
    by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
    . simp [lhsModule] at HContains <;> subst HContains
      obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩⟩ := s₁
      obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩⟩ := s₂
      obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩⟩ := s₃
      simp [lhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
      obtain ⟨⟨_, _⟩, _, _⟩ := h₁ <;> subst_vars
      -- WE CHECK NOW IF WE CAN SWAP IT WITH EACH INTERNAL RULE
      simp [lhsModule] at hᵣ <;> subst hᵣ <;> simp at h₂
      obtain ⟨v₁, v₂, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩ := h₂ <;> subst_vars
      use ⟨⟨q₁s₂ ++ [(v₁, v₂)], q₂s₂⟩, ⟨q₃s₃, q₄s₃⟩⟩ <;> apply And.intro
      . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
      . simp
    . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains)

-- TODO: IMPROVE THE PERFORMANCE OF THIS PROOF
set_option maxHeartbeats 0 in instance: RuleStronglySwapWithMethods (rhsModule T₁ T₂ T₃) where
  inputs  := by
    intros ident s₁ v s₂ s₃ rule hᵣ h₁ h₂
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . simp [rhsModule] at HContains <;> rcases HContains with h | h | h <;> subst h
      . obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩, q₅s₂⟩ := s₂
        obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
        obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := h₁ <;> subst_vars
        -- WE CHECK NOW IF WE CAN SWAP IT WITH EACH INTERNAL RULE
        simp [rhsModule] at hᵣ <;> rcases hᵣ with h | h <;> subst h <;> simp at h₂
        . obtain ⟨a, b, ⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
          reduce at v -- TODO: GET RID OF IT
          use ((q₁s₃ ++ [v], q₂s₂ ++ [(a, b)]), (q₃s₃, q₄s₃), q₅s₃) <;> apply And.intro
          . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp
        . obtain ⟨a, b, c, ⟨_, _⟩, ⟨_, _, _⟩⟩ := h₂ <;> subst_vars
          reduce at v -- TODO: GET RID OF IT
          use ((q₁s₃ ++ [v], q₂s₃), (q₃s₃, q₄s₃), q₅s₂ ++ [((a, b), c)]) <;> apply And.intro
          . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp
      . obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩, q₅s₂⟩ := s₂
        obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
        obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
        -- WE CHECK NOW IF WE CAN SWAP IT WITH EACH INTERNAL RULE
        simp [rhsModule] at hᵣ <;> rcases hᵣ with h | h <;> subst h <;> simp at h₂
        . obtain ⟨a, b, ⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
          reduce at v -- TODO: GET RID OF IT
          use ((q₁s₃, q₂s₂ ++ [(a, b)]), (q₃s₃ ++ [v], q₄s₃), q₅s₃) <;> apply And.intro
          . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp
        . obtain ⟨a, b, c, ⟨_, _⟩, ⟨_, _, _⟩⟩ := h₂ <;> subst_vars
          reduce at v -- TODO: GET RID OF IT
          use ((q₁s₃, q₂s₃), (q₃s₃ ++ [v], q₄s₃), q₅s₂ ++ [((a, b), c)]) <;> apply And.intro
          . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp
      . obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩, q₅s₂⟩ := s₂
        obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
        obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
        -- WE CHECK NOW IF WE CAN SWAP IT WITH EACH INTERNAL RULE
        simp [rhsModule] at hᵣ <;> rcases hᵣ with h | h <;> subst h <;> simp at h₂
        . obtain ⟨a, b, ⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
          reduce at v -- TODO: GET RID OF IT
          use ((q₁s₃, q₂s₂ ++ [(a, b)]), (q₃s₃, q₄s₃ ++ [v]), q₅s₃) <;> apply And.intro
          . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp
        . obtain ⟨a, b, c, ⟨_, _⟩, ⟨_, _, _⟩⟩ := h₂ <;> subst_vars
          reduce at v -- TODO: GET RID OF IT
          use ((q₁s₃, q₂s₃), (q₃s₃, q₄s₃ ++ [v]), q₅s₂ ++ [((a, b), c)]) <;> apply And.intro
          . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp
    . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains)
  outputs := by
    intros ident s₁ v s₂ s₃ rule hᵣ h₁ h₂
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . simp [rhsModule] at HContains <;> subst HContains
      obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
      obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩, q₅s₂⟩ := s₂
      obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
      simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> simp at h₁
      obtain ⟨⟨_, _, _⟩, _, _⟩ := h₁ <;> subst_vars
      -- WE CHECK NOW IF WE CAN SWAP IT WITH EACH INTERNAL RULE
      simp [rhsModule] at hᵣ <;> rcases hᵣ with h | h <;> subst h <;> simp at h₂
      . obtain ⟨a, b, ⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
        use ((q₁s₃, q₂s₂ ++ [(a, b)]), (q₃s₃, q₄s₃), q₅s₂) <;> apply And.intro
        . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
        . simp
      . obtain ⟨a, b, c, ⟨_, _⟩, ⟨_, _, _⟩⟩ := h₂ <;> subst_vars
        use ((q₁s₃, q₂s₃), (q₃s₃, q₄s₃), (q₅s₂ ++ [((a, b), c)])) <;> apply And.intro
        . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
        . simp
    . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains)

-- THIS IS PROVABLE :)
-- TODO: I ACTUALLY COULD USE THE PRETTY VERSION OF IT BY SHOWING THE QUANTIFIED VERSION
--       AND HAVE THE LAMBDA RETURN THAT VALUE AND DISCARD THE INPUT:)
set_option maxHeartbeats 0 in instance dassr: DistinctActionStronglySwaps' (rhsModule T₁ T₂ T₃) where
  inputs := by
    intros ident₁ ident₂ s₁ v₂ s' s₃ h h₁ h₂
    by_cases HContains₁: (rhsModule T₁ T₂ T₃).inputs.contains ident₁
    . simp [rhsModule] at HContains₁ <;> rcases HContains₁ with h | h | h <;> subst h
      . obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        use (λ v: T₁ => ⟨⟨q₁s₃ ++ [v], q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩)
        intro v₁ <;> specialize h₁ v₁ <;> reduce at v₁
        obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        have: (s' v₁) = ⟨⟨q₁s₁ ++ [v₁], q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := by
          have: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).snd ((q₁s₁, q₂s₁), (q₃s₁, q₄s₁), q₅s₁) v₁ ⟨⟨q₁s₁ ++ [v₁], q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := by
            dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp <;> grind
          have det: DeterministicInputs (rhsModule T₁ T₂ T₃) := by infer_instance
          apply det.input_deterministic <;> assumption
        rewrite [this] <;> clear h₁ this
        by_cases HContains₂: (rhsModule T₁ T₂ T₃).inputs.contains ident₂
        . simp [rhsModule] at HContains₂ <;> rcases HContains₂ with h | h | h <;> subst h
          . contradiction
          . simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
            and_intros <;> grind
          . simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
            and_intros <;> grind
        . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
      . obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        use (λ v: T₂ => ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃ ++ [v], q₄s₃⟩, q₅s₃⟩)
        intro v₁ <;> specialize h₁ v₁ <;> reduce at v₁
        obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        have: (s' v₁) = ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁ ++ [v₁], q₄s₁⟩, q₅s₁⟩ := by
          have: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).snd ((q₁s₁, q₂s₁), (q₃s₁, q₄s₁), q₅s₁) v₁ ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁ ++ [v₁], q₄s₁⟩, q₅s₁⟩ := by
            dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp <;> grind
          have det: DeterministicInputs (rhsModule T₁ T₂ T₃) := by infer_instance
          apply det.input_deterministic <;> assumption
        rewrite [this] <;> clear h₁ this
        by_cases HContains₂: (rhsModule T₁ T₂ T₃).inputs.contains ident₂
        . simp [rhsModule] at HContains₂ <;> rcases HContains₂ with h | h | h <;> subst h
          . simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
            and_intros <;> grind
          . contradiction
          . simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
            and_intros <;> grind
        . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
      . obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        use (λ v: T₃ => ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃ ++ [v]⟩, q₅s₃⟩)
        intro v₁ <;> specialize h₁ v₁ <;> reduce at v₁
        obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        have: (s' v₁) = ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁ ++ [v₁]⟩, q₅s₁⟩ := by
          have: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).snd ((q₁s₁, q₂s₁), (q₃s₁, q₄s₁), q₅s₁) v₁ ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁ ++ [v₁]⟩, q₅s₁⟩ := by
            dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp <;> grind
          have det: DeterministicInputs (rhsModule T₁ T₂ T₃) := by infer_instance
          apply det.input_deterministic <;> assumption
        rewrite [this] <;> clear h₁ this
        by_cases HContains₂: (rhsModule T₁ T₂ T₃).inputs.contains ident₂
        . simp [rhsModule] at HContains₂ <;> rcases HContains₂ with h | h | h <;> subst h
          . simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
            and_intros <;> grind
          . simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
            and_intros <;> grind
          . contradiction
        . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
    . use s'
      intro v₁ <;> specialize h₁ v₁
      exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains₁)
  /-outputs := by
    intros ident₁ ident₂ s₁ v₂ s' s₃ h h₁ h₂
    by_cases HContains₁: (rhsModule T₁ T₂ T₃).outputs.contains ident₁
    . by_cases HContains₂: (rhsModule T₁ T₂ T₃).outputs.contains ident₂
      . simp [rhsModule] at HContains₁ HContains₂
        subst HContains₁ HContains₂
        contradiction
      . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
    . use s' <;> intro v₁
      specialize h₁ v₁
      exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains₁)-/
  in_out  := by
    intros ident₁ ident₂ s₁ v₂ s' s₃ h₁ h₂
    by_cases HContains₁: (rhsModule T₁ T₂ T₃).inputs.contains ident₁
    . simp [rhsModule] at HContains₁ <;> rcases HContains₁ with h | h | h <;> subst h
      . obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        use (λ v: T₁ => ⟨⟨q₁s₃ ++ [v], q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩)
        intro v₁ <;> specialize h₁ v₁ <;> reduce at v₁
        obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        have: (s' v₁) = ⟨⟨q₁s₁ ++ [v₁], q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := by
          have: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).snd ((q₁s₁, q₂s₁), (q₃s₁, q₄s₁), q₅s₁) v₁ ⟨⟨q₁s₁ ++ [v₁], q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := by
            dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp <;> grind
          have det: DeterministicInputs (rhsModule T₁ T₂ T₃) := by infer_instance
          apply det.input_deterministic <;> assumption
        rewrite [this] <;> clear h₁ this
        by_cases HContains₂: (rhsModule T₁ T₂ T₃).outputs.contains ident₂
        . simp [rhsModule] at HContains₂ <;> subst HContains₂
          simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
          and_intros <;> grind
        . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
      . obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        use (λ v: T₂ => ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃ ++ [v], q₄s₃⟩, q₅s₃⟩)
        intro v₁ <;> specialize h₁ v₁ <;> reduce at v₁
        obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        have: (s' v₁) = ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁ ++ [v₁], q₄s₁⟩, q₅s₁⟩ := by
          have: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).snd ((q₁s₁, q₂s₁), (q₃s₁, q₄s₁), q₅s₁) v₁ ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁ ++ [v₁], q₄s₁⟩, q₅s₁⟩ := by
            dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp <;> grind
          have det: DeterministicInputs (rhsModule T₁ T₂ T₃) := by infer_instance
          apply det.input_deterministic <;> assumption
        rewrite [this] <;> clear h₁ this
        by_cases HContains₂: (rhsModule T₁ T₂ T₃).outputs.contains ident₂
        . simp [rhsModule] at HContains₂ <;> subst HContains₂
          simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
          and_intros <;> grind
        . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
      . obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        use (λ v: T₃ => ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃ ++ [v]⟩, q₅s₃⟩)
        intro v₁ <;> specialize h₁ v₁ <;> reduce at v₁
        obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        have: (s' v₁) = ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁ ++ [v₁]⟩, q₅s₁⟩ := by
          have: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).snd ((q₁s₁, q₂s₁), (q₃s₁, q₄s₁), q₅s₁) v₁ ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁ ++ [v₁]⟩, q₅s₁⟩ := by
            dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp <;> grind
          have det: DeterministicInputs (rhsModule T₁ T₂ T₃) := by infer_instance
          apply det.input_deterministic <;> assumption
        rewrite [this] <;> clear h₁ this
        by_cases HContains₂: (rhsModule T₁ T₂ T₃).outputs.contains ident₂
        . simp [rhsModule] at HContains₂ <;> subst HContains₂
          simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
          and_intros <;> grind
        . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
    . use s' <;> intro v₁
      specialize h₁ v₁
      exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains₁)
  /-out_in  := by
    intros ident₁ ident₂ s₁ v₂ s' s₃ h₁ h₂
    by_cases HContains₁: (rhsModule T₁ T₂ T₃).outputs.contains ident₁
    . simp [rhsModule] at HContains₁ <;> subst HContains₁
      obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
      use (λ v => ⟨⟨[], []⟩, ⟨[], []⟩, []⟩) -- TODO: FIX THIS
      intro v₁ <;> specialize h₁ v₁
      by_cases HContains₂: (rhsModule T₁ T₂ T₃).inputs.contains ident₂
      . simp [rhsModule] at HContains₂ <;> rcases HContains₂ with h | h | h <;> subst h
        . sorry
        . sorry
        . sorry
      . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
    . use s' <;> intro v₁
      specialize h₁ v₁
      exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains₁)-/
  in_int  := by
    intros ident s₁ s' s₃ rule hᵣ h₁ h₂
    by_cases HContains₁: (rhsModule T₁ T₂ T₃).inputs.contains ident
    . simp [rhsModule] at HContains₁ <;> rcases HContains₁ with h | h | h <;> subst h
      . obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        use (λ v: T₁ => ⟨⟨q₁s₃ ++ [v], q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩)
        intro v₁ <;> specialize h₁ v₁ <;> reduce at v₁
        obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        have: (s' v₁) = ⟨⟨q₁s₁ ++ [v₁], q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := by
          have: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).snd ((q₁s₁, q₂s₁), (q₃s₁, q₄s₁), q₅s₁) v₁ ⟨⟨q₁s₁ ++ [v₁], q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := by
            dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp <;> grind
          have det: DeterministicInputs (rhsModule T₁ T₂ T₃) := by infer_instance
          apply det.input_deterministic <;> assumption
        rewrite [this] <;> clear h₁ this
        simp [rhsModule] at hᵣ <;> rcases hᵣ with h | h <;> subst h
        . simp at ⊢ h₂ <;> and_intros <;> grind
        . simp at ⊢ h₂ <;> and_intros <;> grind
      . obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        use (λ v: T₂ => ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃ ++ [v], q₄s₃⟩, q₅s₃⟩)
        intro v₁ <;> specialize h₁ v₁ <;> reduce at v₁
        obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        have: (s' v₁) = ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁ ++ [v₁], q₄s₁⟩, q₅s₁⟩ := by
          have: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).snd ((q₁s₁, q₂s₁), (q₃s₁, q₄s₁), q₅s₁) v₁ ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁ ++ [v₁], q₄s₁⟩, q₅s₁⟩ := by
            dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp <;> grind
          have det: DeterministicInputs (rhsModule T₁ T₂ T₃) := by infer_instance
          apply det.input_deterministic <;> assumption
        rewrite [this] <;> clear h₁ this
        simp [rhsModule] at hᵣ <;> rcases hᵣ with h | h <;> subst h
        . simp at ⊢ h₂ <;> and_intros <;> grind
        . simp at ⊢ h₂ <;> and_intros <;> grind
      . obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
        use (λ v: T₃ => ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃ ++ [v]⟩, q₅s₃⟩)
        intro v₁ <;> specialize h₁ v₁ <;> reduce at v₁
        obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
        have: (s' v₁) = ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁ ++ [v₁]⟩, q₅s₁⟩ := by
          have: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).snd ((q₁s₁, q₂s₁), (q₃s₁, q₄s₁), q₅s₁) v₁ ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁ ++ [v₁]⟩, q₅s₁⟩ := by
            dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp <;> grind
          have det: DeterministicInputs (rhsModule T₁ T₂ T₃) := by infer_instance
          apply det.input_deterministic <;> assumption
        rewrite [this] <;> clear h₁ this
        simp [rhsModule] at hᵣ <;> rcases hᵣ with h | h <;> subst h
        . simp at ⊢ h₂ <;> and_intros <;> grind
        . simp at ⊢ h₂ <;> and_intros <;> grind
    . use s' <;> intro v₁
      specialize h₁ v₁
      exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains₁)
  /-out_int := by
    intros ident s₁ s' s₃ h₁ h₂
    by_cases HContains₁: (rhsModule T₁ T₂ T₃).outputs.contains ident
    . simp [rhsModule] at HContains₁ <;> subst HContains₁
      use (λ v => ⟨⟨[], []⟩, ⟨[], []⟩, []⟩) -- TODO: FIX THIS
      intro v <;> specialize h₁ v
      sorry
    . use s' <;> intro v₁
      specialize h₁ v₁
      exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains₁)-/

/--
info: 'Graphiti.JoinRewrite.dassr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms dassr

-- TODO: IT WOULD BE NICE TO PROVE IT ON THE NON-FLUSHED MODULE. CAN WE?
instance [RuleSwapWithMethods (lhsModule T₁ T₂ T₃)]: DistinctActionSwaps' (flushed (lhsModule T₁ T₂ T₃)) where
  inputs  := by
    have ⟨fl, hfl⟩ := @flushed_fn _ _ _ (lhsModule T₁ T₂ T₃) _ _
    have mm: MatchInterface (flushed (lhsModule T₁ T₂ T₃)) (lhsModule T₁ T₂ T₃) := by infer_instance
    intros ident₁ ident₂ s₁ v₂ s' s₃ h h₁ h₂
    by_cases HContains₁: (flushed (lhsModule T₁ T₂ T₃)).inputs.contains ident₁
    . rewrite [@match_interface_inputs_contains _ _ _ _ _ _ mm] at HContains₁
      simp [lhsModule] at HContains₁ <;> rcases HContains₁ with h | h | h <;> subst h
      . -- TODO: We need to have a function that do the flushing...
        obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩⟩ := s₃
        use (λ v: T₃ => fl ⟨⟨q₁s₃, q₂s₃ ++ [v]⟩, ⟨q₃s₃, q₄s₃⟩⟩) <;> dsimp
        intro v₁ <;> specialize h₁ v₁ <;> reduce at v₁
        obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩⟩ := s₁
        have: (s' v₁) = fl ⟨⟨q₁s₁, q₂s₁ ++ [v₁]⟩, ⟨q₃s₁, q₄s₁⟩⟩ := by
          have: ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO { inst := InstIdent.top, name := "i_2" }).snd ((q₁s₁, q₂s₁), (q₃s₁, q₄s₁)) v₁ (fl ⟨⟨q₁s₁, q₂s₁ ++ [v₁]⟩, ⟨q₃s₁, q₄s₁⟩⟩) := by
            --dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp <;> grind
            sorry
          --have det: DeterministicInputs (rhsModule T₁ T₂ T₃) := by infer_instance
          --apply det.input_deterministic <;> assumption
          sorry
        rewrite [this] <;> clear h₁ this
        by_cases HContains₂: (flushed (lhsModule T₁ T₂ T₃)).inputs.contains ident₂
        . rewrite [@match_interface_inputs_contains _ _ _ _ _ _ mm] at HContains₂
          simp [lhsModule] at HContains₂ <;> rcases HContains₂ with h | h | h <;> subst h
          . contradiction
          . clear h
            apply And.intro
            . rewrite [flushed_inputs_are_rflushed] at ⊢ h₂
              dsimp [rflushed] at ⊢ h₂
              obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, h₂, h₂'⟩ := h₂
              simp [lhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> simp at h₂
              obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
              rewrite [hfl] at h₂'





              sorry
            . rewrite [flushed_inputs_are_rflushed]
              dsimp [rflushed]
              use ⟨⟨q₁s₃, q₂s₃ ++ [v₁]⟩, ⟨q₃s₃, q₄s₃⟩⟩ <;> apply And.intro
              . and_intros <;> grind
              . rw [hfl]
          . clear h
            sorry
        . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
      . sorry
      . sorry
    . use s'
      intro v <;> specialize h₁ v
      exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains₁)
  --outputs := by sorry
  in_out  := by
    intros ident₁ ident₂ s₁ v₂ s' s₃ h₁ h₂
    sorry
  --out_in  := sorry
  in_int  := by
    intros ident s₁ s' s₃ h₁ h₂
    apply existSR_norules at h₂ <;> subst h₂
    use s'
    intro v <;> specialize h₁ v
    refine ⟨h₁, existSR_reflexive⟩
  --out_int := sorry

/-set_option maxHeartbeats 0 in instance: DistinctActionStronglySwaps (rhsModule T₁ T₂ T₃) where
  inputs    := by
    intro ident₁ ident₂ s₁ v₁ v₂ s₂ s₃ h h₁ h₂
    by_cases HContains₁: (rhsModule T₁ T₂ T₃).inputs.contains ident₁
    . by_cases HContains₂: (rhsModule T₁ T₂ T₃).inputs.contains ident₂
      . simp [rhsModule] at HContains₁ <;> rcases HContains₁ with h | h | h <;> subst h
        . simp [rhsModule] at HContains₂ <;> rcases HContains₂ with h | h | h <;> subst h
          . contradiction
          . clear h
            obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
            obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩, q₅s₂⟩ := s₂
            obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
            simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
            obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := h₁ <;> subst_vars
            simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
            obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
            reduce at v₁ v₂
            use ((q₁s₁ ++ [v₁], q₂s₂), (q₃s₁ ++ [v₂], q₄s₃), q₅s₃) <;> apply And.intro
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . clear h
            obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
            obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩, q₅s₂⟩ := s₂
            obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
            simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
            obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := h₁ <;> subst_vars
            simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
            obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
            reduce at v₁ v₂
            use ((q₁s₁ ++ [v₁], q₂s₂), (q₃s₃, q₄s₁ ++ [v₂]), q₅s₃) <;> apply And.intro
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
        . simp [rhsModule] at HContains₂ <;> rcases HContains₂ with h | h | h <;> subst h
          . clear h
            obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
            obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩, q₅s₂⟩ := s₂
            obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
            simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
            obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
            simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
            obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := h₂ <;> subst_vars
            reduce at v₁ v₂
            use ((q₁s₁ ++ [v₂], q₂s₃), (q₃s₁ ++ [v₁], q₄s₂), q₅s₂) <;> apply And.intro
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . contradiction
          . clear h
            obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
            obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩, q₅s₂⟩ := s₂
            obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
            simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
            obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
            simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
            obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
            reduce at v₁ v₂
            use ((q₁s₁, q₂s₁), (q₃s₃ ++ [v₁], q₄s₂ ++ [v₂]), q₅s₃) <;> apply And.intro
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
        . simp [rhsModule] at HContains₂ <;> rcases HContains₂ with h | h | h <;> subst h
          . clear h
            obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
            obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩, q₅s₂⟩ := s₂
            obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
            simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
            obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
            simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
            obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := h₂ <;> subst_vars
            reduce at v₁ v₂
            use ((q₁s₁ ++ [v₂], q₂s₃), (q₃s₂, q₄s₁ ++ [v₁]), q₅s₂) <;> apply And.intro
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . clear h
            obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩, q₅s₁⟩ := s₁
            obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩, q₅s₂⟩ := s₂
            obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩, q₅s₃⟩ := s₃
            simp [rhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
            obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
            simp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
            obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
            reduce at v₁ v₂
            use ((q₁s₁, q₂s₁), (q₃s₂ ++ [v₂], q₄s₃ ++ [v₁]), q₅s₃) <;> apply And.intro
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
            . simp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . contradiction
      . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
    . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains₁)
  internals := by
    sorry
  outputs   := by
    intro ident₁ ident₂ s₁ v₁ v₂ s₂ s₃ h h₁ h₂
    by_cases HContains₁: (rhsModule T₁ T₂ T₃).outputs.contains ident₁
    . by_cases HContains₂: (rhsModule T₁ T₂ T₃).outputs.contains ident₂
      . simp [rhsModule] at HContains₁ <;> simp [rhsModule] at HContains₂
        subst HContains₁ HContains₂
        contradiction
      . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
    . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains₁)
-/

/-set_option maxHeartbeats 0 in instance: DistinctActionStronglySwaps (lhsModule T₁ T₂ T₃) where
  inputs    := by
    intro ident₁ ident₂ s₁ v₁ v₂ s₂ s₃ h h₁ h₂
    by_cases HContains₁: (lhsModule T₁ T₂ T₃).inputs.contains ident₁
    . by_cases HContains₂: (lhsModule T₁ T₂ T₃).inputs.contains ident₂
      simp [lhsModule] at HContains₁ <;> rcases HContains₁ with h | h | h <;> subst h
      . simp [lhsModule] at HContains₂ <;> rcases HContains₂ with h | h | h <;> subst h
        . contradiction
        . clear h
          obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩⟩ := s₁
          obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩⟩ := s₂
          obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩⟩ := s₃
          simp [lhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
          simp [lhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
          reduce at v₁ v₂
          use ((q₁s₂, q₂s₁ ++ [v₁]), q₃s₁ ++ [v₂], q₄s₃) <;> apply And.intro
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
        . clear h
          obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩⟩ := s₁
          obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩⟩ := s₂
          obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩⟩ := s₃
          simp [lhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
          simp [lhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
          reduce at v₁ v₂
          use ((q₁s₂, q₂s₁ ++ [v₁]), q₃s₃, q₄s₁ ++ [v₂]) <;> apply And.intro
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
      . simp [lhsModule] at HContains₂ <;> rcases HContains₂ with h | h | h <;> subst h
        . clear h
          obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩⟩ := s₁
          obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩⟩ := s₂
          obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩⟩ := s₃
          simp [lhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
          simp [lhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
          reduce at v₁ v₂
          use ((q₁s₃, q₂s₁ ++ [v₂]), q₃s₁ ++ [v₁], q₄s₂) <;> apply And.intro
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
        . contradiction
        . clear h
          obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩⟩ := s₁
          obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩⟩ := s₂
          obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩⟩ := s₃
          simp [lhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
          simp [lhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
          reduce at v₁ v₂
          use ((q₁s₁, q₂s₁), q₃s₃ ++ [v₁], q₄s₂ ++ [v₂]) <;> apply And.intro
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
      . simp [lhsModule] at HContains₂ <;> rcases HContains₂ with h | h | h <;> subst h
        . clear h
          obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩⟩ := s₁
          obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩⟩ := s₂
          obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩⟩ := s₃
          simp [lhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
          simp [lhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
          reduce at v₁ v₂
          use ((q₁s₃, q₂s₁ ++ [v₂]), q₃s₂, q₄s₁ ++ [v₁]) <;> apply And.intro
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
        . clear h
          obtain ⟨⟨q₁s₁, q₂s₁⟩, ⟨q₃s₁, q₄s₁⟩⟩ := s₁
          obtain ⟨⟨q₁s₂, q₂s₂⟩, ⟨q₃s₂, q₄s₂⟩⟩ := s₂
          obtain ⟨⟨q₁s₃, q₂s₃⟩, ⟨q₃s₃, q₄s₃⟩⟩ := s₃
          simp [lhsModule] at h₁ <;> rewrite [PortMap.rw_rule_execution] at h₁ <;> dsimp at h₁
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₁ <;> subst_vars
          simp [lhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂ <;> dsimp at h₂
          obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h₂ <;> subst_vars
          reduce at v₁ v₂
          use ((q₁s₁, q₂s₁), q₃s₂ ++ [v₂], q₄s₃ ++ [v₁]) <;> apply And.intro
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
          . simp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
        . contradiction
      . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
    . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains₁)
  internals := by
    sorry
  outputs   := by
    intro ident₁ ident₂ s₁ v₁ v₂ s₂ s₃ h h₁ h₂
    by_cases HContains₁: (lhsModule T₁ T₂ T₃).outputs.contains ident₁
    . by_cases HContains₂: (lhsModule T₁ T₂ T₃).outputs.contains ident₂
      . simp [lhsModule] at HContains₁ <;> simp [lhsModule] at HContains₂
        subst HContains₁ HContains₂
        contradiction
      . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains₂)
    . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains₁)

instance: DistinctActionStronglySwaps (flushed (lhsModule T₁ T₂ T₃)) := by infer_instance
-/

-- TODO: CAN WE DERIVE THESE PROPERTIES WITH CONNECTIONS?
-- IF WE CAN DERIVE THEM WITH CONNECTIONS, WE SHOULD BE ABLE
-- TO GENERATE THEM AUTOMATICALLY

end RuleSwapping

---------------------------------------------------------------------------------------------------

private theorem lengthify {T₁: Type _} (a b: List T₁): a = b → a.length = b.length := by
  intro heq; rw [heq]

private theorem dropify {T₁: Type _} (l: ℕ) (l₁ l₂: List T₁): l₁ = l₂ -> List.drop l l₁ = List.drop l l₂ := by
  intro heq; rw [heq]

private theorem product_is_list_zip {T₁ T₂: Type _} (x: List (T₁ × T₂)):
  x = List.zip (List.map Prod.fst x) (List.map Prod.snd x) :=
by
  induction x with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.zip_cons_cons, <- ih]

private theorem append_iff {α} {a b c d : List α}:
  a.length = c.length → (a ++ b = c ++ d ↔ a = c ∧ b = d) :=
by
  intro lengths
  constructor
  . intro h
    and_intros
    . replace h := congrArg (List.take a.length) h
      rw [List.take_left, lengths, List.take_left] at h
      assumption
    . apply dropify a.length at h
      rw [List.drop_left, lengths, List.drop_left] at h
      assumption
  . intro ⟨_, _⟩; subst_vars; rfl

---------------------------------------------------------------------------------------------------
-------------------------- NON-FLUSHED, NON-INDUCTIVE ψ PROOF (BASELINE) --------------------------
---------------------------------------------------------------------------------------------------

section DirectRefinement

private def φ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  (ψ rhs lhs) ∧ (pf (lhsModule T₁ T₂ T₃) lhs)

private theorem refines₀_φ: rhsModule T₁ T₂ T₃ ⊑_{φ} lhsModule T₁ T₂ T₃ := by
  have flhs: Flushable (lhsModule T₁ T₂ T₃) := by infer_instance
  unfold Module.refines_φ
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  -- input rules
  . intro ident i s a
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := init_i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i
      unfold rhsModule at HContains; simp at HContains
      rcases HContains with h | h | h
        <;> subst_vars <;> simp <;> rw [PortMap.rw_rule_execution] at a <;> simp at a
      . obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst = _ := by dsimp [reducePortMapgetIO]
        -- We construct the almost_mid_s manually
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l ++ [heq.mp s], sj1r⟩⟩
        apply And.intro
        . -- verify that the rule holds
          rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
          simp only [eq_mp_eq_cast, cast_eq, List.concat_eq_append, and_self]
        . -- verify that the invariant holds when we flush the system
          obtain ⟨s', ⟨_, _⟩⟩ := flhs.flushable ⟨⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r⟩ -- We flush the system to reach s'
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply ψ_holds_over_internals_spec _ (⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . simp only [<- List.append_assoc, List.append_left_inj]
                  assumption
                . assumption
                . rfl
              . assumption
            . assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r ++ [s]⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := flhs.flushable ⟨⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply ψ_holds_over_internals_spec _ (⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . assumption
                . simp only [<- List.append_assoc, List.append_left_inj] at *
                  assumption
                . rfl
              . assumption
            . assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r ++ [s]⟩, ⟨sj1l, sj1r⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := flhs.flushable ⟨⟨sj2l, sj2r ++ [s]⟩, sj1l, sj1r⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply ψ_holds_over_internals_spec _ (⟨sj2l, sj2r  ++ [s]⟩, sj1l, sj1r) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . assumption
                . assumption
                . simp only [<- List.append_assoc, List.append_left_inj] at *
              . assumption
            . assumption
    . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
  -- output rules
  . intro ident i v hrule
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    · use init_s
      rw [exists_and_left]
      and_intros
      . apply existSR_reflexive
      . obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
        obtain ⟨⟨ij2l, ij2r⟩, ⟨ij1l, ij1r⟩, ip⟩ := init_i
        obtain ⟨⟨ij2l', ij2r'⟩, ⟨ij1l', ij1r'⟩, ip'⟩ := i
        unfold rhsModule at HContains; simp at HContains
        rcases HContains with h <;> subst_vars <;> simp
        rw [PortMap.rw_rule_execution (by simp [PortMap.getIO]; rfl)] at hrule <;>
        simp at hrule
        obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := hrule
        repeat cases ‹_∧_›
        subst_vars
        rename_i hlval hrval hpf
        dsimp at *
        rename_i htmp; cases htmp
        rewrite [pf_iff_partially_flushed] at hpf
        cases hpf
        · simp at hlval; simp at *
          rw [<- List.take_append_drop ij2l.length (List.map Prod.fst ij2r ++ ij1l)] at hrval
          --rw [<- List.append_assoc (List.map (Prod.snd ∘ Prod.fst) ip')] at hrval
          --rw [<- List.append.eq_2 _ _ ((List.map (Prod.snd ∘ Prod.fst) ip' ++ List.take ij2l.length (List.map Prod.fst ij2r' ++ ij1l'))] at hrval
          rw [show v.1.2 ::
              (List.map (Prod.snd ∘ Prod.fst) ip' ++
                (List.take ij2l.length (List.map Prod.fst ij2r ++ ij1l) ++
                  List.drop ij2l.length (List.map Prod.fst ij2r ++ ij1l))) = v.1.2 ::
              (List.map (Prod.snd ∘ Prod.fst) ip' ++
                List.take ij2l.length (List.map Prod.fst ij2r ++ ij1l)) ++
                  List.drop ij2l.length (List.map Prod.fst ij2r ++ ij1l) by simp] at hrval
          rw [append_iff] at hrval
          obtain ⟨hrvall, _⟩ := hrval
          . subst_vars
            apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
            and_intros <;> dsimp
            · rewrite [product_is_list_zip sj2l, hlval, hrvall]; rfl
            · apply lengthify at hlval; simp at hlval
              apply lengthify at hrvall; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrvall
              rw [List.append_nil, <- List.zip_eq_zipWith, List.map_fst_zip]
              simp [hrvall] -- lia + assumption in context
            . apply lengthify at hlval; simp at hlval
              apply lengthify at hrvall; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrvall
              rewrite [<- List.zip_eq_zipWith, List.map_snd_zip]
              . simp only [List.append_assoc, List.take_append_drop]
              . simp only [List.length_append, List.length_map, List.length_take, add_le_add_iff_left, inf_le_left]
            · rewrite [List.append_assoc]; rfl
            · grind [pf, lhsModule]
          . apply lengthify at hlval; simp at hlval
            apply lengthify at hrval; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrval
            simp only [hlval, List.length_map, List.length_cons, List.length_append, List.length_take,
              add_left_inj, add_right_inj, left_eq_inf] -- lengthify the goal
            simp only [le_iff_exists_add, <- hrval, add_right_inj, exists_eq'] -- lia
        . simp at hrval; simp at *
          rw [<- List.take_append_drop (ij2r.length + ij1l.length) ij2l] at hlval
          rw [show v.1.1 ::
              (List.map (Prod.fst ∘ Prod.fst) ip' ++
                (List.take (ij2r.length + ij1l.length) ij2l ++
                  List.drop (ij2r.length + ij1l.length) ij2l)) = v.1.1 ::
              (List.map (Prod.fst ∘ Prod.fst) ip' ++
                List.take (ij2r.length + ij1l.length) ij2l) ++
                  List.drop (ij2r.length + ij1l.length) ij2l by simp] at hlval
          rw [append_iff] at hlval
          obtain ⟨hlvall, hlvalr⟩ := hlval
          . subst_vars
            apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
            . and_intros <;> dsimp
              . rewrite [product_is_list_zip sj2l, hrval, hlvall]; rfl
              . apply lengthify at hrval; simp at hrval
                apply lengthify at hlvall; simp [hrval, add_comm _ 1, add_right_inj, add_assoc] at hlvall
                simp [<- List.zip_eq_zipWith, List.map_fst_zip, hlvall]
              . apply lengthify at hrval; simp at hrval
                apply lengthify at hlvall; simp [hrval, add_comm _ 1, add_right_inj, add_assoc] at hlvall
                rewrite [<- List.zip_eq_zipWith, List.map_snd_zip]
                . simp
                . simp [hlvall]
              . simp
              . grind [pf, lhsModule]
          . apply lengthify at hrval; simp [add_comm _ 1, add_right_inj, add_assoc] at hrval
            apply lengthify at hlval; simp [hrval, add_comm _ 1, add_left_inj, add_assoc] at hlval
            simp only [hrval, List.length_map, List.length_cons, add_comm _ 1, add_right_inj, List.length_append, List.length_take, left_eq_inf] -- lengthify the goal
            simp only [le_iff_exists_add, <- hlval, add_right_inj, exists_eq', add_assoc] -- lia
    . exfalso; exact (PortMap.getIO_not_contained_false hrule HContains)
  -- internal rules
  . intros rule mid_i _ _
    use init_s
    apply And.intro
    . exact existSR_reflexive
    . unfold φ at *
      obtain ⟨_, _⟩ := Hφ
      apply And.intro
      . apply ψ_holds_over_internals_impl init_i
        . assumption
        . apply existSR_single_step <;> assumption
      . assumption

theorem refines: rhsModule T₁ T₂ T₃ ⊑ lhsModule T₁ T₂ T₃ :=
by
  unfold Module.refines
  use (by infer_instance), φ <;> and_intros
  . exact refines₀_φ
  . unfold Module.refines_initial
    intro i hᵢ
    use ⟨⟨[], []⟩, ⟨[], []⟩⟩
    apply And.intro
    . trivial
    . dsimp [rhsModule] at hᵢ
      unfold φ
      apply And.intro
      . unfold ψ <;> grind [ψ]
      . grind [pf, lhsModule]

/--
info: 'Graphiti.JoinRewrite.refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refines

end DirectRefinement

section UnflushedRefinement

private inductive empty_internal: lhsModuleType T₁ T₂ T₃ -> Prop where
| mk: ∀ q₁ q₂ q₃, empty_internal ⟨⟨[], q₃⟩, ⟨q₁, q₂⟩⟩

private inductive single_internal: lhsModuleType T₁ T₂ T₃ -> Prop where
| mk: ∀ v q₁ q₂ q₃, single_internal ⟨⟨[v], q₃⟩, ⟨q₁, q₂⟩⟩

private theorem f': ∀ s₁ s₂, ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals,
  empty_internal s₁ → rule s₁ s₂ → single_internal s₂ :=
by
  intro ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ rule h₁ h₂ h₃
  simp [lhsModule] at h₁
  subst h₁

  cases h₂
  dsimp at h₃
  simp at h₃
  obtain ⟨_, _, _, _, _, _, _⟩ := h₃
  repeat
    cases ‹_ ∧ _›
  subst_vars
  constructor

private theorem f₃: ∀ ident s₁ s₂ v,
  single_internal s₁
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → empty_internal s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ _ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . -- fetch the single output port ident
    simp [lhsModule] at HContains; subst HContains
    unfold lhsModule at h₂
    rw [PortMap.rw_rule_execution] at h₂
    dsimp at h₂
    simp at h₂
    repeat
      cases ‹_ ∧ _›
    subst_vars
    cases h₁
    constructor
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

private def φ₃ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) :=
  ψ rhs lhs ∧ empty_internal lhs

private theorem f₁: ∀ ident i₁ i₂ v s₁, ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals,
  φ₃ i₁ s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ v i₂
  → ∃ s₂, rule s₁ s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ v ⟨⟨_, _⟩,⟨_, _⟩⟩ rule h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . -- Fetch the output rule
    simp [rhsModule] at HContains; subst HContains
    obtain ⟨hψ, h₂⟩ := h₂
    cases h₂
    dsimp [ψ] at hψ
    obtain ⟨_, _, _⟩ := hψ
    subst_vars
    -- work on h₃
    unfold rhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    simp at h₃
    repeat
      cases ‹_ ∧ _›
    subst_vars
    -- work on h₁
    simp [lhsModule] at h₁; subst h₁
    dsimp
    apply Exists.intro ⟨⟨_, _⟩,⟨_, _⟩⟩
    repeat
      apply Exists.intro
    simp
    and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

private theorem f'': ∀ ident i₁ i₂ v s₁,
  ψ i₁ s₁
  → single_internal s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ ↑v i₂
  → ∃ s₂, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ (coe_out.mp v) s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ _ ⟨⟨_, _⟩,⟨_, _⟩⟩ h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [rhsModule] at HContains; subst HContains
    unfold rhsModule at h₃; rw [PortMap.rw_rule_execution] at h₃; simp at h₃
    cases h₂
    dsimp [ψ] at h₁
    repeat
      cases ‹_ ∧ _›
    subst_vars
    unfold lhsModule
    apply Exists.intro ⟨⟨_, _⟩,⟨_, _⟩⟩
    rw [PortMap.rw_rule_execution]; dsimp
    and_intros
    . simp at *
      iterate 2 cases ‹_ ∧ _›
      and_intros
      . apply Prod.ext <;> assumption
      . rfl
    . rfl
    . rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

private theorem refines₃: rhsModule T₁ T₂ T₃ ⊑_{φ₃} lhsModule T₁ T₂ T₃ := by
  unfold Module.refines_φ
  intro init_i init_s Hψ
  apply Module.comp_refines.mk
  -- input rules
  . intro ident i s a
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := init_i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i

      unfold rhsModule at HContains; simp at HContains
      rcases HContains with h | h | h <;> subst_vars <;> simp
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst = _ := by dsimp [reducePortMapgetIO]
        -- We construct the almost_mid_s manually
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l ++ [heq.mp s], sj1r⟩⟩
        apply And.intro
        . -- verify that the rule holds
          rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
          simp -- TODO: Remove this simp here
        . -- verify that the invariant holds when we flush the system
          use ⟨⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [φ₃, ψ] at Hψ
            obtain ⟨⟨h, _, _⟩, hₑ⟩ := Hψ
            dsimp [φ₃, ψ]
            and_intros
            . rw [<- List.append_assoc, <- List.append_assoc, h]
            . assumption
            . assumption
            . cases hₑ; constructor
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).fst = _ := by dsimp [reducePortMapgetIO]
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r ++ [heq.mp s]⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . use ⟨⟨sj2l, sj2r⟩, sj1l, sj1r ++ [heq.mp s]⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [φ₃, ψ] at Hψ
            obtain ⟨⟨_, h, _⟩, hₑ⟩ := Hψ
            subst_vars
            dsimp [φ₃, ψ]
            and_intros
            . assumption
            . rw [<- List.append_assoc, <- List.append_assoc, h]
            . rfl
            . cases hₑ; constructor
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).fst = _ := by dsimp [reducePortMapgetIO]
        use ⟨⟨sj2l, sj2r ++ [heq.mp s]⟩, ⟨sj1l, sj1r⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . use ⟨⟨sj2l, sj2r ++ [heq.mp s]⟩, sj1l, sj1r⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [φ₃, ψ] at Hψ
            obtain ⟨⟨_, _, _⟩, hₑ⟩ := Hψ
            subst_vars
            dsimp [φ₃, ψ]
            and_intros
            . assumption
            . assumption
            . rw [<- List.append_assoc]
            . cases hₑ; constructor
    . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
  -- output rules
  . intro ident i v hrule
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . obtain ⟨rule, h⟩: ∃ rule, rule ∈ (lhsModule T₁ T₂ T₃).internals := by simp [lhsModule]
      obtain ⟨almost_mid_s, _⟩ : ∃ almost_mid_s, rule init_s almost_mid_s := by
        apply (f₁ _ init_i i) at Hψ
        . specialize Hψ hrule
          assumption
        . assumption
      use almost_mid_s
      rw [exists_and_left]
      and_intros
      . apply existSR_single_step <;> assumption
      . unfold φ₃ at Hψ
        obtain ⟨_, _⟩ := Hψ
        have hₛ: single_internal almost_mid_s := by
          apply f' <;> assumption
        have: existSR (lhsModule T₁ T₂ T₃).internals init_s almost_mid_s := by
          apply existSR_single_step <;> assumption
        have hψ: ψ init_i almost_mid_s := by
          apply ψ_holds_over_internals_spec <;> assumption
        clear this
        have: ∃ mid_s, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd almost_mid_s (coe_out.mp v) mid_s := by
          apply f'' <;> assumption
        obtain ⟨mid_s, _⟩ := this
        use mid_s
        apply And.intro
        . assumption
        . unfold φ₃
          apply And.intro
          . apply outputs_preserves_ψ <;> assumption
          . apply f₃ <;> assumption
    . exfalso; exact (PortMap.getIO_not_contained_false hrule HContains)
  -- internal rules
  . intros
    use init_s
    apply And.intro
    . exact existSR_reflexive
    . obtain ⟨_, _⟩ := Hψ
      . apply And.intro
        . apply ψ_holds_over_internals_impl init_i
          . assumption
          . apply existSR_single_step <;> assumption
        . assumption

theorem refines'': rhsModule T₁ T₂ T₃ ⊑ lhsModule T₁ T₂ T₃ := by
  unfold Module.refines
  use (by infer_instance), φ₃ <;> and_intros
  . exact refines₃
  . unfold Module.refines_initial
    intro i hᵢ
    use ⟨⟨[], []⟩, [], []⟩ <;> apply And.intro
    . simp [lhsModule]
    . dsimp
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := hᵢ
      apply And.intro
      . simp [ψ]
      . constructor

/--
info: 'Graphiti.JoinRewrite.refines''' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refines''

end UnflushedRefinement

-- TODO: CLEAN THINGS UP BY DELETING THIS??
section RefinementBetweenFlushed

private def φ₄ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  ψ rhs lhs ∧ pf (lhsModule T₁ T₂ T₃) lhs

private inductive at_least_single_internal: lhsModuleType T₁ T₂ T₃ -> Prop where
| mk: ∀ v q₁ q₂ q₃ q₄, at_least_single_internal ⟨⟨v :: q₃, q₄⟩, ⟨q₁, q₂⟩⟩

private theorem f₆: ∀ ident i₁ i₂ v s₁,
  ψ i₁ s₁
  → pf ((lhsModule T₁ T₂ T₃)) s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ v i₂
  → at_least_single_internal s₁ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂ h₃
  by_cases HContains: (rhsModule T₁ T₂ T₃).outputs.contains ident
  .
    simp [rhsModule] at HContains <;> subst HContains
    --
    unfold rhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    simp at h₃
    obtain ⟨⟨_, _, _⟩, _, _⟩ := h₃
    obtain ⟨_, _, _⟩ := h₁
    subst_vars
    --
    rewrite [pf_iff_partially_flushed] at h₂
    cases h₂
    . rename_i h₁ h₂
      simp at h₁ h₂
      simp
      sorry -- TODO: Reasoning about the length again?
    . rename_i h₁ h₂
      simp at h₁ h₂
      sorry -- TODO: Reasoning about the length again?
  . exfalso; exact (PortMap.getIO_not_contained_false h₃ HContains)

-- move to have a reasoning about atleast one in internal
-- we case only on once over queues that are in the top queue
private theorem f₅: ∀ ident i₁ i₂ v s₁,
  ψ i₁ s₁ -- TODO: Remove this assumption
  → at_least_single_internal s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ ↑v i₂ -- TODO: Remove this assumption
  → ∃ s₂, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ (coe_out.mp v) s₂ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v s₁ h₁ h₂ h₃
  by_cases HContains: (rhsModule T₁ T₂ T₃).outputs.contains ident
  . simp [rhsModule] at HContains <;> subst HContains
    --
    unfold rhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    simp at h₃
    obtain ⟨⟨_, _, _⟩, _, _⟩ := h₃
    subst_vars
    --
    cases h₂
    obtain ⟨_, _, _⟩ := h₁
    apply Exists.intro ⟨⟨_, _⟩, ⟨_, _⟩⟩
    unfold lhsModule
    rw [PortMap.rw_rule_execution]
    simp
    and_intros
    . rw [List.map_cons, List.map_cons] at *
      simp at *
      iterate 2
        cases ‹_ ∧ _›
      apply Prod.ext <;> assumption
    . rfl
    . rwa [List.map_cons] at *
    . rfl
    . rfl
  . exfalso; exact (PortMap.getIO_not_contained_false h₃ HContains)

-- TODO: This is basically wellformess of a module?
--       I don't really need wellformness, I need to be able to close the gap
--       Basically, confluence between inputs and internals
--       How do I formulate it in all the confluence contexts
-- TODO: Get rid of this theorem
private theorem lhs_can_always_input: ∀ ident s₁ v,
  (lhsModule T₁ T₂ T₃).inputs.contains ident → ∃ s₂, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂ :=
by
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ h
  simp [lhsModule] at h
  rcases h with h | h | h <;> subst h
  all_goals
    apply Exists.intro ⟨⟨_ , _⟩, ⟨_ , _⟩⟩
    dsimp [lhsModule]
    rw [PortMap.rw_rule_execution]
    simp <;> and_intros <;> rfl

-- NOTE: To generalize this statement, the underlying module must:
--            - be able to input an element (can we call this the wellformness of a module?)
--            - be able to eventually reach a flushed state
-- Generalize it to if a module can input and it is flushable, then the flushable can input
-- Converse don't need flushability
private theorem flhs_can_always_input [flhs: Flushable (lhsModule T₁ T₂ T₃)]:
  ∀ ident s₁ v,
  (lhsModule T₁ T₂ T₃).inputs.contains ident
  → ∃ s₂, ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd s₁ v s₂ :=
by
  intro ident s₁ v h
  obtain ⟨s₃, _⟩ := lhs_can_always_input ident s₁ (coe_in.mp v) h
  obtain ⟨s₄, _⟩ := flhs.flushable s₃
  use s₄
  rewrite [flushed_inputs_are_rflushed]
  dsimp [rflushed]
  use s₃ <;> and_intros <;> assumption

private theorem refines₄:
  flushed (rhsModule T₁ T₂ T₃) ⊑_{φ₄} flushed (lhsModule T₁ T₂ T₃) :=
by
  have sr: SimulationRelation ψ (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by infer_instance
  have opfm: OutputPreservesFlushability (lhsModule T₁ T₂ T₃) := by infer_instance
  unfold Module.refines_φ
  intro init_i init_s Hψ
  apply Module.comp_refines.mk
  . -- inputs rules
    intro ident mid_i v h₁
    -- TODO: This is basically the inputability property here
    obtain ⟨s', h₂⟩ : ∃ s', ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd init_s (coe_in.mp v) s' := by
      apply flhs_can_always_input
      apply PortMap.rule_contains at h₁
      rw [flushed_preserves_ports] at h₁
      rwa [@match_interface_inputs_contains _ _ _ _ (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃)] at h₁
    use s', s'
    apply And.intro
    . assumption
    . apply And.intro
      . apply existSR_reflexive
      . unfold φ₄; apply And.intro
        . rw [flushed_inputs_are_rflushed] at h₁
          rw [flushed_inputs_are_rflushed] at h₂
          obtain ⟨s₁, _, h₁⟩ := h₁
          obtain ⟨s₂, _, h₂⟩ := h₂
          obtain ⟨_, _⟩ := Hψ -- TODO: This can be removed if we go down to ψ instead of φ₄
          apply flushesTo_implies_reachable at h₁
          apply flushesTo_implies_reachable at h₂
          simp at *
          have: ψ s₁ s₂ := by
            apply sr.inputs_preserved _ init_i _ _ init_s _ <;> simpa
          apply sr.internals_preserved <;> simpa
        . apply flushed_modules_has_flushed_states <;> assumption
  . -- outputs rules
    intro ident mid_i v h₁
    use init_s
    rw [exists_and_left]
    apply And.intro
    . apply existSR_reflexive
    . obtain ⟨_, _⟩ := Hψ
      obtain ⟨s', _⟩: ∃ s', ((flushed (lhsModule T₁ T₂ T₃)).outputs.getIO ident).snd init_s (coe_out.mp v) s' := by
        have: at_least_single_internal init_s := by
          apply f₆ <;> assumption
        dsimp [flushed] at *
        apply f₅ <;> assumption
      use s'
      apply And.intro
      . assumption
      . dsimp [flushed] at *
        unfold φ₄; apply And.intro
        . apply sr.outputs_preserved <;> assumption
        . apply opfm.rule <;> assumption
  . --internal rules
    intros _ mid_i h₁ _
    dsimp [flushed] at *
    use init_s
    apply And.intro
    . apply existSR_reflexive
    . obtain ⟨_, _⟩ := Hψ
      apply And.intro
      . contradiction
      . assumption

--#print axioms refines₄

end RefinementBetweenFlushed

------------------------

/-section Wellformness

-- TODO: Will we be able, at some point, to get rid of this completely ??
instance: InhabitedPorts (rhsModule T₁ T₂ T₃) := by
  constructor
  . intro ident
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . simp [rhsModule] at HContains <;> rcases HContains with h | h | h
      . subst h <;> simp [rhsModule] <;> infer_instance
      -- TODO: WHY DOESN'T infer_instance work here?
      . subst h <;> simp [rhsModule] <;> assumption
      . subst h <;> simp [rhsModule] <;> assumption
    . apply Bool.eq_false_of_not_eq_true at HContains
      rewrite [<- Batteries.AssocList.contains_find?_none_iff] at HContains
      apply PortMap.getIO_none at HContains
      rewrite [HContains] <;> dsimp
      exact ⟨PUnit.unit⟩
  . intro ident
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . simp [rhsModule] at HContains <;> subst HContains
      simp [rhsModule] <;> and_intros <;> infer_instance
    . apply Bool.eq_false_of_not_eq_true at HContains
      rewrite [<- Batteries.AssocList.contains_find?_none_iff] at HContains
      apply PortMap.getIO_none at HContains
      rewrite [HContains] <;> dsimp
      exact ⟨PUnit.unit⟩

end Wellformness-/

section InductiveRefinement

set_option quotPrecheck false -- TODO: Can I do without?
infix:60 " ≺ " => (indistinguishable (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃))

set_option quotPrecheck false -- TODO: Can I do without?
infix:60 " ≺≺ " => (indistinguishable (rhsModule T₁ T₂ T₃) (flushed (lhsModule T₁ T₂ T₃)))

private inductive φ₀: (rhsModuleType T₁ T₂ T₃) → (lhsModuleType T₁ T₂ T₃) → Prop :=
| mk q₁ q₂: q₁.length = q₂.length → φ₀ ⟨⟨[], []⟩, ⟨[], []⟩, q₁.zip q₂⟩ ⟨⟨q₁, q₂⟩, ⟨[], []⟩⟩

private instance φ₀.ind: Indistinguishable (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) φ₀ := by
  constructor
  intros i₁ s₁ φₕ
  constructor
  . intros ident i₂ v h
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . obtain ⟨q₁, q₂⟩ := φₕ
      simp [rhsModule] at HContains <;> rcases HContains with hᵢ | hᵢ | hᵢ <;> subst hᵢ <;> simp
      . use ⟨⟨q₁, q₂⟩, ⟨[v], []⟩⟩
        dsimp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> trivial
      . use ⟨⟨q₁, q₂⟩, ⟨[], [v]⟩⟩
        dsimp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> trivial
      . reduce at v -- TODO: GET RID OF THIS REDUCE
        use ⟨⟨q₁, q₂ ++ [v]⟩, ⟨[], []⟩⟩
        dsimp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> trivial
    . exfalso; exact (PortMap.getIO_not_contained_false h HContains)
  . intros ident i₂ v h
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . simp [rhsModule] at HContains <;> subst HContains <;> simp
      obtain ⟨q₁, q₂⟩ := φₕ
      cases q₁ with
      | nil =>
        dsimp [rhsModule] at h
        rewrite [PortMap.rw_rule_execution] at h
        grind
      | cons hd₁ tl₁ => cases q₂ with
        | nil =>
          dsimp [rhsModule] at h
          rewrite [PortMap.rw_rule_execution] at h
          simp at h
        | cons hd₂ tl₂ =>
          use ((tl₁, tl₂), [], [])
          dsimp [lhsModule]
          rewrite [PortMap.rw_rule_execution]
          simp
          dsimp [rhsModule] at h
          rewrite [PortMap.rw_rule_execution] at h
          simp at h
          grind
    . exfalso; exact (PortMap.getIO_not_contained_false h HContains)

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.φ₀.ind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms φ₀.ind

---------------------------------------------------------------------------------------------------
-----
---------------------------------------------------------------------------------------------------

-- TODO: MOVE IT CLOSE TO DEFINITION OF IND
-- ofc, need spec to be flushable
private lemma ind_imp_find {s s'} : s ≺ s' → s ≺≺ s' :=
by
  intro h
  have fl: Flushable (lhsModule T₁ T₂ T₃) := by infer_instance
  constructor
  . intro ident new_i v hᵢ
    apply h.inputs_indistinguishable at hᵢ
    obtain ⟨new_s, hₛ⟩ := hᵢ
    have ⟨fnew_s, hf⟩ := fl.flushable new_s
    use fnew_s
    rewrite [flushed_inputs_are_rflushed]
    dsimp [rflushed]
    use new_s <;> apply And.intro
    . simpa
    . assumption
  . intro ident new_i v hᵢ
    exact h.outputs_indistinguishable _ _ _ hᵢ

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.ind_imp_find' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms ind_imp_find

private lemma ind₀ (q₁ q₂ q₃ q₄) {p₁ p₂ p₃ p₄ p₅ p₆}: ((p₁, p₂), (p₃, p₄), q₁.zip q₂) ≺ ((q₁ ++ q₃, q₂ ++ q₄), p₅, p₆) := by
  constructor
  . intros ident new_i v hᵢ
    apply PortMap.rule_contains at hᵢ
    apply lhs_can_always_input <;> try assumption
    --have mm: MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by infer_instance
    -- NOTE: Could have been nice to write mm.inputs_contains
    rewrite [@match_interface_inputs_contains _ _ _ _ _ (lhsModule T₁ T₂ T₃)] at hᵢ
    assumption
  . intros ident new_i v hᵢ
    by_cases HContains: (rhsModule T₁ T₂ T₃).outputs.contains ident
    . simp [rhsModule] at HContains <;> subst HContains
      cases q₁ with
      | nil =>
        dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
        grind
      | cons hd₁ tl₁ => cases q₂ with
        | nil =>
          rewrite [List.zip_nil_right] at hᵢ
          dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
          grind
        | cons hd₂ tl₂ =>
          use ((tl₁ ++ q₃, tl₂ ++ q₄), p₅, p₆)
          dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
          dsimp [lhsModule] <;> rewrite [PortMap.rw_rule_execution]
          grind
    . exfalso; exact (PortMap.getIO_not_contained_false hᵢ HContains)

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.ind₀' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ind₀

private lemma ind₁ {v₀ q₁ q₂}: (([v₀], []), ([], []), q₁.zip q₂) ≺ ((q₁, q₂), [v₀], []) := by
  have this := @ind₀ _ _ _ q₁ q₂ [] [] [v₀] [] [] [] [v₀] []
  simp at this
  exact this

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.ind₁' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ind₁

private lemma ind₂ {v₁ q₁ q₂}: (([], []), ([v₁], []), q₁.zip q₂) ≺ ((q₁, q₂), [], [v₁]) := by
  have this := @ind₀ _ _ _ q₁ q₂ [] [] [] [] [v₁] [] [] [v₁]
  simp at this
  exact this

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.ind₂' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ind₂

private lemma ind₃ {v₂ q₁ q₂}: (([], []), ([], [v₂]), q₁.zip q₂) ≺ ((q₁, q₂ ++ [v₂]), [], []) := by
  have this := @ind₀ _ _ _ q₁ q₂ [] [v₂] [] [] [] [v₂] [] []
  simp at this
  exact this

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.ind₃' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ind₃

private lemma ind₄ {v₀ v₁ q₁ q₂}: (([v₀], []), ([v₁], []), q₁.zip q₂) ≺ ((q₁ ++ [(v₀, v₁)], q₂), [], []) := by
  have this := @ind₀ _ _ _ q₁ q₂ [⟨v₀, v₁⟩] [] [v₀] [] [v₁] [] [] []
  simp at this
  exact this

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.ind₄' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ind₄

private lemma ind₅ {v₀ v₂ q₁ q₂}: (([v₀], []), ([], [v₂]), q₁.zip q₂) ≺ ((q₁, q₂ ++ [v₂]), [v₀], []) := by
  have this := @ind₀ _ _ _ q₁ q₂ [] [v₂] [v₀] [] [] [v₂] [v₀] []
  simp at this
  exact this

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.ind₅' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ind₅

-- TODO: PROVE IND NON-FLUSHED SPEC
private lemma ind₆ {v₀ v₁ v₂ q₁ q₂}: (([v₀], []), ([v₁], [v₂]), q₁.zip q₂) ≺ ((q₁ ++ [(v₀, v₁)], q₂ ++ [v₂]), [], []) := by
  have this := @ind₀ _ _ _ q₁ q₂ [⟨v₀, v₁⟩] [v₂] [v₀] [] [v₁] [v₂] [] []
  simp at this
  exact this

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.ind₆' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ind₆

private lemma boo {q₁ q₂}: ∀ v₀ v₁ v₂, q₁.length = q₂.length →
  @φᵢ _ _ _ _ (rhsModule T₁ T₂ T₃) (flushed (lhsModule T₁ T₂ T₃)) _ φ₀ (([v₀], []), ([v₁], [v₂]), q₁.zip q₂) ((q₁ ++ [(v₀, v₁)], q₂ ++ [v₂]), [], []) :=
by
  intro v₀ v₁ v₂ h
  have: existSR (rhsModule T₁ T₂ T₃).internals ⟨⟨[v₀], []⟩, ⟨[v₁], [v₂]⟩, q₁.zip q₂⟩ ⟨⟨[], []⟩, ⟨[], []⟩, (q₁ ++ [(v₀, v₁)]).zip (q₂ ++ [v₂])⟩ := by
    -- TODO: CAN WE HAVE A TACTIC THAT SOLVES THIS KIND OF GOALS AUTOMATICALLY?
    have: existSR (rhsModule T₁ T₂ T₃).internals ⟨⟨[v₀], []⟩, ⟨[v₁], [v₂]⟩, q₁.zip q₂⟩ ⟨⟨[v₀], [⟨v₁, v₂⟩]⟩, ⟨[], []⟩, q₁.zip q₂⟩ := by
      let rule := (rhsModule T₁ T₂ T₃).internals.get ⟨0, by dsimp [rhsModule]; trivial⟩
      apply existSR_single_step'
      use rule <;> apply And.intro
      . apply List.get_mem
      . simp [rule, rhsModule]
    have: existSR (rhsModule T₁ T₂ T₃).internals ⟨⟨[v₀], [⟨v₁, v₂⟩]⟩, ⟨[], []⟩, q₁.zip q₂⟩ ⟨⟨[], []⟩, ⟨[], []⟩, (q₁ ++ [(v₀, v₁)]).zip (q₂ ++ [v₂])⟩ := by
      let rule := (rhsModule T₁ T₂ T₃).internals.get ⟨1, by dsimp [rhsModule]; trivial⟩
      apply existSR_single_step'
      use rule <;> apply And.intro
      . apply List.get_mem
      . simp [rule, rhsModule, List.zip_append h]
    apply existSR_transitive <;> assumption
  apply φᵢ.internal _ _ (ind_imp_find ind₆) _ this <;> clear this
  apply φᵢ.base
  constructor
  grind

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.boo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms boo

private lemma input₀_preserves_φᵢ: ∀ i s v₀ mid_i mid_s,
  φ₀ i s →
  ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).snd i v₀ mid_i →
  ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO { inst := InstIdent.top, name := "i_0" }).snd s (coe_in.mp v₀) mid_s →
  @φᵢ _ _ _ _ (rhsModule T₁ T₂ T₃) (flushed (lhsModule T₁ T₂ T₃)) _ φ₀ mid_i mid_s
  :=
by
  intros i s v₀ mid_i mid_s φₕ hᵢ hₛ
  obtain ⟨q₁, q₂, hₗ⟩ := φₕ
  -- SOLVING AFTER `i_0`
  have: mid_i = (([v₀], []), ([], []), q₁.zip q₂) := by
    clear hₛ
    obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := mid_i
    dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
    simp at hᵢ <;> grind
  subst this <;> clear hᵢ
  have: mid_s = ((q₁, q₂), ([v₀], [])) := by
    rewrite [flushed_inputs_are_rflushed] at hₛ
    obtain ⟨s', hₛ, hₛ'⟩ := hₛ
    have: s' = ((q₁, q₂), ([v₀], [])) := by
      obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := s'
      dsimp [lhsModule] at hₛ <;> rewrite [PortMap.rw_rule_execution] at hₛ
      simp at hₛ <;> grind
    subst this <;> clear hₛ
    apply flushesTo_implies_reachable at hₛ'
    -- TODO: MOVE ALL THE pf states as we did with ind
    have: pf (lhsModule T₁ T₂ T₃) ((q₁, q₂), [v₀], []) :=
      by grind [pf, lhsModule]
    symm <;> apply pf_is_terminal <;> assumption
  subst this <;> clear hₛ
  -- SOLVING AFTER `i_1`
  have ⟨i, hᵢ⟩:  ∃ i: (((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).fst → rhsModuleType T₁ T₂ T₃), ∀ v₁, ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).snd (([v₀], []), ([], []), q₁.zip q₂) v₁ (i v₁) := by
    use (λ v₁ => ⟨⟨[v₀], []⟩, ⟨[v₁], []⟩, q₁.zip q₂⟩) <;> dsimp -- dsimp for β-reduction
    intro v₂
    dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> trivial
  have ⟨s, hₛ⟩:  ∃ s: (((lhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).fst → lhsModuleType T₁ T₂ T₃), ∀ v₁, ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO { inst := InstIdent.top, name := "i_1" }).snd ((q₁, q₂), [v₀], []) v₁ (s v₁) := by
    use (λ v₁ => ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂⟩, ⟨[], []⟩⟩) <;> dsimp -- dsimp for β-reduction
    intro v₁
    rewrite [flushed_inputs_are_rflushed] <;> dsimp [rflushed]
    use ⟨⟨q₁, q₂⟩, [v₀], [v₁]⟩ <;> apply And.intro
    . dsimp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
    . constructor <;> and_intros
      . let rule := (lhsModule T₁ T₂ T₃).internals.get ⟨0, by dsimp [lhsModule]; trivial⟩
        apply existSR_single_step'
        use rule <;> apply And.intro
        . simp [rule]
        . simp [rule, lhsModule]
      . grind [lhsModule, pf]
  apply φᵢ.input _ _ _ _ _ (ind_imp_find ind₁) _ hᵢ hₛ
  dsimp
  intro v₁ <;> specialize hᵢ v₁ <;> specialize hₛ v₁
  have: (i v₁) = ⟨⟨[v₀], []⟩, ⟨[v₁], []⟩, q₁.zip q₂⟩ := by
    clear hₛ s
    dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
    simp at hᵢ
    grind [Prod.mk.eta]
  rewrite [this] <;> clear this hᵢ i
  have: (s v₁) = ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂⟩, ⟨[], []⟩⟩ := by
    rewrite [flushed_inputs_are_rflushed] at hₛ
    obtain ⟨s', hₛ, hₛ'⟩ := hₛ
    have: s' = ((q₁, q₂), ([v₀], [v₁])) := by
      obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := s'
      dsimp [lhsModule] at hₛ <;> rewrite [PortMap.rw_rule_execution] at hₛ
      simp at hₛ <;> grind
    subst this <;> clear hₛ
    have: existSR (lhsModule T₁ T₂ T₃).internals ((q₁ ++ [⟨v₀, v₁⟩], q₂), ([], [])) (s v₁) := by
      reduce at v₀ v₁
      have: existSR (lhsModule T₁ T₂ T₃).internals ((q₁, q₂), [v₀], [v₁]) ((q₁ ++ [(v₀, v₁)], q₂), [], []) := by
        let rule := (lhsModule T₁ T₂ T₃).internals.get ⟨0, by dsimp [lhsModule]; trivial⟩
        apply existSR_single_step'
        use rule <;> apply And.intro
        . simp [rule]
        . simp [rule, lhsModule]
      apply newrule at this
      specialize this hₛ'
      apply flushesTo_implies_reachable
      assumption
    -- TODO: MOVE ALL THE pf states as we did with ind
    have: pf (lhsModule T₁ T₂ T₃) ((q₁ ++ [⟨v₀, v₁⟩], q₂), ([], [])) :=
      by grind [pf, lhsModule]
    symm <;> apply pf_is_terminal <;> assumption
  rewrite [this] <;> clear this hₛ s
  -- SOLVING AFTER `i_2`
  have ⟨i, hᵢ⟩: ∃ i: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).fst → rhsModuleType T₁ T₂ T₃, ∀ v₂, ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).snd (([v₀], []), ([v₁], []), q₁.zip q₂) v₂ (i v₂) := by
    use (λ v₂ => ⟨⟨[v₀], []⟩, ⟨[v₁], [v₂]⟩, q₁.zip q₂⟩) <;> dsimp -- dsimp for β-reduction
    intro v₂
    dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> trivial
  reduce at v₀ v₁ -- TODO: REMOVE THIS REDUCE HERE
  have ⟨s, hₛ⟩: ∃ s: ((lhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).fst → lhsModuleType T₁ T₂ T₃, ∀ v₂, ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO { inst := InstIdent.top, name := "i_2" }).snd ((q₁ ++ [(v₀, v₁)], q₂), [], []) v₂ (s v₂) := by
    use (λ v₂: T₃ => ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]⟩, ⟨[], []⟩⟩) <;> dsimp -- dsimp for β-reduction
    intro v₂
    rewrite [flushed_inputs_are_rflushed] <;> dsimp [rflushed]
    reduce at v₂
    use ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]⟩, [], []⟩ <;> apply And.intro
    . dsimp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
    . constructor <;> and_intros
      . exact existSR_reflexive
      . grind [lhsModule, pf]
  apply φᵢ.input _ _ _ _ _ (ind_imp_find ind₄) _ hᵢ hₛ
  dsimp
  intro v₂ <;> specialize hᵢ v₂ <;> specialize hₛ v₂
  have: (i v₂) = ⟨⟨[v₀], []⟩, ⟨[v₁], [v₂]⟩, q₁.zip q₂⟩ := by
    clear hₛ s
    dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
    simp at hᵢ
    grind [Prod.mk.eta]
  rewrite [this] <;> clear this hᵢ i
  reduce at v₂
  have: (s v₂) = ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]⟩, ⟨[], []⟩⟩ := by
    rewrite [flushed_inputs_are_rflushed] at hₛ
    obtain ⟨s', hₛ, hₛ'⟩ := hₛ
    have: s' = ((q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]), ([], [])) := by
      obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := s'
      dsimp [lhsModule] at hₛ <;> rewrite [PortMap.rw_rule_execution] at hₛ
      simp at hₛ <;> grind
    subst this <;> clear hₛ
    apply flushesTo_implies_reachable at hₛ'
    -- TODO: MOVE ALL THE pf states as we did with ind
    have: pf (lhsModule T₁ T₂ T₃) ((q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]), ([], [])) :=
      by grind [pf, lhsModule]
    symm <;> apply pf_is_terminal <;> assumption
  rewrite [this] <;> clear this hₛ s
  -- CONCLUDE
  exact boo v₀ v₁ v₂ hₗ

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.input₀_preserves_φᵢ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms input₀_preserves_φᵢ

private lemma input₁_preserves_φᵢ: ∀ i s v₁ mid_i mid_s,
  φ₀ i s →
  ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).snd i v₁ mid_i →
  ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO { inst := InstIdent.top, name := "i_1" }).snd s (coe_in.mp v₁) mid_s →
  @φᵢ _ _ _ _ (rhsModule T₁ T₂ T₃) (flushed (lhsModule T₁ T₂ T₃)) _ φ₀ mid_i mid_s
  :=
by
  intros i s v₁ mid_i mid_s φₕ hᵢ hₛ
  obtain ⟨q₁, q₂, hₗ⟩ := φₕ
  -- SOLVING AFTER `i_1`
  have: mid_i = (([], []), ([v₁], []), q₁.zip q₂) := by
    clear hₛ
    obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := mid_i
    dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
    simp at hᵢ <;> grind
  subst this <;> clear hᵢ
  have: mid_s = ((q₁, q₂), ([], [v₁])) := by
    rewrite [flushed_inputs_are_rflushed] at hₛ
    obtain ⟨s', hₛ, hₛ'⟩ := hₛ
    have: s' = ((q₁, q₂), ([], [v₁])) := by
      obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := s'
      dsimp [lhsModule] at hₛ <;> rewrite [PortMap.rw_rule_execution] at hₛ
      simp at hₛ <;> grind
    subst this <;> clear hₛ
    apply flushesTo_implies_reachable at hₛ'
    -- TODO: MOVE ALL THE pf states as we did with ind
    have: pf (lhsModule T₁ T₂ T₃) ((q₁, q₂), ([], [v₁])) :=
      by grind [pf, lhsModule]
    symm <;> apply pf_is_terminal <;> assumption
  subst this <;> clear hₛ
  -- SOLVING AFTER `i_0`
  have ⟨i, hᵢ⟩:  ∃ i: (((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst → rhsModuleType T₁ T₂ T₃), ∀ v₀, ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).snd (([], []), ([v₁], []), q₁.zip q₂) v₀ (i v₀) := by
    use (λ v₀ => ⟨⟨[v₀], []⟩, ⟨[v₁], []⟩, q₁.zip q₂⟩) <;> dsimp -- dsimp for beta-reduction
    intro v₂
    dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> trivial
  have ⟨s, hₛ⟩:  ∃ s: (((lhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst → lhsModuleType T₁ T₂ T₃), ∀ v₀, ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO { inst := InstIdent.top, name := "i_0" }).snd ((q₁, q₂), [], [v₁]) v₀ (s v₀) := by
    use (λ v₀ => ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂⟩, ⟨[], []⟩⟩) <;> dsimp -- dsimp for beta-reduction
    intro v₀
    rewrite [flushed_inputs_are_rflushed] <;> dsimp [rflushed]
    use ⟨⟨q₁, q₂⟩, [v₀], [v₁]⟩ <;> apply And.intro
    . dsimp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
    . constructor <;> and_intros
      . let rule := (lhsModule T₁ T₂ T₃).internals.get ⟨0, by dsimp [lhsModule]; trivial⟩
        apply existSR_single_step'
        use rule <;> apply And.intro
        . simp [rule]
        . simp [rule, lhsModule]
      . grind [lhsModule, pf]
  apply φᵢ.input _ _ _ _ _ (ind_imp_find ind₂) _ hᵢ hₛ
  dsimp
  intro v₀ <;> specialize hᵢ v₀ <;> specialize hₛ v₀
  have: (i v₀) = ⟨⟨[v₀], []⟩, ⟨[v₁], []⟩, q₁.zip q₂⟩ := by
    clear hₛ s
    dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
    simp at hᵢ
    grind [Prod.mk.eta]
  rewrite [this] <;> clear this hᵢ i
  have: (s v₀) = ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂⟩, ⟨[], []⟩⟩ := by
    rewrite [flushed_inputs_are_rflushed] at hₛ
    obtain ⟨s', hₛ, hₛ'⟩ := hₛ
    have: s' = ((q₁, q₂), ([v₀], [v₁])) := by
      obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := s'
      dsimp [lhsModule] at hₛ <;> rewrite [PortMap.rw_rule_execution] at hₛ
      simp at hₛ <;> grind
    subst this <;> clear hₛ
    have: existSR (lhsModule T₁ T₂ T₃).internals ((q₁ ++ [⟨v₀, v₁⟩], q₂), ([], [])) (s v₀) := by
      reduce at v₀ v₁
      have: existSR (lhsModule T₁ T₂ T₃).internals ((q₁, q₂), [v₀], [v₁]) ((q₁ ++ [(v₀, v₁)], q₂), [], []) := by
        let rule := (lhsModule T₁ T₂ T₃).internals.get ⟨0, by dsimp [lhsModule]; trivial⟩
        apply existSR_single_step'
        use rule <;> apply And.intro
        . simp [rule]
        . simp [rule, lhsModule]
      apply newrule at this
      specialize this hₛ'
      apply flushesTo_implies_reachable
      assumption
    -- TODO: MOVE ALL THE pf states as we did with ind
    have: pf (lhsModule T₁ T₂ T₃) ((q₁ ++ [⟨v₀, v₁⟩], q₂), ([], [])) :=
      by grind [pf, lhsModule]
    symm <;> apply pf_is_terminal <;> assumption
  rewrite [this] <;> clear this hₛ s
  -- SOLVING AFTER `i_2`
  have ⟨i, hᵢ⟩: ∃ i: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).fst → rhsModuleType T₁ T₂ T₃, ∀ v', ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).snd (([v₀], []), ([v₁], []), q₁.zip q₂) v' (i v') := by
    use (λ v₂ => ⟨⟨[v₀], []⟩, ⟨[v₁], [v₂]⟩, q₁.zip q₂⟩) <;> dsimp -- dsimp for beta-reduction
    intro v₂
    dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> trivial
  reduce at v₀ v₁
  have ⟨s, hₛ⟩: ∃ s: ((lhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).fst → lhsModuleType T₁ T₂ T₃, ∀ v', ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO { inst := InstIdent.top, name := "i_2" }).snd ((q₁ ++ [(v₀, v₁)], q₂), [], []) v' (s v') := by
    use (λ v₂: T₃ => ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]⟩, ⟨[], []⟩⟩) <;> dsimp -- dsimp for β-reduction
    intro v₂
    rewrite [flushed_inputs_are_rflushed] <;> dsimp [rflushed]
    reduce at v₂
    use ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]⟩, [], []⟩ <;> apply And.intro
    . dsimp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
    . constructor <;> and_intros
      . exact existSR_reflexive
      . grind [lhsModule, pf]
  apply φᵢ.input _ _ _ _ _ (ind_imp_find ind₄) _ hᵢ hₛ
  dsimp
  intro v₂ <;> specialize hᵢ v₂ <;> specialize hₛ v₂
  have: (i v₂) = ⟨⟨[v₀], []⟩, ⟨[v₁], [v₂]⟩, q₁.zip q₂⟩ := by
    clear hₛ s
    dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
    simp at hᵢ
    grind [Prod.mk.eta]
  rewrite [this] <;> clear this hᵢ i
  reduce at v₂
  have: (s v₂) = ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]⟩, ⟨[], []⟩⟩ := by
    rewrite [flushed_inputs_are_rflushed] at hₛ
    obtain ⟨s', hₛ, hₛ'⟩ := hₛ
    have: s' = ((q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]), ([], [])) := by
      obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := s'
      dsimp [lhsModule] at hₛ <;> rewrite [PortMap.rw_rule_execution] at hₛ
      simp at hₛ <;> grind
    subst this <;> clear hₛ
    apply flushesTo_implies_reachable at hₛ'
    -- TODO: MOVE ALL THE pf states as we did with ind
    have: pf (lhsModule T₁ T₂ T₃) ((q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]), ([], [])) :=
      by grind [pf, lhsModule]
    symm <;> apply pf_is_terminal <;> assumption
  rewrite [this] <;> clear this hₛ s
  -- CONCLUDE
  exact boo v₀ v₁ v₂ hₗ

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.input₁_preserves_φᵢ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms input₁_preserves_φᵢ

private lemma input₂_preserves_φᵢ: ∀ i s v₂ mid_i mid_s,
  φ₀ i s →
  ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).snd i v₂ mid_i →
  ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO { inst := InstIdent.top, name := "i_2" }).snd s (coe_in.mp v₂) mid_s →
  @φᵢ _ _ _ _ (rhsModule T₁ T₂ T₃) (flushed (lhsModule T₁ T₂ T₃)) _ φ₀ mid_i mid_s
  :=
by
  intros i s v₂ mid_i mid_s φₕ hᵢ hₛ
  obtain ⟨q₁, q₂, hₗ⟩ := φₕ
  -- SOLVING AFTER `i_2`
  have: mid_i = (([], []), ([], [v₂]), q₁.zip q₂) := by
    clear hₛ
    obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := mid_i
    dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
    simp at hᵢ <;> grind
  subst this <;> clear hᵢ
  reduce at v₂
  have: mid_s = ((q₁, q₂ ++ [v₂]), ([], [])) := by
    rewrite [flushed_inputs_are_rflushed] at hₛ
    obtain ⟨s', hₛ, hₛ'⟩ := hₛ
    have: s' = ((q₁, q₂ ++ [v₂]), ([], [])) := by
      obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := s'
      dsimp [lhsModule] at hₛ <;> rewrite [PortMap.rw_rule_execution] at hₛ
      simp at hₛ <;> grind
    subst this <;> clear hₛ
    apply flushesTo_implies_reachable at hₛ'
    -- TODO: MOVE ALL THE pf states as we did with ind
    have: pf (lhsModule T₁ T₂ T₃) ((q₁, q₂ ++ [v₂]), ([], [])) :=
      by grind [pf, lhsModule]
    symm <;> apply pf_is_terminal <;> assumption
  subst this <;> clear hₛ
  -- SOLVING AFTER `i_0`
  have ⟨i, hᵢ⟩:  ∃ i: (((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst → rhsModuleType T₁ T₂ T₃), ∀ v₀, ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).snd (([], []), ([], [v₂]), q₁.zip q₂) v₀ (i v₀) := by
    use (λ v₀ => ⟨⟨[v₀], []⟩, ⟨[], [v₂]⟩, q₁.zip q₂⟩) <;> dsimp -- dsimp for beta-reduction
    intro v₂
    dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> trivial
  have ⟨s, hₛ⟩:  ∃ s: (((lhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst → lhsModuleType T₁ T₂ T₃), ∀ v₀, ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO { inst := InstIdent.top, name := "i_0" }).snd ((q₁, q₂ ++ [v₂]), [], []) v₀ (s v₀) := by
    use (λ v₀ => ⟨⟨q₁, q₂ ++ [v₂]⟩, ⟨[v₀], []⟩⟩) <;> dsimp -- dsimp for beta-reduction
    intro v₀
    rewrite [flushed_inputs_are_rflushed] <;> dsimp [rflushed]
    use ⟨⟨q₁, q₂ ++ [v₂]⟩, [v₀], []⟩ <;> apply And.intro
    . dsimp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
    . constructor <;> and_intros
      . exact existSR_reflexive
      . grind [lhsModule, pf]
  apply φᵢ.input _ _ _ _ _ (ind_imp_find ind₃) _ hᵢ hₛ
  dsimp
  intro v₀ <;> specialize hᵢ v₀ <;> specialize hₛ v₀
  have: (i v₀) = ⟨⟨[v₀], []⟩, ⟨[], [v₂]⟩, q₁.zip q₂⟩ := by
    clear hₛ s
    dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
    simp at hᵢ
    grind [Prod.mk.eta]
  rewrite [this] <;> clear this hᵢ i
  have: (s v₀) = ⟨⟨q₁, q₂ ++ [v₂]⟩, [v₀], []⟩ := by
    rewrite [flushed_inputs_are_rflushed] at hₛ
    obtain ⟨s', hₛ, hₛ'⟩ := hₛ
    have: s' = ⟨⟨q₁, q₂ ++ [v₂]⟩, [v₀], []⟩ := by
      obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := s'
      dsimp [lhsModule] at hₛ <;> rewrite [PortMap.rw_rule_execution] at hₛ
      simp at hₛ <;> grind
    subst this <;> clear hₛ
    apply flushesTo_implies_reachable at hₛ'
    -- TODO: MOVE ALL THE pf states as we did with ind
    have: pf (lhsModule T₁ T₂ T₃) ⟨⟨q₁, q₂ ++ [v₂]⟩, [v₀], []⟩ :=
      by grind [pf, lhsModule]
    symm <;> apply pf_is_terminal <;> assumption
  rewrite [this] <;> clear this hₛ s
  -- SOLVING AFTER `i_1`
  have ⟨i, hᵢ⟩: ∃ i: ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).fst → rhsModuleType T₁ T₂ T₃, ∀ v₁, ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).snd (([v₀], []), ([], [v₂]), q₁.zip q₂) v₁ (i v₁) := by
    use (λ v₁ => ⟨⟨[v₀], []⟩, ⟨[v₁], [v₂]⟩, q₁.zip q₂⟩) <;> dsimp -- dsimp for beta-reduction
    intro v₂
    dsimp [rhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> trivial
  have ⟨s, hₛ⟩: ∃ s: ((lhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).fst → lhsModuleType T₁ T₂ T₃, ∀ v₁, ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO { inst := InstIdent.top, name := "i_1" }).snd ((q₁, q₂ ++ [v₂]), [v₀], []) v₁ (s v₁) := by
    use (λ v₁ => ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]⟩, ⟨[], []⟩⟩) <;> dsimp -- dsimp for β-reduction
    intro v₁
    rewrite [flushed_inputs_are_rflushed] <;> dsimp [rflushed]
    use ⟨⟨q₁, q₂ ++ [v₂]⟩, [v₀], [v₁]⟩ <;> apply And.intro
    . dsimp [lhsModule] <;> rewrite [PortMap.rw_rule_execution] <;> simp
    . constructor <;> and_intros
      . let rule := (lhsModule T₁ T₂ T₃).internals.get ⟨0, by dsimp [lhsModule]; trivial⟩
        apply existSR_single_step'
        use rule <;> apply And.intro
        . simp [rule]
        . simp [rule, lhsModule]
      . grind [lhsModule, pf]
  apply φᵢ.input _ _ _ _ _ (ind_imp_find ind₅) _ hᵢ hₛ
  dsimp
  intro v₁ <;> specialize hᵢ v₁ <;> specialize hₛ v₁
  have: (i v₁) = ⟨⟨[v₀], []⟩, ⟨[v₁], [v₂]⟩, q₁.zip q₂⟩ := by
    clear hₛ s
    dsimp [rhsModule] at hᵢ <;> rewrite [PortMap.rw_rule_execution] at hᵢ
    simp at hᵢ
    grind [Prod.mk.eta]
  rewrite [this] <;> clear this hᵢ i
  have: (s v₁) = ⟨⟨q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]⟩, ⟨[], []⟩⟩ := by
    rewrite [flushed_inputs_are_rflushed] at hₛ
    obtain ⟨s', hₛ, hₛ'⟩ := hₛ
    have: s' = ((q₁, q₂ ++ [v₂]), ([v₀], [v₁])) := by
      obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := s'
      dsimp [lhsModule] at hₛ <;> rewrite [PortMap.rw_rule_execution] at hₛ
      simp at hₛ <;> grind
    subst this <;> clear hₛ
    have: existSR (lhsModule T₁ T₂ T₃).internals ((q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]), ([], [])) (s v₁) := by
      reduce at v₀ v₁
      have: existSR (lhsModule T₁ T₂ T₃).internals ((q₁, q₂ ++ [v₂]), [v₀], [v₁]) ((q₁ ++ [(v₀, v₁)], q₂ ++ [v₂]), [], []) := by
        let rule := (lhsModule T₁ T₂ T₃).internals.get ⟨0, by dsimp [lhsModule]; trivial⟩
        apply existSR_single_step'
        use rule <;> apply And.intro
        . simp [rule]
        . simp [rule, lhsModule]
      apply newrule at this
      specialize this hₛ'
      apply flushesTo_implies_reachable
      assumption
    -- TODO: MOVE ALL THE pf states as we did with ind
    have: pf (lhsModule T₁ T₂ T₃) ((q₁ ++ [⟨v₀, v₁⟩], q₂ ++ [v₂]), ([], [])) :=
      by grind [pf, lhsModule]
    symm <;> apply pf_is_terminal <;> assumption
  rewrite [this] <;> clear this hₛ s
  -- CONCLUDE
  exact boo v₀ v₁ v₂ hₗ

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.input₂_preserves_φᵢ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms input₂_preserves_φᵢ

private lemma output_preserves_φᵢ: ∀ i s v i' s',
    φ₀ i s →
    ((rhsModule T₁ T₂ T₃).outputs.getIO { inst := InstIdent.top, name := "o_out" }).snd i v i' →
    ((lhsModule T₁ T₂ T₃).outputs.getIO { inst := InstIdent.top, name := "o_out" }).snd s (coe_out.mp v) s' →
    @φᵢ _ _ _ _ (rhsModule T₁ T₂ T₃) (flushed (lhsModule T₁ T₂ T₃)) _ φ₀ i' s' :=
by
  intro i s v i' s' h₁ h₂ h₃
  obtain ⟨q₁, q₂, _⟩ := h₁
  cases q₁ with
  | nil =>
    dsimp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂
    grind
  | cons hd₁ tl₁ => cases q₂ with
    | nil =>
      dsimp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂
      rewrite [List.zip_nil_right] at h₂
      grind
    | cons hd₂ tl₂ =>
      have: i' = (([], []), ([], []), tl₁.zip tl₂) := by
        obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i'
        dsimp [rhsModule] at h₂ <;> rewrite [PortMap.rw_rule_execution] at h₂
        grind
      subst this <;> clear h₂
      have: s' = ((tl₁, tl₂), [], []) := by
        obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := s'
        dsimp [lhsModule] at h₃ <;> rewrite [PortMap.rw_rule_execution] at h₃
        grind
      subst this <;> clear h₃
      apply φᵢ.base
      constructor
      grind

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.output_preserves_φᵢ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms output_preserves_φᵢ

private instance cpwi: CanProveWithInduction (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) φ₀ where
  input := by
    intro ident i s v mid_i mid_s φₕ hᵢ hₛ
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . simp[rhsModule] at HContains <;> rcases HContains with h | h | h <;> subst h
      -- NOTE: BECAUSE THIS TECHNIC REQUIRES ALL KIND OF SWAPS, WE CAN PROVE THAT IF ONE TRACE EXISTS THAT USES ALL THE INPUT PORTS
      -- THEN, NO NEED TO REDO THE WORK FOR ALL THE OTHER TRACES, ACTIONS AND RULES JUST SWAP
      -- NOTE THAT ONE CAN BUILD AN AUTOMATION HERE
      . exact input₀_preserves_φᵢ i s v mid_i mid_s φₕ hᵢ hₛ
      . exact input₁_preserves_φᵢ i s v mid_i mid_s φₕ hᵢ hₛ
      . exact input₂_preserves_φᵢ i s v mid_i mid_s φₕ hᵢ hₛ
    . exfalso; exact (PortMap.getIO_not_contained_false hᵢ HContains)
  output := by
    intro ident i s v mid_i mid_s φₕ hᵢ hₛ
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . simp[rhsModule] at HContains <;> subst HContains
      exact output_preserves_φᵢ i s v mid_i mid_s φₕ hᵢ hₛ
    . exfalso; exact (PortMap.getIO_not_contained_false hᵢ HContains)
  internal := by
    intro i s i' φₕ h
    apply Graphiti.φᵢ.base
    grind [φ₀, existSR, rhsModule]
  initial := by
    unfold Module.refines_initial
    intro i hᵢ
    use ⟨⟨[], []⟩, ⟨[], []⟩⟩ <;> apply And.intro
    . dsimp only [lhsModule] <;> grind
    . obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := hᵢ
      have: ∀ α β, (@List.nil α).zip (@List.nil β) = [] := by simp
      rewrite (occs := [2]) [<- this]
      constructor
      grind

/--
info: '_private.Graphiti.Projects.Flushability.JoinRewriteCorrect.0.Graphiti.JoinRewrite.cpwi' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cpwi

theorem fffffffffff: rhsModule T₁ T₂ T₃ ⊑ lhsModule T₁ T₂ T₃ := by
  apply Graphiti.inductively_refines _ _ φ₀

/--
info: 'Graphiti.JoinRewrite.fffffffffff' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fffffffffff

end InductiveRefinement

end Graphiti.JoinRewrite
