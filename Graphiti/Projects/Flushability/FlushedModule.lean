/-
Copyright (c) 2025-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Mathlib.Tactic

import Graphiti.Core.Module
import Graphiti.Core.BasicLemmas
import Graphiti.Core.ModuleLemmas

import Graphiti.Projects.Flushability.Coe
import Graphiti.Projects.Flushability.ConfluentModule
import Graphiti.Projects.Flushability.RuleSwapping
import Graphiti.Projects.Flushability.DeterministicModule
import Graphiti.Projects.Flushability.Outputability

namespace Graphiti

section Flushability

variable {Ident S : Type _}

def pf (mod: Module Ident S) (s: S): Prop :=
  ∀ r ∈ mod.internals, ∀ s', ¬ r s s'

--TODO: Make it a structure?
inductive flushesTo: (Module Ident S) → S → S → Prop where
| mk: ∀ mod s₁ s₂,
  existSR mod.internals s₁ s₂
  → pf mod s₂
  → flushesTo mod s₁ s₂

def flushable (mod: Module Ident S) (s: S): Prop :=
  ∃ s', flushesTo mod s s'

class Flushable (mod: Module Ident S): Prop where
 flushable: ∀ s, flushable mod s

-- TODO: Add notations here

end Flushability

section FlushedModules

variable {Ident S : Type _}

def rflushed (mod: Module Ident S) (rule: RelIO S): RelIO S :=
  ⟨rule.1 , λ s ret s'' => ∃ s', rule.2 s ret s' ∧ flushesTo mod s' s''⟩

def isflushed (mod: Module Ident S) :=
  mod.init_state
  --λ s => ∃ s', mod.init_state s ∧ flushesTo mod s s' (Wrong definition, s itself is not flushed)
  --λ s => ∃ s', mod.init_state s' ∧ flushesTo mod s' s
  --λ s => mod.init_state s ∧ pf mod s
  --λ s => mod.init_state s ∧ flushable mod s

-- TODO: Should we make internal rules instead be a single rule using the flushesTo relation?
-- TODO: Should we make the output rules flush too?
-- TODO: With all of these changes, should we make a hierarchy of flushes modules (weaker and stronger than the above definition)?
def flushed (mod: Module Ident S): Module Ident S :=
  {
    inputs     := mod.inputs.mapVal (λ _ v => rflushed mod v) -- transform all the rules to flushed rules
    internals  := []                                          -- no more internal rules, inputs takes up the role of internals
    outputs    := mod.outputs                                 -- output rules remains unchanges
    init_state := isflushed mod                               -- Make sure the initial state is also flushed (use `iflushed`?)
  }

end FlushedModules

section MatchInterface

variable {Ident: Type _}
variable [DecidableEq Ident]

-- TODO: THIS REMOVE THIS THEOREM SINCE IT SHOULD BE DERIVED FROM [MatchInterface]
theorem flushed_preserves_ports {S : Type _} {mod: Module Ident S}:
  ∀ ident, (flushed mod).inputs.contains ident ↔ mod.inputs.contains ident :=
by
  intro ident
  dsimp [flushed]
  cases mod.inputs with
  | nil => simp [Batteries.AssocList.mapVal]
  | cons k hd tl =>
      dsimp [Batteries.AssocList.mapVal, Batteries.AssocList.contains, Batteries.AssocList.any] at *
      by_cases h: k = ident
      . subst h; simp
      . have: (k == ident) = false := decide_eq_false h
        simp [this]

instance {S: Type _} (mod: Module Ident S): MatchInterface (flushed mod) mod := by
  rw [MatchInterface_simpler_iff]
  intros <;> and_intros
  . rewrite [flushed, Batteries.AssocList.mapVal_mapVal] <;> dsimp [rflushed]
  . dsimp [flushed]

instance {S: Type _} (mod: Module Ident S): MatchInterface mod (flushed mod) := by
  haveI: MatchInterface (flushed mod) mod := by infer_instance
  apply MatchInterface_symmetric <;> assumption

instance {S₁ S₂: Type _} (mod₁: Module Ident S₁) (mod₂: Module Ident S₂) [MatchInterface mod₁ mod₂]: MatchInterface (flushed mod₁) (flushed mod₂) := by
  have: MatchInterface (flushed mod₁) mod₁ := by infer_instance
  have: MatchInterface mod₂ (flushed mod₂) := by infer_instance
  have: MatchInterface mod₁ (flushed mod₂) := by
    apply MatchInterface_transitive <;> assumption
  apply MatchInterface_transitive <;> assumption

instance {S₁ S₂: Type _} (mod₁: Module Ident S₁) (mod₂: Module Ident S₂) [MatchInterface mod₁ mod₂]: MatchInterface mod₁ (flushed mod₂) := by
  have: MatchInterface mod₂ (flushed mod₂) := by infer_instance
  apply MatchInterface_transitive <;> assumption

instance {S₁ S₂: Type _} (mod₁: Module Ident S₁) (mod₂: Module Ident S₂) [MatchInterface mod₁ mod₂]: MatchInterface (flushed mod₁) mod₂ := by
  have: MatchInterface (flushed mod₁) mod₁ := by infer_instance
  apply MatchInterface_transitive <;> assumption

end MatchInterface

variable {Ident S : Type _}

section FlushabilityLemmas

variable (mod: Module Ident S)

theorem everystate_is_pf_in_flushed:
  ∀ s, pf (flushed mod) s :=
by
  simp [pf, flushed]

theorem pf_is_terminal:
  ∀ s₁ s₂, pf mod s₁ → existSR mod.internals s₁ s₂ → s₁ = s₂ :=
by
  intro s₁ s₂ h₁ h₂
  cases h₂ with
  | done => rfl
  | step _ mid _ rule h₃ =>
    specialize h₁ rule h₃ mid
    contradiction

lemma flushesTo_implies_pf:
  ∀ s₁ {s₂}, flushesTo mod s₁ s₂ → pf mod s₂ :=
by
  intro _ _ h
  cases h
  assumption

lemma flushesTo_implies_reachable:
  ∀ {s₁ s₂}, flushesTo mod s₁ s₂ → existSR mod.internals s₁ s₂ :=
by
  intro _ _ h
  cases h
  assumption

lemma flushesTo_implies_flushable:
  ∀ {s₁ s₂}, flushesTo mod s₁ s₂ → flushable mod s₁ :=
by
  intros s₁ s₂ h
  use s₂

theorem flushesTo_reflexive:
  ∀ {s}, pf mod s → flushesTo mod s s :=
by
  intro s h
  constructor
  . apply existSR_reflexive
  . exact h

theorem flushesTo_transitive:
  ∀ {s₁} s₂ {s₃}, flushesTo mod s₁ s₂ → flushesTo mod s₂ s₃ → flushesTo mod s₁ s₃ :=
by
  intro s₁ s₂ s₃ h₁ h₂
  constructor
  . apply flushesTo_implies_reachable at h₁
    apply flushesTo_implies_reachable at h₂
    apply existSR_transitive
    . exact h₁
    . exact h₂
  . apply flushesTo_implies_pf
    exact h₂

theorem flushesTo_antisymmetric:
  ∀ s₁ s₂, flushesTo mod s₁ s₂ → flushesTo mod s₂ s₁ → s₁ = s₂ :=
by
  intro s₁ s₂ h₁ h₂
  have: pf mod s₁ := by apply flushesTo_implies_pf <;> assumption
  apply pf_is_terminal at this
  apply flushesTo_implies_reachable at h₁
  apply this
  assumption

theorem pf_is_flushable:
  ∀ s, pf mod s → flushable mod s :=
by
  intro s h
  use s
  exact flushesTo_reflexive mod h

instance: Flushable (flushed mod) := {
  flushable := by
    dsimp [flushable]
    intro s <;> use s
    apply flushesTo_reflexive
    apply everystate_is_pf_in_flushed
}

end FlushabilityLemmas

section QuasiConfluentModules

variable [DecidableEq Ident]
variable {mod: Module Ident S}
variable [qc: QuasiConfluent mod]

-- TODO: Can I weaken the requirements to only need LocalConfluence?
theorem newrule:
  ∀ s₁ s₂ s₃, existSR mod.internals s₁ s₂ → flushesTo mod s₁ s₃ → flushesTo mod s₂ s₃ :=
by
  intro _ _ s₃ h₁ h₂
  obtain ⟨h₂, g⟩ := h₂
  constructor
  . induction h₁ with
    | done => assumption
    | step _ mid _ rule h₃ _ _ ih =>
      apply ih <;> clear ih
      have: ∃ s₄, existSR mod.internals mid s₄ ∧ existSR mod.internals s₃ s₄ := by
        apply qc.internals <;> assumption
      obtain ⟨s₄, _, _⟩ := this
      have: s₃ = s₄ := by
        apply pf_is_terminal <;> assumption
      subst this
      assumption
  . exact g

/--
info: 'Graphiti.newrule' does not depend on any axioms
-/
#guard_msgs in
#print axioms newrule

-- TODO: This is basically a rewritting of the newrule
theorem flushable_reached_from_flushable:
  ∀ s₁ s₂, existSR mod.internals s₁ s₂ → flushable mod s₁ → flushable mod s₂ :=
by
  intros s₁ s₂ h₁ h₂
  obtain ⟨s₃, _⟩ := h₂
  use s₃
  apply newrule <;> assumption

end QuasiConfluentModules

section GloballyConfluentModules

variable {Ident S: Type _}
variable [DecidableEq Ident]
variable {mod: Module Ident S}
variable [fl: Flushable mod]
-- TODO: Can we reduce it to quasi/locally-confluent?
variable [gc: GloballyConfluent mod]

theorem flushed_is_unique:
  ∀ s, ∃! s', flushesTo mod s s' :=
by
  intro s
  obtain ⟨s₂, h₁⟩ := fl.flushable s
  use s₂ <;> dsimp <;> and_intros
  . exact h₁
  . intro y h₂
    have: pf mod s₂ := by apply flushesTo_implies_pf at h₁ <;> assumption
    have: pf mod y := by apply flushesTo_implies_pf at h₂ <;> assumption
    apply flushesTo_implies_reachable at h₁
    apply flushesTo_implies_reachable at h₂
    obtain ⟨w, _, _⟩ := gc.internals s s₂ y h₁ h₂
    have: s₂ = w := by apply pf_is_terminal <;> assumption
    subst this
    apply pf_is_terminal <;> assumption

theorem flushed_fn: ∃ f: S → S, ∀ s₁ s₂, flushesTo mod s₁ s₂ ↔ f s₁ = s₂ := by
  classical
  have h: ∀ s, ∃! s', flushesTo mod s s' := flushed_is_unique
  refine ⟨fun a => Classical.choose (h a), ?_⟩
  intro a b
  constructor
  · intro hRab
    have huniq := (Classical.choose_spec (h a)).2
    dsimp <;> symm
    exact huniq _ hRab
  · intro hEq
    subst hEq
    exact (Classical.choose_spec (h a)).1

/--
info: 'Graphiti.flushed_fn' depends on axioms: [Classical.choice]
-/
#guard_msgs in
#print axioms flushed_fn

end GloballyConfluentModules

section
  variable (mod: Module Ident S)
  variable [DecidableEq Ident]

-- TODO: Find a better name
-- todo, add tokens and states and make it a ↔
theorem flushed_inputs_are_rflushed: ∀ ident s₁ v s₂,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₂ ↔ (rflushed mod (mod.inputs.getIO ident)).snd s₁ (coe_in.mp v) s₂ :=
by
  intros ident _ _ _
  have: ((flushed mod).inputs.getIO ident) = (rflushed mod (mod.inputs.getIO ident)) := by
    dsimp [flushed, rflushed, PortMap.getIO]
    rw [Batteries.AssocList.find?_mapVal]
    by_cases h: mod.inputs.contains ident
    . rw [<- Batteries.AssocList.contains_find?_iff] at h
      obtain ⟨_, h⟩ := h; rw [h]
      dsimp only [Option.map_some, Option.getD_some]
    . apply Batteries.AssocList.contains_none at h
      rw [h]; dsimp
      simp only [false_and, exists_false]
  rw [Module.sigma_rw' this]

/--
info: 'Graphiti.flushed_inputs_are_rflushed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms flushed_inputs_are_rflushed

-- TODO: LocalConfluence should be enough here if newrule holds with local confluence
theorem flushed_reachable_from_nonflushed [lc: QuasiConfluent mod] : ∀ ident s₁ v s₂ s₃,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₃
  → (mod.inputs.getIO ident).snd s₁ (coe_in.mp v) s₂
  → existSR mod.internals s₂ s₃ :=
by
  intro ident s₁ v s₂ s₃ h₁ h₂
  rewrite [flushed_inputs_are_rflushed] at h₁
  dsimp [rflushed] at h₁
  obtain ⟨w, _, _, _⟩ := h₁
  have: ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals w s₄ := by
    apply lc.inputs <;> assumption
  obtain ⟨s₄, _, _⟩ := this
  have: existSR mod.internals s₄ s₃ := by
    have: flushesTo mod w s₃ := by
      constructor <;> assumption
    have: flushesTo mod s₄ s₃ := by
      apply newrule <;> assumption
    obtain ⟨_, _⟩ := this
    assumption
  apply existSR_transitive <;> assumption

theorem flushed_modules_has_flushed_states: ∀ ident s₁ v s₂,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₂ → pf mod s₂ :=
by
  intro ident _ _ _ h
  have HContains: mod.inputs.contains ident := by
    have mm: MatchInterface mod (flushed mod) := by infer_instance
    have: (flushed mod).inputs.contains ident := by
      apply PortMap.rule_contains <;> assumption
    rewrite [<- Batteries.AssocList.contains_find?_isSome_iff]
    rewrite [mm.inputs_present]
    rewrite [Batteries.AssocList.contains_find?_isSome_iff]
    exact this
  have: ∃ mrule, mod.inputs.find? ident = some mrule := by
    rw [Batteries.AssocList.contains_find?_iff] <;> assumption
  clear HContains
  obtain ⟨_, h₂⟩ := this
  apply PortMap.getIO_some at h₂
  subst h₂
  rewrite [flushed_inputs_are_rflushed] at h
  dsimp [rflushed] at h
  obtain ⟨_, _, _, _⟩ := h
  assumption

end

section Idempotence

variable {mod: Module Ident S}

theorem rflushed_idempotent:
  ∀ rule, rflushed mod (rflushed mod rule) = rflushed mod rule :=
by
  intros
  simp [rflushed]
  funext s ret s''
  apply propext
  constructor
  . intro ⟨_, ⟨w, _, _⟩, _⟩
    use w
    and_intros
    . assumption
    . apply flushesTo_transitive <;> assumption
  . intro ⟨w, _⟩
    use s''
    and_intros
    . use w
    . apply flushesTo_reflexive
      apply flushesTo_implies_pf
      cases ‹_ ∧ _›
      assumption

theorem findaname:
  ∀ s₁ s₂, flushesTo (flushed mod) s₁ s₂ → s₁ = s₂ :=
by
  intros _ _ h
  obtain ⟨h, _⟩ := h
  -- TODO: Make this a lemma, that in a flushed module, nothing is reachable
  dsimp [flushed] at h
  apply existSR_norules
  assumption

private theorem rflushed_idempotent':
  ∀ rule, rflushed (flushed mod) (rflushed mod rule) = rflushed mod rule :=
by
  intros
  rw (occs := .pos [1])[rflushed]
  rw (occs := .pos [4])[rflushed]
  congr
  funext s ret s''
  apply propext
  constructor
  . intro ⟨s', h₁, h₂⟩
    obtain ⟨w, _, _⟩ :=  h₁
    use w
    and_intros
    . assumption
    . apply findaname at h₂
      rwa [← h₂]
  . intro ⟨s', h₁, h₂⟩
    dsimp [rflushed]
    use s''
    and_intros
    . use s'
    . apply flushesTo_reflexive
      apply everystate_is_pf_in_flushed

theorem flushed_idempotent:
  flushed (flushed mod) = flushed mod :=
by
  -- TODO: Why can't I merge both rw by giving both positions to the first one? Bug in the tactic?
  rewrite (occs := .pos [1]) [flushed]
  rewrite (occs := .pos [5]) [flushed]
  ext
  . dsimp
    rw (occs := .pos [2]) [flushed] <;> dsimp
    rw [Batteries.AssocList.mapVal_mapVal]
    congr <;> funext _ rule
    exact rflushed_idempotent' rule
  . dsimp [flushed]
  . dsimp [flushed] <;> rfl -- TODO: Why do we have this form in the goal. What did ext do?
  . dsimp [flushed, isflushed]
    rfl

end Idempotence

section Confluence

-- TODO: Can we derive the confluence properties of a flushed module from the confluence properties
--       of the underlying module?

end Confluence

section Determinism

variable {mod: Module Ident S}
variable [DecidableEq Ident]

instance: DeterministicInternals (flushed mod) := {
  internal_deterministic := by
    intros _ h _ _ _ _ _
    dsimp [flushed] at h
    contradiction
}

instance [dt: DeterministicOutputs mod]: DeterministicOutputs (flushed mod) := {
  output_deterministic := by
    intros
    dsimp [flushed] at *
    apply dt.output_deterministic <;> assumption
}

instance [gc: GloballyConfluent mod]: DeterministicInputs (flushed mod) := {
  input_deterministic := by
    intros ident s₁ v s₂ s₃ h₁ h₂
    rewrite [flushed_inputs_are_rflushed] at h₁ h₂
    obtain ⟨w₁, hl₁, ⟨hr₁, h₁⟩⟩ := h₁
    obtain ⟨w₂, hl₂, ⟨hr₂, h₂⟩⟩ := h₂
    obtain ⟨w₃, hl₃, hr₃⟩ := gc.inputs ident s₁ (coe_in.mp v) w₁ w₂ hl₁ hl₂
    obtain ⟨w₄, hl₄, hr₄⟩ := gc.internals w₁ s₂ w₃ hr₁ hl₃
    obtain ⟨w₅, hl₅, hr₅⟩ := gc.internals w₂ s₃ w₃ hr₂ hr₃
    obtain ⟨w₆, hl₆, hr₆⟩ := gc.internals w₃ w₄ w₅ hr₄ hr₅
    have: s₃ = w₅ := pf_is_terminal mod s₃ w₅ h₂ hl₅
    subst this
    have: s₃ = w₆ := pf_is_terminal mod s₃ w₆ h₂ hr₆
    subst this
    have: s₂ = w₄ := pf_is_terminal mod s₂ w₄ h₁ hl₄
    subst this
    exact pf_is_terminal mod s₂ s₃ h₁ hl₆
}

instance [DeterministicOutputs mod] [GloballyConfluent mod]: Deterministic (flushed mod) := by
  constructor

end Determinism

/-section Wellfoundness

variable (mod: Module Ident S)
variable [DecidableEq Ident]
variable [fl: Flushable mod]

-- TODO: PROVE THAT FROM FLUSHABLE DIRECTLY??
private theorem wf: WellFounded (λ s₁ s₂ => existSR' mod.internals s₂ s₁) :=
by
  constructor
  intro s
  sorry

variable [lc: LocallyConfluent mod]

instance: GloballyConfluent mod where
  inputs    := lc.inputs
  internals := by
    intros s₁
    induction s₁ using (wf mod).induction
    rename_i s₁ ih
    intro s₂ s₃ h₂ h₃
    cases h₂ with
    | done => refine ⟨s₃, h₃, existSR_reflexive⟩
    | step _ mid₁ _ rule₁ _ h'₁ h'₂ =>
      cases h₃ with
      | done =>
        refine ⟨s₂, existSR_reflexive, ?_⟩
        have: existSR mod.internals s₁ mid₁ := by
          apply existSR_single_step <;> assumption
        apply existSR_transitive <;> assumption
      | step _ mid₂ _ rule₂ _ h''₁ h''₂ =>
        obtain ⟨d, h2d, h3d⟩: ∃ s₄, existSR mod.internals mid₁ s₄ ∧ existSR mod.internals mid₂ s₄ := by
          apply lc.internals s₁ mid₁ mid₂ rule₁ _ rule₂ <;> assumption

        have: existSR' mod.internals s₁ mid₁ := by
          apply existSR'.step _ _ _ rule₁ <;> try assumption
          exact existSR_reflexive
        obtain ⟨e, hbe, hde⟩ := ih mid₁ this s₂ d (by assumption) (by assumption)

        have: existSR' mod.internals s₁ mid₂ := by
          apply existSR'.step _ _ _ rule₂ <;> try assumption
          exact existSR_reflexive
        obtain ⟨f, hcf, hdf⟩ := ih mid₂ this s₃ d (by assumption) (by assumption)

        have: existSR' mod.internals s₁ d := by
          constructor <;> assumption
        obtain ⟨g, heg, hfg⟩ := ih d this e f hde hdf
        refine ⟨g, by apply existSR_transitive <;> assumption, by apply existSR_transitive <;> assumption⟩
  outputs   := lc.outputs

end Wellfoundness-/

section RuleSwap

variable [DecidableEq Ident]
variable {mod: Module Ident S}

-- TODO: THE WAY THIS IS WRITTEN IS NOT VERY FRIENDLY HERE
-- NOTE: NEED THE MODULE TO BE FLUSHABLE TOO, PROBABLY CONFLUENT TOO
-- I NEED DETERMINISM TO GET THE TRANSFORMATION FROM THE RELATION
instance [dass: DistinctActionSwaps' mod][GloballyConfluent mod]: DistinctActionStronglySwaps' (flushed mod) where
  inputs  := by
    intros ident₁ ident₂ s₁ v₂ s' s₃ h h₁ h₂
    have h₁: ∀ (v₁ : ((flushed mod).inputs.getIO ident₁).fst), (rflushed mod (mod.inputs.getIO ident₁)).snd s₁ (coe_in.mp v₁) (s' v₁) := by
      intro v₁
      specialize h₁ v₁
      rewrite [flushed_inputs_are_rflushed] at h₁
      exact h₁
    rename_i a <;> clear a
    rewrite [flushed_inputs_are_rflushed] at h₂
    dsimp [rflushed] at h₁ h₂
    --rewrite [forall_and] at h₁
    have := dass.inputs ident₁ ident₂ s₁ (coe_in.mp v₂) sorry sorry h
    sorry
  --outputs := sorry
  in_out  := sorry
  --out_in  := sorry
  in_int  := sorry
  --out_int := sorry

end RuleSwap

section Lemmas

variable {Ident S: Type _}
variable [DecidableEq Ident]
variable (mod: Module Ident S)

lemma m_imp_fm [f: Flushable mod] : ∀ ident s₁ v s₂,
  (mod.inputs.getIO ident).snd s₁ v s₂
  → ∃ s₃, ((flushed mod).inputs.getIO ident).snd s₁ (coe_in.mp v) s₃ :=
by
  intros ident _ _ s₂ _
  obtain ⟨s₃, _⟩ := f.flushable s₂
  use s₃
  rewrite [flushed_inputs_are_rflushed]
  simp [rflushed]
  use s₂

lemma fm_imp_m: ∀ ident s₁ v s₂,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₂
  → ∃ s₃, (mod.inputs.getIO ident).snd s₁ (coe_in.mp v) s₃ :=
by
  intros ident _ _ _ h
  rewrite [flushed_inputs_are_rflushed] at h
  simp [rflushed] at h
  obtain ⟨s₃, _, _⟩ := h
  simp
  use s₃

end Lemmas

section

  variable {Ident S : Type _}
  variable [DecidableEq Ident]

-- TODO: If we build a hierarchy of flushable modules. Should we also define a typeclass
--    for InputPreserversFlushability

class OutputPreservesFlushability (mod: Module Ident S) where
  rule: ∀ ident s₁ v s₂,
    pf mod s₁
  → (mod.outputs.getIO ident).snd s₁ v s₂
  →  pf mod s₂

-- This defintion maybe incomplete because it doesn't enforce that the same token will be outputed
-- TODO: Should we make it reachability preserves outputability?
--       In this case, flushing becomes a special case
class FlushabilityPreservesOutputability (mod: Module Ident S) where
  rule: ∀ ident s₁ s₂,
   outputable mod s₁ ident
   → flushesTo mod s₁ s₂
   → outputable mod s₂ ident

-- TODO: We can also define flushability preserves inputability for symmetry
-- Both of these properties should define wellformness (or be derived from wellformess)
-- of dataflow circuit (only DAGs?)

end

section Refinements

variable (mod: Module Ident S)
variable [DecidableEq Ident]

section FlushedRefinesNonFlushed

private theorem flushed_refinesφ_nonflushed:
  flushed mod ⊑_{Eq} mod :=
by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  subst_vars
  apply Module.comp_refines.mk
  . intro ident mid_i v h
    simp only [eq_mp_eq_cast, exists_and_left, exists_eq_right']
    rewrite [flushed_inputs_are_rflushed] at h
    dsimp [rflushed] at h
    obtain ⟨s', _, h⟩ := h
    apply flushesTo_implies_reachable at h
    use s'
  . intro _ mid_i _ _
    dsimp [flushed] at *
    use init_s, mid_i;
    and_intros <;> simpa [existSR_reflexive]
  . intro _ mid_i h _
    dsimp [flushed] at h
    contradiction

private theorem refines_init:
  Module.refines_initial (flushed mod) mod Eq :=
by
  unfold Module.refines_initial
  intros s h
  use s
  dsimp [flushed, isflushed] at h
  trivial

/-- TODO: WRITE THE DOCUMENTATION HERE -/
theorem flushed_refines_nonflushed:
  flushed mod ⊑ mod :=
by
  unfold Module.refines
  use (by infer_instance), Eq <;> and_intros
  . apply flushed_refinesφ_nonflushed
  . apply refines_init

/--
info: 'Graphiti.flushed_refines_nonflushed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms flushed_refines_nonflushed

end FlushedRefinesNonFlushed

section NonFlushedRefinesFlushed

variable [qc: QuasiConfluent mod] -- TODO: Can we only use local confluence?
variable [sm: RuleSwapWithMethods mod] -- TODO: Can we derive this property from some sort of confluence?
variable [fl: Flushable mod]
variable [opfm: OutputPreservesFlushability mod] -- TODO: Definition of flushed should guarantee this

private theorem nonflushed_refinesφ_flushed:
  mod ⊑_{flushesTo mod} flushed mod :=
by
  unfold Module.refines_φ
  intro init_i init_s h
  apply Module.comp_refines.mk
  . intros ident mid_i v _
    have: ∃ s₄, (mod.inputs.getIO ident).snd init_s v s₄ ∧ existSR mod.internals mid_i s₄ := by
      obtain ⟨_, _⟩ := h
      apply sm.inputs <;> assumption
    obtain ⟨s₄, h₂, _⟩ := this
    obtain h₃ := m_imp_fm mod ident init_s v s₄ h₂
    obtain ⟨s₃, h₃⟩ := h₃
    use s₃, s₃
    and_intros
    . assumption
    . apply existSR_reflexive
    . rewrite [flushed_inputs_are_rflushed] at h₃
      simp [rflushed] at h₃
      obtain ⟨s₅, _, _, _⟩ := h₃
      constructor
      . apply existSR_transitive _ _ s₄ _
        . assumption
        . have: ∃ s₆, existSR mod.internals s₄ s₆ ∧ existSR mod.internals s₅ s₆ := by
            apply qc.inputs <;> assumption
          obtain ⟨s₆, _, _⟩ := this
          apply existSR_transitive _ _ s₆ _
          . assumption
          . have: flushesTo mod s₅ s₃ := by
              constructor <;> assumption
            have: flushesTo mod s₆ s₃ := by
              apply newrule <;> assumption
            obtain ⟨_, _⟩ := this
            assumption
      . assumption
  . intros ident mid_i v _
    use init_s
    obtain ⟨_, _⟩ := h
    simp only [exists_and_left]
    and_intros
    . apply existSR_reflexive
    . obtain ⟨s₄, _, _⟩ := sm.outputs ident init_i v mid_i init_s (by assumption) (by assumption)
      use s₄
      dsimp [flushed]
      and_intros
      . assumption
      . constructor
        . assumption
        . apply opfm.rule <;> assumption
  . intros rule mid_i _ _
    use init_s
    and_intros
    . apply existSR_reflexive
    . have: existSR mod.internals init_i mid_i := by
        apply existSR_single_step <;> assumption
      have: ∃ s₄, existSR mod.internals mid_i s₄ ∧ existSR mod.internals init_s s₄ := by
          obtain ⟨_, _⟩ := h
          apply qc.internals <;> assumption
      obtain ⟨s₄, _, _⟩ := this
      have: existSR mod.internals init_i mid_i := by
        apply existSR_single_step <;> assumption
      apply newrule <;> assumption

omit qc sm opfm in
private theorem refines_init':
  Module.refines_initial mod (flushed mod) (flushesTo mod) :=
by
  unfold Module.refines_initial
  intros s h
  have ⟨s', _⟩ := fl.flushable s
  use s
  apply And.intro
  . dsimp [flushed, isflushed] <;> assumption
  . sorry -- TODO: Wellformness should solve this

theorem nonflushed_refines_flushed:
  mod ⊑ flushed mod :=
by
  unfold Module.refines
  have mm: MatchInterface mod (flushed mod) := by infer_instance
  use mm
  use (flushesTo mod)
  and_intros
  . apply nonflushed_refinesφ_flushed
  . apply refines_init'

end NonFlushedRefinesFlushed

section Indistinguishability

variable {S₁ S₂: Type _}
variable (mod₁: Module Ident S₁) (mod₂: Module Ident S₂)
variable [MatchInterface mod₁ mod₂]

variable (φ: S₁ → S₂ → Prop)

instance [ind: Indistinguishable mod₁ mod₂ φ][fl: Flushable mod₂] : Indistinguishable mod₁ (flushed mod₂) φ := by
  constructor
  intros i₁ s₁ φₕ
  have h: indistinguishable mod₁ mod₂ i₁ s₁ := ind.prop i₁ s₁ φₕ
  clear ind φₕ
  constructor
  . intros ident i₂ v h'
    have ⟨s₂, h₂⟩ := h.inputs_indistinguishable ident i₂ v h'
    have ⟨s₃, h₃⟩: ∃ s₃, flushesTo mod₂ s₂ s₃ := by
      apply fl.flushable
    use s₃
    rewrite [flushed_inputs_are_rflushed] <;> simp
    use s₂ <;> and_intros
    . exact h₂
    . exact h₃
  . dsimp [flushed] <;> exact h.outputs_indistinguishable

end Indistinguishability

end Refinements

end Graphiti
