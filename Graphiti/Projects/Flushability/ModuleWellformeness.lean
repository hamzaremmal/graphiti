/-
Copyright (c) 2025-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Mathlib.Tactic

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas

namespace Graphiti

variable {Ident S: Type _}
variable [DecidableEq Ident]

class WellFormed (mod : Module Ident S) :=
  can_input :  (ident: InternalPort Ident) → (s: S) → (v: (mod.inputs.getIO ident).fst) → Prop
  can_output: (ident: InternalPort Ident) → (s: S) → (v: (mod.outputs.getIO ident).fst) → Prop
  input : ∀ ident s v, can_input ident s v  → ∃ s', (mod.inputs.getIO ident).snd s v s'
  output: ∀ ident s v, can_output ident s v → ∃ s', (mod.outputs.getIO ident).snd s v s'

class InhabitedPorts (mod : Module Ident S) :=
  inputs : ∀ ident, Nonempty (mod.inputs.getIO ident).fst
  outputs: ∀ ident, Nonempty (mod.outputs.getIO ident).fst

end Graphiti
