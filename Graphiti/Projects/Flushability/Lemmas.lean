/-
Copyright (c) 2025-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Graphiti.Core.Module
import Graphiti.Projects.Flushability.FlushedModule
import Graphiti.Projects.Flushability.ConfluentModule

namespace Graphiti

variable {Ident S : Type _}

variable (mod: Module Ident S)
variable [DecidableEq Ident]

-- TODO: WE ONLY NEED INTERNAL CONFLUENCE
instance [swap: DistinctActionStronglySwaps mod] [GloballyConfluent mod] [Flushable mod]: DistinctActionStronglySwaps (flushed mod) where
  inputs    := by
    intros ident₁ ident₂ s₁ v₁ v₂ s₂ s₃ h h₁ h₂
    rewrite [flushed_inputs_are_rflushed] at h₁
    rewrite [flushed_inputs_are_rflushed] at h₂
    obtain ⟨mid_s₁, h₁l, h₁r⟩ := h₁
    obtain ⟨mid_s₂, h₂l, h₂r⟩ := h₂
    apply flushesTo_implies_reachable at h₁r
    apply flushesTo_implies_reachable at h₂r
    sorry
  internals := by
    sorry
  outputs   := by
    dsimp [flushed]
    exact swap.outputs

end Graphiti
