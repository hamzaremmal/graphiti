/-
Copyright (c) 2025-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas

namespace Graphiti

variable {Ident : Type _}
variable [deq: DecidableEq Ident]
variable {I : Type _}
variable {S : Type _}
variable {imod : Module Ident I}
variable {smod : Module Ident S}
variable [mm: MatchInterface imod smod]

def coe_in {ident} : ((imod.inputs.getIO ident).fst) = ((smod.inputs.getIO ident).fst) := by
  apply mm.input_types

def coe_out {ident} : ((imod.outputs.getIO ident).fst) = ((smod.outputs.getIO ident).fst) := by
  apply mm.output_types

end Graphiti
