/-
Copyright (c) 2025-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Graphiti.Core.Module

namespace Graphiti

variable {Ident S: Type _}
variable [DecidableEq Ident]
variable (mod: Module Ident S)

class SingleInternal (mod: Module Ident S): Prop where
  prop: mod.internals.length = 1

end Graphiti
