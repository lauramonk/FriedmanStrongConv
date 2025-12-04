/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import Mathlib.Combinatorics.Graph.Basic
import FriedmanStrongConv.Graph.Walks.Basic

universe u v
variable {α : Type u} {β : Type v} {x y z u v w : α} {e f : β}

namespace Graph

namespace Walk

variable {G : Graph α β}

/-- The concatenation of two compatible walks. -/
@[trans]
def append {x y z : α} : G.Walk x y → G.Walk y z → G.Walk x z
  | nil, q => q
  | cons h p, q => cons h (p.append q)
