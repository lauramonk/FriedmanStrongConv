/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import Mathlib.Combinatorics.Graph.Basic

universe u v
variable {α : Type u} {β : Type v} {x y z u v w : α} {e f : β}

namespace Graph


variable {G : Graph α β}

/-- A walk is a sequence of adjacent vertices together with the edges connecting them.
For vertices `x y : α`, the type `walk x y` consists of all walks starting at
`x` and ending at `y`. We should perhaps adopt the convention that the empty walk is only defined
for vertices of the graph (to implement).
-/

inductive Walk : α → α → Type (max u v)
  | nil {x : α} : Walk x x
  | cons {x y z : α} {e : β} (h : G.IsLink e x y) (p : Walk y z) : Walk x z
  deriving DecidableEq

/-- The one-edge walk associated to a edge. -/
@[match_pattern]
abbrev IsLink.toWalk {G : Graph α β} {x y : α} {e : β} (h : G.IsLink e x y) : G.Walk x y :=
  Walk.cons h Walk.nil

/-- A one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern]
noncomputable abbrev Adj.toWalk {G : Graph α β} {x y : α} (h : G.Adj x y) : G.Walk x y :=
  h.choose_spec.toWalk
