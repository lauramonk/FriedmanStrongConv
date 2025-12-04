/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import Mathlib.Combinatorics.Graph.Basic
import FriedmanStrongConv.Graph.Walk

variable {α β : Type*} {x y z u v w : α} {e f : β}
variable (G : Graph α β)

namespace Graph

/-! ## `Reachable` and `Connected` -/

/-- Two vertices are *reachable* if there is a walk between them. -/
def Reachable (x y : α) : Prop := Nonempty (G.Walk x y)

lemma not_reachable_iff_isEmpty_walk {x y : α} :
  ¬G.Reachable x y ↔ IsEmpty (G.Walk x y) := not_nonempty_iff

protected theorem Walk.reachable {G : Graph α β} {x y : α} (p : G.Walk x y) :
  G.Reachable x y := ⟨p⟩

protected theorem Adj.reachable {x y : α} (h : G.Adj x y) : G.Reachable x y :=
  h.toWalk.reachable

@[refl]
protected theorem Reachable.refl (x : α) : G.Reachable x x := ⟨Walk.nil⟩
