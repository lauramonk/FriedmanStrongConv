/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import Mathlib.Combinatorics.Graph.Basic
import FriedmanStrongConv.Graph.Walks.Basic
import FriedmanStrongConv.Graph.Walks.Operations

variable {α β : Type*} {x y z u v w : α} {e f : β}
variable (G : Graph α β)

namespace Graph

/-! ## `Reachable` and `Connected` -/

/-- Two vertices are *reachable* if there is a walk between them. -/
def Reachable (x y : α) : Prop := Nonempty (G.Walk x y)

variable {G}

theorem reachable_iff_nonempty_univ {x y : α} :
    G.Reachable x y ↔ (Set.univ : Set (G.Walk x y)).Nonempty :=
  Set.nonempty_iff_univ_nonempty

lemma not_reachable_iff_isEmpty_walk {x y : α} :
  ¬G.Reachable x y ↔ IsEmpty (G.Walk x y) := not_nonempty_iff

protected theorem Reachable.elim {p : Prop} {x y : α} (h : G.Reachable x y)
    (hp : G.Walk x y → p) : p :=
  Nonempty.elim h hp

protected theorem Walk.reachable {G : Graph α β} {x y : α} (p : G.Walk x y) :
  G.Reachable x y := ⟨p⟩

protected theorem Adj.reachable {x y : α} (h : G.Adj x y) : G.Reachable x y :=
  h.toWalk.reachable

@[refl]
protected theorem Reachable.refl (x : α) : G.Reachable x x := ⟨Walk.nil⟩

@[simp] protected theorem Reachable.rfl {x : α} : G.Reachable x x := Reachable.refl _

@[symm]
protected theorem Reachable.symm {x y : α} (hxy : G.Reachable x y) : G.Reachable y x :=
  hxy.elim fun p => ⟨p.reverse⟩

theorem reachable_comm {x y : α} : G.Reachable x y ↔ G.Reachable y x :=
  ⟨Reachable.symm, Reachable.symm⟩

@[trans]
protected theorem Reachable.trans {x y z : α} (hxy : G.Reachable x y) (hyz : G.Reachable y z) :
    G.Reachable x z :=
  hxy.elim fun pxy => hyz.elim fun pyz => ⟨pxy.append pyz⟩

variable (G)

/-theorem reachable_is_equivalence : Equivalence G.Reachable :=
  Equivalence.mk (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)
-/
