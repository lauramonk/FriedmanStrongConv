/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import Mathlib.Combinatorics.Graph.Basic
import FriedmanStrongConv.Graph.Dartwalks.Basic
import FriedmanStrongConv.Graph.Dartwalks.Operations

variable {α β : Type*} {x y z u v w : α} {e f : β}
variable (G : Graph α β)

namespace Graph

/-! ## `Reachable` and `Connected` -/

/-- Two vertices are *reachable* if there is a walk between them. -/
def Reachable (x y : α) : Prop := Nonempty (G.Dartwalk x y)

variable {G}

theorem reachable_iff_nonempty_univ {x y : α} :
    G.Reachable x y ↔ (Set.univ : Set (G.Dartwalk x y)).Nonempty :=
  Set.nonempty_iff_univ_nonempty

lemma not_reachable_iff_isEmpty_walk {x y : α} :
  ¬G.Reachable x y ↔ IsEmpty (G.Dartwalk x y) := not_nonempty_iff

protected theorem Reachable.elim {p : Prop} {x y : α} (h : G.Reachable x y)
    (hp : G.Dartwalk x y → p) : p :=
  Nonempty.elim h hp

protected theorem Dartwalk.reachable {G : Graph α β} {x y : α} (p : G.Dartwalk x y) :
  G.Reachable x y := ⟨p⟩

protected theorem Adj.reachable {x y : α} (h : G.Adj x y) : G.Reachable x y :=
  h.toDartwalk.reachable

@[refl]
protected theorem Reachable.refl (x : α) : G.Reachable x x := ⟨Dartwalk.nil⟩

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

theorem reachable_is_equivalence : Equivalence G.Reachable :=
  Equivalence.mk (@Reachable.refl (G := G)) (@Reachable.symm (G := G)) (@Reachable.trans (G := G))

/-- The equivalence relation on vertices given by `Graph.Reachable`. -/
def reachableSetoid : Setoid α := Setoid.mk _ G.reachable_is_equivalence

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ x y : V(G), G.Reachable x y

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V(G)]
