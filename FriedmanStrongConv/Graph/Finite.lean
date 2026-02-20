import Mathlib.Combinatorics.Graph.Basic
import FriedmanStrongConv.Graph.Dart
import Mathlib.Data.Set.Card


/-!
# Definitions for finite and locally finite graphs

This file defines finite versions of the sets associated to a
graph, as well as the notion of degree, and elementary properties.


## Main definitions
[TODO]
-/

universe u v
variable {α : Type u} {β : Type v} {x y z u v w : α} {e f : β}

namespace Graph

variable (G : Graph α β)

/-- The edegree of a vertex `x` is the number of darts starting at `x`.
Note that, in particuliar, loops are counted twice.-/
noncomputable def edegree (x : α) : ENat := Set.encard (G.dartSet x)

/-- The degree of a vertex `x` is the number of darts starting at `x`,
with the junk value `0` if this is infinite.-/
noncomputable def degree (x : α) : ℕ := (G.edegree x).toNat

/-- A graph is locally finite if all of its vertices have finite degree.-/
abbrev LocallyFinite :=
  ∀ x : α, Finite (G.dartSet x)

/-- A graph is locally bounded if the degrees of its vertices are bounded.-/
abbrev LocallyBounded :=
  ∃ M : ℕ, ∀ x : α, G.edegree x < M

/-- A graph is regular of degree `d` if all of its vertices are of degree `d`.-/
def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ x : V(G), G.edegree x = d

theorem IsRegularOfDegree.degree_eq {d : ℕ} (h : G.IsRegularOfDegree d) (x : V(G)) : G.edegree x = d
:= h x
