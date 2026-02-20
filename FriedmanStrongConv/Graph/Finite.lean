import Mathlib.Combinatorics.Graph.Basic
import FriedmanStrongConv.Graph.Dart
import Mathlib.Data.ENat.Lattice


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

section FiniteAt

/-!
## Finiteness at a vertex and notion of degree at this vertex

This section contains the notion of finiteness and degree at the vertex `x`.
-/

def edegree (x : α) : ℕ∞ := set.ncard dartSet x
