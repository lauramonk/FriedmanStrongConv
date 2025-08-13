import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Fintype.BigOperators
import FriedmanStrongConv.Graph.Basic

/-!
# Definitions for finite and locally finite graphs

This file defines finite versions of the sets associated to a
graph, as well as the notion of degree, and elementary properties.
We follow the approach from SimpleGraph and only use minimal hypotheses.

## Main definitions
[TODO]
-/

open Finset Function

namespace Graph

section FiniteAt

variable {α β : Type*} {G : Graph α β}

variable (x) [Fintype (G.incSet x)]
/-- `G.incFinset x` is the `Finset` version of `G.incSet x` in case `G` is
locally finite at `x`. -/
def incFinset : Finset β := (G.incSet x).toFinset

theorem incFinset_def : G.incFinset x = (G.incSet x).toFinset := rfl

@[simp]
theorem mem_incFinset (e : β) : e ∈ G.incFinset x ↔ G.Inc e x :=
  Set.mem_toFinset

end FiniteAt

section FiniteLoop

variable {α β : Type*} {G : Graph α β}

variable (x) [Fintype (G.loopSet x)]

/-- `G.loopFinset x` is the `Finset` version of `G.loopSet x` in case `G` has
a finite number of loops at `x`.-/
def loopFinset : Finset β := (G.loopSet x).toFinset

theorem loopFinset_def : G.loopFinset x = (G.loopSet x).toFinset := rfl

@[simp]
theorem mem_loopFinset (e : β) : e ∈ G.loopFinset x ↔ G.IsLink e x x :=
  Set.mem_toFinset

end FiniteLoop

section Degree

variable {α β : Type*} {G : Graph α β}

variable (x) [Fintype (G.incSet x)] [Fintype (G.loopSet x)]  /-Remove redundant hypothesis-/

/-- `G.degree x` is the number of edges incident to `x`, with loops counted twice. -/
def degree : ℕ := #(G.incFinset x) + #(G.loopFinset x)

end Degree
