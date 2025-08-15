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

variable {α β : Type*} (G : Graph α β)

section FiniteLoopAt

variable (x) [Fintype (G.loopSet x)]

/-- `G.loopFinset x` is the `Finset` version of `G.loopSet x` in case `G` has
a finite number of loops at `x`.-/
def loopFinset : Finset β := (G.loopSet x).toFinset

theorem loopFinset_def :
  G.loopFinset x = (G.loopSet x).toFinset := rfl

@[simp]
theorem mem_loopFinset (e : β) :
  e ∈ G.loopFinset x ↔ G.IsLink e x x := Set.mem_toFinset

end FiniteLoopAt

section FiniteAt

variable (x) [Fintype (G.incSet x)]

/-- `G.incFinset x` is the `Finset` version of `G.incSet x` in case `G` is
locally finite at `x`. -/
def incFinset : Finset β := (G.incSet x).toFinset

theorem incFinset_def :
  G.incFinset x = (G.incSet x).toFinset := rfl

@[simp]
theorem mem_incFinset (e : β) : e ∈ G.incFinset x ↔ G.Inc e x := Set.mem_toFinset

/-- If a graph has a finite number of incident edges at x then it has a finite number
of loops at x.-/
instance loopSetFintype [DecidableRel G.IsLoopAt] : Fintype (G.loopSet x) := sorry

/-- theorem loopFinset_eq_filter [DecidableRel IsLoopAt] :
    G.loopFinset x = ({e ∈ G.incFinset x | G.IsLoopAt e x} : Finset _) := by sorry--/

theorem loopFinset_subset (x : α) [Fintype (G.incSet x)] [DecidableRel G.IsLoopAt] :
    G.loopFinset x ⊆ G.incFinset x :=
  Set.toFinset_subset_toFinset.mpr (G.loopSet_subset x)

end FiniteAt

section Degree

variable (x) [Fintype (G.incSet x)] [DecidableRel G.IsLoopAt]

/-- `G.degree x` is the number of edges incident to `x`, with loops counted twice. -/
def degree : ℕ := #(G.incFinset x) + #(G.loopFinset x)

end Degree

section LocallyFinite

/-- A graph is locally finite if every vertex has a finite incidence set. -/
abbrev LocallyFinite :=
  ∀ x : α, Fintype (G.incSet x)

/-- A locally finite graph is regular of degree `d` if every vertex has degree `d`. -/
def IsRegularOfDegree (d : ℕ) [LocallyFinite G] [DecidableRel G.IsLoopAt] : Prop :=
  ∀ x : V(G), G.degree x = d

end LocallyFinite
