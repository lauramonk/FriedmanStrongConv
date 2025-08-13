import Mathlib.Combinatorics.Graph.Basic

/- Additions to Graph.Basic -/

namespace Graph

variable {α β : Type*} {G : Graph α β} {x : α}

/-- `G.incSet x` is the set of edges incident to `x` in `G`. -/
def incSet (x : α) : Set β := {e | G.Inc e x}

/-- `G.loopSet x` is the set of loops at `x` in `G`. -/
def loopSet (x : α) : Set β := {e | G.IsLoopAt e x}

/-- The loopSet is included in the incSet-/
lemma loopSet_incl_incSet : G.loopSet x ⊆ G.incSet x := by
  intro _ h
  use x
  exact h
