import Mathlib.Combinatorics.Graph.Basic

/- Additions to Graph.Basic -/

namespace Graph

variable {α β : Type*} {G : Graph α β} {x : α}

/-- `G.incSet x` is the set of edges incident to `x` in `G`. -/
def incSet (x : α) : Set β := {e | G.Inc e x}

@[simp]
theorem mem_incSet (x : α) (e : β) : e ∈ G.incSet x ↔ G.Inc e x :=
  Iff.rfl

/-- `G.loopSet x` is the set of loops at `x` in `G`. -/
def loopSet (x : α) : Set β := {e | G.IsLoopAt e x}

@[simp]
theorem mem_loopSet (x : α) (e : β) : e ∈ G.loopSet x ↔ G.IsLoopAt e x :=
  Iff.rfl

/-- The loopSet is included in the incSet-/
lemma loopSet_incl_incSet : G.loopSet x ⊆ G.incSet x := by
  intro _ h
  use x
  exact h
