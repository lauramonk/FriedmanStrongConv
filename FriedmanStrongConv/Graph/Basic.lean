import Mathlib.Combinatorics.Graph.Basic

/- Additions to Graph.Basic -/

universe u v
variable {α : Type u} {β : Type v} {x y z u v w : α} {e f : β}

namespace Graph

variable {G : Graph α β}

/-! Permutation graphs. -/

/-- The graph associated to a vertex-set `vertexSet` and a set of permutations `permSet` of
`vertexSet`. -/
def perm (vertexSet : Set α) {permSet : Set (Equiv.Perm α)}
(hP : ∀p ∈ permSet, p '' vertexSet ⊆ vertexSet) : Graph α (α × Equiv.Perm α) where
  vertexSet := vertexSet
  edgeSet := {e | e.1 ∈ vertexSet ∧ e.2 ∈ permSet}
  IsLink e x y := (e.1 ∈ vertexSet ∧ e.2 ∈ permSet) ∧ ((x = e.1 ∧ y = e.2 x) ∨ (y = e.1 ∧ x = e.2 y))
  isLink_symm := fun _ _ _ _ h => ⟨h.1, Or.comm.mp h.2⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w hxy hvw
    rcases hxy.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hvw.2 with  ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun he => ⟨e.1, e.2 e.1, he, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, h⟩ => h.1⟩
  left_mem_of_isLink := by
    intro e x y he
    rcases he.2 with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · exact he.1.1
    · apply hP e.2
      · exact he.1.2
      · simp; exact he.1.1

variable {vertexSet : Set α} {permSet : Set (Equiv.Perm α)} {hP : ∀p ∈ permSet, p '' vertexSet ⊆ vertexSet}
variable {x y : α} {e : α × Equiv.Perm α}

lemma perm.isLink : ((perm vertexSet hP).IsLink e x y) ↔ (e.1 ∈ vertexSet ∧ e.2 ∈ permSet) ∧
((x = e.1 ∧ y = e.2 x) ∨ (y = e.1 ∧ x = e.2 y)) := by exact Eq.to_iff rfl

lemma perm.edge_mem : ((perm vertexSet hP).IsLink e x y) → e.2 ∈ permSet := by
  rw [perm.isLink]
  exact fun h => h.1.2

lemma perm.vertex_mem :  ((perm vertexSet hP).IsLink e x y) → x ∈ vertexSet := by apply left_mem_of_isLink

lemma perm_isLoopAt : (perm vertexSet hP).IsLoopAt e x ↔ ((x ∈ vertexSet ∧ e.2 ∈ permSet) ∧ e.2 x = x) := sorry
