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
  edgeSet := {(v, p) : α × Equiv.Perm α | v ∈ vertexSet ∧ p ∈ permSet}
  IsLink e x y := (e.1 ∈ vertexSet ∧ e.2 ∈ permSet) ∧ ((x = e.1 ∧ y = e.2 x) ∨ (y = e.1 ∧ x = e.2 y))
  isLink_symm := fun _ _ _ _ h => ⟨h.1, Or.comm.mp h.2⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro _ _ _ _ _ h h'
    rcases h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h'.2 with  ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  edge_mem_iff_exists_isLink := by
    intro (v, p)
    exact ⟨fun he => ⟨v, p v, he, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, h⟩ => h.1⟩
  left_mem_of_isLink := by
    intro (_, p) _ _ h
    rcases h.2 with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · exact h.1.1
    · apply hP p
      · exact h.1.2
      · simp; exact h.1.1

namespace perm

variable {vertexSet : Set α} {permSet : Set (Equiv.Perm α)}
variable {hP : ∀p ∈ permSet, p '' vertexSet ⊆ vertexSet}
variable {x y v : α} {p : Equiv.Perm α}

lemma isLink_iff : ((perm vertexSet hP).IsLink (v, p) x y) ↔ (v ∈ vertexSet ∧ p ∈ permSet) ∧
((x = v ∧ y = p x) ∨ (y = v ∧ x = p y)) := by exact Eq.to_iff rfl

lemma left_mem : ((perm vertexSet hP).IsLink (v, p) x y) → x ∈ vertexSet := by apply left_mem_of_isLink

lemma right_mem : ((perm vertexSet hP).IsLink (v, p) x y) → y ∈ vertexSet := sorry

lemma edge_mem : ((perm vertexSet hP).IsLink (v, p) x y) → (v, p) ∈ (perm vertexSet hP).edgeSet := sorry

lemma permSet_mem : ((perm vertexSet hP).IsLink (v, p) x y) → p ∈ permSet := sorry

lemma isLink_rel : ((perm vertexSet hP).IsLink (v, p) x y) → (x = p y) ∨ (x = p.symm y) := sorry

lemma isLoopAt : (perm vertexSet hP).IsLoopAt (v, p) x ↔ ((x ∈ vertexSet ∧ p ∈ permSet) ∧ p x = x) := by
  constructor
  · intro hx
    constructor
    · exact ⟨left_mem hx, permSet_mem hx⟩
    · have : x = p x ∨ x = p.symm x := by exact isLink_rel hx
      rcases this with h | h
      · rw [← h]
      · rw [h]
        exact (Equiv.apply_eq_iff_eq_symm_apply p).mpr (congrArg (⇑(Equiv.symm p)) h) -- found with apply?
  · sorry
