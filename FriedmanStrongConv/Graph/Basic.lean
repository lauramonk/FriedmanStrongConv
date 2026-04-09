import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Sym.Sym2


/- Additions to Graph.Basic -/

universe u v
variable {α : Type u} {β : Type v} {x y z u v w : α} {e f : β}

private lemma Sym2.fst_eq_iff {x y a b : α} (h : s(x, y) = s(a, b)) : x = a ∨ x = b := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := Sym2.eq_iff.mp h <;> simp

namespace Graph

variable {G : Graph α β}

/-! Permutation graphs. -/

structure permEdge (α : Type*) where
  fst : α
  perm : Equiv.Perm α

def permEdge.snd {e : permEdge α} := e.perm e.fst

/-- The graph associated to a vertex-set `vertexSet` and a set of permutations `permSet` of
`vertexSet`. -/
def perm (vertexSet : Set α) {permSet : Set (Equiv.Perm α)}
(hP : ∀p ∈ permSet, p '' vertexSet ⊆ vertexSet) : Graph α (permEdge α) where
  vertexSet := vertexSet
  edgeSet := {e : permEdge α | e.fst ∈ vertexSet ∧ e.perm ∈ permSet}
  IsLink e x y := (e.fst ∈ vertexSet ∧ e.perm ∈ permSet) ∧ (s(x, y) = s(e.fst, e.snd))
  isLink_symm := by
    intro _ _ _ _ _
    rw [Sym2.eq_swap]
    assumption
  eq_or_eq_of_isLink_of_isLink := fun _ _ _ _ _ ⟨_, h⟩ ⟨_, h'⟩ => Sym2.fst_eq_iff (h' ▸ h)
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun he => ⟨e.fst, e.snd, he, rfl⟩, fun ⟨_, _, h⟩ => h.1⟩
  left_mem_of_isLink := by sorry

-- namespace perm

-- variable {vertexSet : Set α} {permSet : Set (Equiv.Perm α)}
-- variable {hP : ∀p ∈ permSet, p '' vertexSet ⊆ vertexSet}
-- variable {x y v : α} {p : Equiv.Perm α}

-- lemma isLink_iff : ((perm vertexSet hP).IsLink (v, p) x y) ↔ (v ∈ vertexSet ∧ p ∈ permSet) ∧
-- ((x = v ∧ y = p x) ∨ (y = v ∧ x = p y)) := by exact Eq.to_iff rfl

-- lemma left_mem : ((perm vertexSet hP).IsLink (v, p) x y) → x ∈ vertexSet := by apply left_mem_of_isLink

-- lemma right_mem : ((perm vertexSet hP).IsLink (v, p) x y) → y ∈ vertexSet := sorry

-- lemma edge_mem : ((perm vertexSet hP).IsLink (v, p) x y) → (v, p) ∈ (perm vertexSet hP).edgeSet := sorry

-- lemma permSet_mem : ((perm vertexSet hP).IsLink (v, p) x y) → p ∈ permSet := sorry

-- lemma isLink_rel : ((perm vertexSet hP).IsLink (v, p) x y) → (x = p y) ∨ (x = p.symm y) := sorry

-- lemma isLoopAt : (perm vertexSet hP).IsLoopAt (v, p) x ↔ ((x ∈ vertexSet ∧ p ∈ permSet) ∧ p x = x) := by
--   constructor
--   · intro hx
--     constructor
--     · exact ⟨left_mem hx, permSet_mem hx⟩
--     · have : x = p x ∨ x = p.symm x := by exact isLink_rel hx
--       rcases this with h | h
--       · rw [← h]
--       · rw [h]
--         exact (Equiv.apply_eq_iff_eq_symm_apply p).mpr (congrArg (⇑(Equiv.symm p)) h) -- found with apply?
--   · sorry
