/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import Mathlib.Combinatorics.Graph.Basic

/-!
# Walks

In a graph, a *walk* is a finite sequence of adjacent vertices and corresponding edges.
The following notions are directly adapted from SimpleGraph, with the significant
difference that the edges need to be specified for a walk on a Graph due to multi-edges.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from [Chou1994].

## Main definitions

* `Graph.Walk` (with accompanying pattern definitions
  `Graph.Walk.nil'` and `Graph.Walk.cons'`)
* `Graph.Walk.Nil`: A predicate for the empty walk
* `Graph.Walk.length`: The length of a walk
* `Graph.Walk.support`: The list of vertices a walk visits in order
* `Graph.Walk.edges`: The list of edges a walk visits in order
* `Graph.Walk.edgeSet`: The set of edges of a walk visits

## Tags
walks
-/

universe u v
variable {α : Type u} {β : Type v} {x y z u v w : α} {e f : β}

namespace Graph

variable (G : Graph α β)

/-- A walk is a sequence of adjacent vertices together with the edges connecting them.
For vertices `x y : α`, the type `walk x y` consists of all walks starting at
`x` and ending at `y`.
Question: should the empty walk be defined for any `x : α` or only if `x ∈ V(G)`?
-/

inductive Walk : α → α → Type (max u v)
  | nil {x : α} : Walk x x
  | cons {x y z : α} {e : β} (h : G.IsLink e x y) (p : Walk y z) : Walk x z
  deriving DecidableEq

attribute [refl] Walk.nil

@[simps]
instance Walk.instInhabited (x : α) : Inhabited (G.Walk x x) := ⟨Walk.nil⟩

/-- The one-edge walk associated to a edge. -/
@[match_pattern]
abbrev IsLink.toWalk {G : Graph α β} {x y : α} {e : β} (h : G.IsLink e x y) : G.Walk x y :=
  Walk.cons h Walk.nil

/-- A one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern]
noncomputable abbrev Adj.toWalk {G : Graph α β} {x y : α} (h : G.Adj x y) : G.Walk x y :=
  h.choose_spec.toWalk

namespace Walk
variable {G}

/-- Pattern to get `Walk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (x : α) : G.Walk x x := Walk.nil

/-- Pattern to get `Walk.cons` with the vertices and edge as explicit arguments. -/
@[match_pattern]
abbrev cons' (x y z : α) (e : β) (h : G.IsLink e x y) (p : G.Walk y z) : G.Walk x z := Walk.cons h p

theorem exists_eq_cons_of_ne {x y : α} (hne : x ≠ y) :
    ∀ (p : G.Walk x y), ∃ (z : α) (e : β) (h : G.IsLink e x z) (p' : G.Walk z y), p = cons h p'
  | nil => (hne rfl).elim
  | cons' _ _ _ _ h p' => ⟨_, _, h, p', rfl⟩

/-- The length of a walk is the number of edges along it. -/
def length {x y : α} : G.Walk x y → ℕ
  | nil => 0
  | cons _ q => q.length.succ

@[simp]
theorem length_nil {x : α} : (nil : G.Walk x x).length = 0 := rfl

@[simp]
theorem length_cons {x y z : α} {e : β} (h : G.IsLink e x y) (p : G.Walk y z) :
    (cons h p).length = p.length + 1 := rfl

theorem eq_of_length_eq_zero {x y : α} : ∀ {p : G.Walk x y}, p.length = 0 → x = y
  | nil, _ => rfl

theorem adj_of_length_eq_one {x y : α} : ∀ {p : G.Walk x y}, p.length = 1 → G.Adj x y
  | cons h nil, _ => h.adj

@[simp]
theorem exists_length_eq_zero_iff {x y : α} : (∃ p : G.Walk x y, p.length = 0) ↔ x = y :=
  ⟨fun ⟨_, h⟩ ↦ (eq_of_length_eq_zero h), (· ▸ ⟨nil, rfl⟩)⟩

@[simp]
lemma exists_length_eq_one_iff {x y : α} : (∃ (p : G.Walk x y), p.length = 1) ↔ G.Adj x y := by
  refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun h ↦ ⟨h.toWalk, by simp⟩⟩
  induction p with
  | nil => simp at hp
  | cons h p' =>
    simp only [Walk.length_cons, add_eq_right] at hp
    exact (p'.eq_of_length_eq_zero hp) ▸ h.adj

@[simp]
theorem length_eq_zero_iff {x : α} {p : G.Walk x x} : p.length = 0 ↔ p = nil := by cases p <;> simp

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {x y : α} : G.Walk x y → List α
  | nil => [x]
  | cons _ p => x :: p.support

/-- The `edges` of a walk is the list of edges it visits in order. -/
def edges {x y : α} : G.Walk x y → List β
  | nil => []
  | cons' _ _ _ e _ p => e :: p.edges

@[simp]
theorem support_nil {x : α} : (nil : G.Walk x x).support = [x] := rfl

@[simp]
theorem support_cons {x y z : α} {e : β} (h : G.IsLink e x y) (p : G.Walk y z) :
    (cons h p).support = x :: p.support := rfl

@[simp]
theorem support_ne_nil {x y : α} (p : G.Walk x y) : p.support ≠ [] := by cases p <;> simp

@[simp]
theorem head_support {G : Graph α β} {x y : α} (p : G.Walk x y) :
    p.support.head (by simp) = x := by cases p <;> simp

@[simp]
theorem getLast_support {G : Graph α β} {x y : α} (p : G.Walk x y) :
    p.support.getLast (by simp) = y := by
  induction p <;> simp [*]

theorem support_eq_cons {x y : α} (p : G.Walk x y) : p.support = x :: p.support.tail := by
  cases p <;> simp

@[simp]
theorem start_mem_support {x y : α} (p : G.Walk x y) : x ∈ p.support := by cases p <;> simp

@[simp]
theorem end_mem_support {x y : α} (p : G.Walk x y) : y ∈ p.support := by induction p <;> simp [*]

@[simp]
theorem support_nonempty {x y : α} (p : G.Walk x y) : {z | z ∈ p.support}.Nonempty :=
  ⟨x, by simp⟩

theorem mem_support_iff {x y z : α} (p : G.Walk x y) :
    z ∈ p.support ↔ z = x ∨ z ∈ p.support.tail := by cases p <;> simp

theorem mem_support_nil_iff {x y : α} : x ∈ (nil : G.Walk y y).support ↔ x = y := by simp

@[simp]
theorem end_mem_tail_support_of_ne {x y : α} (h : x ≠ y) (p : G.Walk x y) : y ∈ p.support.tail := by
  obtain ⟨_, _, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

theorem support_subset_support_cons {x y z : α} {e : β} (p : G.Walk y z) (h : G.IsLink e x y) :
    p.support ⊆ (p.cons h).support := by
  simp

theorem coe_support {x y : α} (p : G.Walk x y) :
  (p.support : Multiset α) = {x} + p.support.tail := by cases p <;> rfl
