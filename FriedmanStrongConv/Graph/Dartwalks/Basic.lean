/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk and Freddie Nash
-/

import Mathlib.Combinatorics.Graph.Basic
import FriedmanStrongConv.Graph.Dart

/-!
# Dartwalks

In a graph, a *dartwalk* is a finite sequence of darts, i.e. oriented edges.
The following notions are directly adapted from the library SimpleGraph. A significant distinction
here is that, on the presence of loops and multi-edges, different notions of walks can be defined
and yield different walk counting problems. Here, we focus on dartwalks, which means that the
walk knows precisely which edge is traversed (in particular multi-edges will yield different
walks between adjacent vertices), and in which direction (i.e. any loop corresponds to two
distinct walks of length 1).

## Main definitions

* `Graph.Dartwalk` (with accompanying pattern definitions
  `Graph.Dartwalk.nil'` and `Graph.Dartwalk.cons'`)
* `Graph.Dartwalk.Nil`: A predicate for the empty dartwalk
* `Graph.Dartwalk.length`: The length of a dartwalk
* `Graph.Dartwalk.support`: The list of vertices a dartwalk visits in order
* `Graph.Dartwalk.edges`: The list of edges a dartwalk visits in order

## Tags
dartwalks
-/

universe u v
variable {α : Type u} {β : Type v} {x y z u v w : α} {e f : β}

namespace Graph

variable (G : Graph α β)

/-- A dartwalk is a sequence of connecting darts.
For vertices `x y : α`, the type `dartwalk x y` consists of all dartwalks starting at
`x` and ending at `y`.
We here accept the junk value `dartwalk x x` for any `x : α` even if `x` is not a vertex.
-/
inductive Dartwalk : α → α → Type (max u v)
  | nil {x : α} : Dartwalk x x
  | cons {x y z : α} {d : Dart} (h : G.IsDartLink d x y) (p : Dartwalk y z) : Dartwalk x z

attribute [refl] Dartwalk.nil

@[simps]
instance Dartwalk.instInhabited (x : α) : Inhabited (G.Dartwalk x x) := ⟨Dartwalk.nil⟩

/-- The one-dart dartwalk associated to a dart. -/
@[match_pattern]
abbrev IsDartLink.toDartwalk {G : Graph α β} {x y : α} {d : Dart} (h : G.IsDartLink d x y) :
  G.Dartwalk x y := Dartwalk.cons h Dartwalk.nil

 @[match_pattern]
abbrev Link.toDartwalk {G : Graph α β} {x y : α} {e : β} (h : G.IsLink e x y) :
 G.Dartwalk x y := sorry

 @[match_pattern]
noncomputable abbrev Adj.toDartwalk {G : Graph α β} {x y : α} (h : G.Adj x y) :
 G.Dartwalk x y := sorry

namespace Dartwalk
variable {G}

/-- Pattern to get `Dartwalk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (x : α) : G.Dartwalk x x := Dartwalk.nil

/-- Pattern to get `Dartwalk.cons` with the vertices and edge as explicit arguments. -/
@[match_pattern]
abbrev cons' (x y z : α) (d : Dart) (h : G.IsDartLink d x y) (p : G.Dartwalk y z) : G.Dartwalk x z := Dartwalk.cons h p

theorem exists_eq_cons_of_ne {x y : α} (hne : x ≠ y) :
    ∀ (p : G.Dartwalk x y), ∃ (z : α) (d : Dart) (h : G.IsDartLink d x z) (p' : G.Dartwalk z y), p = cons h p'
  | nil => (hne rfl).elim
  | cons' _ _ _ _ h p' => ⟨_, _, h, p', rfl⟩

/-- The length of a dartwalk is the number of darts along it. -/
def length {x y : α} : G.Dartwalk x y → ℕ
  | nil => 0
  | cons _ q => q.length.succ

@[simp]
theorem length_nil {x : α} : (nil : G.Dartwalk x x).length = 0 := rfl

@[simp]
theorem length_cons {x y z : α} {d : Dart} (h : G.IsDartLink d x y) (p : G.Dartwalk y z) :
    (cons h p).length = p.length + 1 := rfl

theorem eq_of_length_eq_zero {x y : α} : ∀ {p : G.Dartwalk x y}, p.length = 0 → x = y
  | nil, _ => rfl

-- TOFIX
-- theorem adj_of_length_eq_one {x y : α} : ∀ {p : G.Dartwalk x y}, p.length = 1 → G.Adj x y
--   | cons h nil, _ => h.adj

@[simp]
theorem exists_length_eq_zero_iff {x y : α} : (∃ p : G.Dartwalk x y, p.length = 0) ↔ x = y :=
  ⟨fun ⟨_, h⟩ ↦ (eq_of_length_eq_zero h), (· ▸ ⟨nil, rfl⟩)⟩

-- TOFIX
-- @[simp]
-- lemma exists_length_eq_one_iff {x y : α} : (∃ (p : G.Dartwalk x y), p.length = 1) ↔ G.Adj x y := by
--   refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun h ↦ ⟨h.toWalk, by simp⟩⟩
--   induction p with
--   | nil => simp at hp
--   | cons h p' =>
--     simp only [Walk.length_cons, add_eq_right] at hp
--     exact (p'.eq_of_length_eq_zero hp) ▸ h.adj

@[simp]
theorem length_eq_zero_iff {x : α} {p : G.Dartwalk x x} : p.length = 0 ↔ p = nil := by cases p <;> simp

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {x y : α} : G.Dartwalk x y → List α
  | nil => [x]
  | cons _ p => x :: p.support

/-- The `edges` of a dartwalk is the list of edges it visits in order. -/
def edges {x y : α} : G.Dartwalk x y → List β
  | nil => []
  | cons' _ _ _ d _ p => d.edge :: p.edges

@[simp]
theorem support_nil {x : α} : (nil : G.Dartwalk x x).support = [x] := rfl

@[simp]
theorem support_cons {x y z : α} {d : Dart} (h : G.IsDartLink d x y) (p : G.Dartwalk y z) :
    (cons h p).support = x :: p.support := rfl

@[simp]
theorem support_ne_nil {x y : α} (p : G.Dartwalk x y) : p.support ≠ [] := by cases p <;> simp

@[simp]
theorem head_support {G : Graph α β} {x y : α} (p : G.Dartwalk x y) :
    p.support.head (by simp) = x := by cases p <;> simp

@[simp]
theorem getLast_support {G : Graph α β} {x y : α} (p : G.Dartwalk x y) :
    p.support.getLast (by simp) = y := by
  induction p <;> simp [*]

theorem support_eq_cons {x y : α} (p : G.Dartwalk x y) : p.support = x :: p.support.tail := by
  cases p <;> simp

@[simp]
theorem start_mem_support {x y : α} (p : G.Dartwalk x y) : x ∈ p.support := by cases p <;> simp

@[simp]
theorem end_mem_support {x y : α} (p : G.Dartwalk x y) : y ∈ p.support := by induction p <;> simp [*]

@[simp]
theorem support_nonempty {x y : α} (p : G.Dartwalk x y) : {z | z ∈ p.support}.Nonempty :=
  ⟨x, by simp⟩

theorem mem_support_iff {x y z : α} (p : G.Dartwalk x y) :
    z ∈ p.support ↔ z = x ∨ z ∈ p.support.tail := by cases p <;> simp

theorem mem_support_nil_iff {x y : α} : x ∈ (nil : G.Dartwalk y y).support ↔ x = y := by simp

@[simp]
theorem end_mem_tail_support_of_ne {x y : α} (h : x ≠ y) (p : G.Dartwalk x y) : y ∈ p.support.tail := by
  obtain ⟨_, _, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

theorem support_subset_support_cons {x y z : α} {d : Dart} (p : G.Dartwalk y z) (h : G.IsDartLink d x y) :
    p.support ⊆ (p.cons h).support := by
  simp

theorem coe_support {x y : α} (p : G.Dartwalk x y) :
  (p.support : Multiset α) = {x} + p.support.tail := by cases p <;> rfl
