/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Int.Basic

/-!
# Darts in graphs

A `Dart` or half-edge or bond in a graph is an oriented edge.
This file defines darts and proves some of their basic properties.
-/

universe u v w
variable {α : Type u} {β : Type v} {x y z u v w : α} {e f : β}

namespace Graph

variable {G : Graph α β}

/- A dart is describes a possible direction for a walk starting at one point.
In order to count walks correctly, we adopt the convention that each loop
can be taken in two distinct directions, encoded in orienOfEq. -/
@[ext]
structure Dart where
  fst : α
  snd : α
  edge : β
  isLink : G.IsLink edge fst snd
  orienOfEq : fst = snd -> Bool
  deriving DecidableEq

namespace Dart

lemma fst_mem (d : G.Dart) : d.fst ∈ V(G) := d.isLink.left_mem

lemma snd_mem (d : G.Dart) : d.snd ∈ V(G) := d.isLink.right_mem

lemma edge_mem (d : G.Dart) : d.edge ∈ E(G) := d.isLink.edge_mem

/- The reversing operation on darts, which reverses its orientation. -/
def reverse (d : G.Dart) : G.Dart :=
  Dart.mk d.snd d.fst d.edge d.isLink.symm (fun h => (d.orienOfEq h.symm).not)

/- The start point of the reverse dart is its end point. -/
lemma fst_of_reverse (d : G.Dart) : d.reverse.fst = d.snd := rfl

/- The end point of the reverse dart is its start point. -/
lemma snd_of_reverse (d : G.Dart) : d.reverse.snd = d.fst := rfl

/- The edge is unchanged upon reversing the dart. -/
lemma edge_of_reverse (d : G.Dart) : d.reverse.edge = d.edge := rfl

/- The reverse of a dart is distinct from the dart. -/
lemma reverse_neq_self (d : G.Dart) : d.reverse ≠ d := by
  by_cases h : d.fst = d.snd
  · sorry
  · sorry

/- The reverse of the reverse of a dart is the dart itself. -/
lemma reverse_of_reverse (d : G.Dart) : d.reverse.reverse = d := sorry

end Dart

/- The dartset of a vertex is the set of darts starting at this vertex. -/
def dartSet (x : α) : Set G.Dart := {d | d.fst = x}

lemma dart_of_edge (e : E(G)) : ∃ d : G.Dart, d.edge = e := sorry

/- Two darts have the same edge iff they are equal or reverse of one another. -/
lemma edge_dart_eq_iff {d₁ d₂ : G.Dart} (h : d₁.edge = d₂.edge) : d₁ = d₂ ∨ d₁ = d₂.reverse := sorry

/- An edge is incident to a vertex iff there is a dart starting at this vertex
carried by this edge.-/
lemma Inc_iff_exists_dart {x : α} {e : β} :
  G.Inc e x ↔ ∃ d : G.Dart, d.fst = x ∧ d.edge = e := by sorry
