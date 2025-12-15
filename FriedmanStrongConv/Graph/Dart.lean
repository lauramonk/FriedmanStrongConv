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
variable {α : Type u} {β : Type v} {γ : Type w} {x y z u v w : α} {e f : β} {i : ℤ}

namespace Graph

structure Dart (G : Graph α β) {γ : Type*} where
  /-- The dartSet -/
  dartSet : Set (γ)
  /-- The startpoint of a dart -/
  startPt : γ → V(G)
  /-- The endpoint of a dart -/
  endPt : γ → V(G)
  /-- The edge of a dart -/
  edge : γ → E(G)
  /-- The symmetric of a dart -/
  symm : γ → γ
  /-- The edge links the start and end -/
  isLink : ∀ d ∈ dartSet, G.IsLink (edge d) (startPt d) (endPt d)
  /-- The start point of the symmetric is the end point -/
  start_of_symm : ∀ d ∈ dartSet, startPt (symm d) = endPt d
  /-- The end point of the symmetric is the start point -/
  end_of_symm : ∀ d ∈ dartSet, endPt (symm d) = startPt d
  /-- The edge of the symmetric is the edge -/
  edge_of_symm : ∀ d ∈ dartSet, edge (symm d) = edge d
  /-- symm has no fixed point -/
  symm_neq_self : ∀ d ∈ dartSet, symm d ≠ d
  /-- Every edge is realised -/
  edge_surj : ∀ e ∈ E(G), ∃ d ∈ dartSet, e = edge d

namespace Dart

variable {G : Graph α β} {D : Dart G}

/-- `D.dartSetStart x` is the set of darts starting at `x` in `G`. -/
def dartSetStart (x : α) : Set γ := {d | D.startPt d = x}

/-- `D.dartSetPair x y` is the set of darts going from `x` to `y` in `G`. -/
def dartSetPair (x : α) (y : α) : Set γ := {d | D.startPt d = x ∧ D.endPt d = y}
