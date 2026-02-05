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

inductive Dart {G : Graph α β}
  | Fwd : {x : α} -> {e : β} -> (h : G.IsLoopAt e x) -> Dart
  | Bck : {x : α} -> {e : β} -> (h : G.IsLoopAt e x) -> Dart
  | Dir : {x : α} -> {e : β} -> (h : G.IsNonloopAt e x) -> Dart

variable {G : Graph α β}

namespace Dart

-- TODO: define Dart.vertex_mem which takes a dart and shows x is in V(G)
-- using IsLoopAt.vertex_mem and IsNonloopAt.vertex_mem

-- def startPt : G.Dart → V(G)
--   | Fwd (h : G.IsLoopAt _ x) => x
--   | Bck (h : G.IsLoopAt _ x) => x
--   | Dir (h : G.IsNonloopAt _ x) => x


-- def endPt : G.Dart → V(G)
--   | Fwd (h : G.IsLoopAt x) => x
--   | Bck (h : G.IsLoopAt x) => x
--   | Dir (h : G.IsNonloopAt e x) =>
 -- TODO: take the y from IsNonloopAt using Inc.inc_other

-- TODO: define Dart.edge_mem which takes a dart and shows e is in E(G)
-- using IsLoopAt.edge_mem and IsNonloopAt.edge_mem

-- def edge : G.Dart → E(G)
--   | Fwd (h : G.IsLoopAt e _) => e
--   | Bck (h : G.IsLoopAt e _) => e
--   | Dir (h : G.IsNonloopAt e _) => e


-- TODO: define a symmetry function which flips a dart
-- Might need a lemma showing that if IsNonLoopAt e x then IsNonLoopAt e y where
-- y is the other endpoint (would be easy as we can just take x)
