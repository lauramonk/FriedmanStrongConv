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

-- inductive Dart {G : Graph α β}
--   | Fwd : {x : α} -> {e : β} -> (h : G.IsLoopAt e x) -> Dart
--   | Bck : {x : α} -> {e : β} -> (h : G.IsLoopAt e x) -> Dart
--   | Dir : {x : α} -> {e : β} -> (h : G.IsNonloopAt e x) -> Dart

variable {G : Graph α β}

structure Dart extends α × α where
  edge : β
  isLink : G.IsLink edge fst snd
  orienOfEq : fst = snd -> Bool
  deriving DecidableEq

namespace Dart

lemma fst_mem (d : G.Dart) : d.fst ∈ V(G) := d.isLink.left_mem

lemma snd_mem (d : G.Dart) : d.snd ∈ V(G) := d.isLink.right_mem

lemma edge_mem (d : G.Dart) : d.edge ∈ E(G) := d.isLink.edge_mem

def symm (d : G.Dart) : G.Dart := -- todo

-- TODO: define a symmetry function which flips a dart
