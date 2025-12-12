/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara, Rida Hamadani
-/

import FriedmanStrongConv.Graph.Connectivity
import Mathlib.Data.ENat.Lattice

/-!
# Graph metric

This module defines the `SimpleGraph.edist` function, which takes pairs of vertices to the length of
the shortest walk between them, or `⊤` if they are disconnected. It also defines `SimpleGraph.dist`
which is the `ℕ`-valued version of `SimpleGraph.edist`.

## Main definitions

- `Graph.edist` is the graph extended metric.
- `Graph.dist` is the graph metric.
-/

namespace Graph

variable {α β : Type*} {x y z u v w : α} {e f : β}
variable (G : Graph α β)

/-! ## Metric -/

section edist

/--
The extended distance between two vertices is the length of the shortest walk between them.
It is `⊤` if no such walk exists.
-/
noncomputable def edist (x y : α) : ℕ∞ :=
  ⨅ w : G.Walk x y, w.length

variable {G} {x y z : α}

theorem edist_eq_sInf : G.edist x y = sInf (Set.range fun w : G.Walk x y ↦ (w.length : ℕ∞)) := rfl

protected theorem Reachable.exists_walk_length_eq_edist (hr : G.Reachable x y) :
    ∃ p : G.Walk x y, p.length = G.edist x y :=
  csInf_mem <| Set.range_nonempty_iff_nonempty.mpr hr

  protected theorem Connected.exists_walk_length_eq_edist (hconn : G.Preconnected) {x y : V(G)} :
    ∃ p : G.Walk x y, p.length = G.edist x y :=
  (hconn x y).exists_walk_length_eq_edist

theorem edist_le (p : G.Walk x y) :
    G.edist x y ≤ p.length :=
  sInf_le ⟨p, rfl⟩
protected alias Walk.edist_le := edist_le

@[simp]
theorem edist_eq_zero_iff :
    G.edist x y = 0 ↔ x = y := by
  apply Iff.intro <;> simp [edist, ENat.iInf_eq_zero]

@[simp]
theorem edist_self : edist G x x = 0 :=
  edist_eq_zero_iff.mpr rfl

theorem edist_pos_of_ne (hne : x ≠ y) :
    0 < G.edist x y :=
  pos_iff_ne_zero.mpr <| edist_eq_zero_iff.ne.mpr hne

lemma edist_eq_top_of_not_reachable (h : ¬G.Reachable x y) :
    G.edist x y = ⊤ := by
  simp [edist, not_reachable_iff_isEmpty_walk.mp h]

theorem reachable_of_edist_ne_top (h : G.edist x y ≠ ⊤) :
    G.Reachable x y :=
  not_not.mp <| edist_eq_top_of_not_reachable.mt h

lemma exists_walk_of_edist_ne_top (h : G.edist x y ≠ ⊤) :
    ∃ p : G.Walk x y, p.length = G.edist x y :=
  (reachable_of_edist_ne_top h).exists_walk_length_eq_edist

protected theorem edist_triangle : G.edist x z ≤ G.edist x y + G.edist y z := by
  cases eq_or_ne (G.edist x y) ⊤ with
  | inl hxy => simp [hxy]
  | inr hxy =>
    cases eq_or_ne (G.edist y z) ⊤ with
    | inl hyz => simp [hyz]
    | inr hyz =>
      obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top hxy
      obtain ⟨q, hq⟩ := exists_walk_of_edist_ne_top hyz
      rw [← hp, ← hq, ← Nat.cast_add, ← Walk.length_append]
      exact edist_le _
