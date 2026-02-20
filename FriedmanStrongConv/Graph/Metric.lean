/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import FriedmanStrongConv.Graph.Connectivity
import Mathlib.Data.ENat.Lattice

/-!
# Graph metric

This module defines the `Graph.edist` function, which takes pairs of vertices to the length of
the shortest walk between them, or `⊤` if they are disconnected. It also defines `Graph.dist`
which is the `ℕ`-valued version of `Graph.edist`.

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
  ⨅ w : G.Dartwalk x y, w.length

variable {G} {x y z : α}

theorem edist_eq_sInf : G.edist x y = sInf (Set.range fun w : G.Dartwalk x y ↦ (w.length : ℕ∞)) := rfl

protected theorem Reachable.exists_walk_length_eq_edist (hr : G.Reachable x y) :
    ∃ p : G.Dartwalk x y, p.length = G.edist x y :=
  csInf_mem <| Set.range_nonempty_iff_nonempty.mpr hr

  protected theorem Connected.exists_walk_length_eq_edist (hconn : G.Preconnected) {x y : V(G)} :
    ∃ p : G.Dartwalk x y, p.length = G.edist x y :=
  (hconn x y).exists_walk_length_eq_edist

theorem edist_le (p : G.Dartwalk x y) :
    G.edist x y ≤ p.length :=
  sInf_le ⟨p, rfl⟩
protected alias Dartwalk.edist_le := edist_le

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
    ∃ p : G.Dartwalk x y, p.length = G.edist x y :=
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
      rw [← hp, ← hq, ← Nat.cast_add, ← Dartwalk.length_append]
      exact edist_le _

theorem edist_comm : G.edist x y = G.edist y x := by
  rw [edist_eq_sInf, ← Set.image_univ, ← Set.image_univ_of_surjective Dartwalk.reverse_surjective,
    ← Set.image_comp, Set.image_univ, Function.comp_def]
  simp_rw [Dartwalk.length_reverse, ← edist_eq_sInf]

lemma exists_walk_of_edist_eq_coe {k : ℕ} (h : G.edist x y = k) :
    ∃ p : G.Dartwalk x y, p.length = k :=
  have : G.edist x y ≠ ⊤ := by rw [h]; exact ENat.coe_ne_top _
  have ⟨p, hp⟩ := exists_walk_of_edist_ne_top this
  ⟨p, Nat.cast_injective (hp.trans h)⟩

lemma edist_ne_top_iff_reachable : G.edist x y ≠ ⊤ ↔ G.Reachable x y := by
  refine ⟨reachable_of_edist_ne_top, fun h ↦ ?_⟩
  by_contra hx
  simp only [edist, iInf_eq_top, ENat.coe_ne_top] at hx
  exact h.elim hx
