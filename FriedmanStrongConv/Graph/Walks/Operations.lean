/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import Mathlib.Combinatorics.Graph.Basic
import FriedmanStrongConv.Graph.Walks.Basic

universe u v
variable {α : Type u} {β : Type v} {x y z u v w : α} {e f : β}

namespace Graph

namespace Walk

variable {G : Graph α β}

/-- Change the endpoints of a walk using equalities. This is helpful for relaxing
definitional equality constraints and to be able to state otherwise difficult-to-state
lemmas. While this is a simple wrapper around `Eq.rec`, it gives a canonical way to write it.

The simp-normal form is for the `copy` to be pushed outward. That way calculations can
occur within the "copy context." -/
protected def copy {x y x' y'} (p : G.Walk x y) (hx : x = x') (hy : y = y') : G.Walk x' y' :=
  hx ▸ hy ▸ p

@[simp]
theorem copy_rfl_rfl {x y} (p : G.Walk x y) : p.copy rfl rfl = p := rfl

@[simp]
theorem copy_copy {x y x' y' x'' y''} (p : G.Walk x y)
    (hx : x = x') (hy : y = y') (hx' : x' = x'') (hy' : y' = y'') :
    (p.copy hx hy).copy hx' hy' = p.copy (hx.trans hx') (hy.trans hy') := by
  subst_vars
  rfl

@[simp]
theorem copy_nil {x x'} (hx : x = x') : (Walk.nil : G.Walk x x).copy hx hx = nil := by
  subst_vars
  rfl

theorem copy_cons {x y z x' z'} {e} (h : G.IsLink e x y) (p : G.Walk y z) (hx : x = x') (hz : z = z') :
    (Walk.cons h p).copy hx hz = Walk.cons (hx ▸ h) (p.copy rfl hz) := by
  subst_vars
  rfl

@[simp]
theorem cons_copy {x y z y' z'} {e} (h : G.IsLink e x y) (p : G.Walk y' z') (hy : y' = y) (hz : z' = z) :
    cons h (p.copy hy hz) = (Walk.cons (hy ▸ h) p).copy rfl hz := by
  subst_vars
  rfl

/-- The concatenation of two compatible walks. -/
@[trans]
def append {x y z : α} : G.Walk x y → G.Walk y z → G.Walk x z
  | nil, q => q
  | cons h p, q => cons h (p.append q)

/-- The reversed version of `Graph.Walk.cons`, concatenating an edge to
the end of a walk. -/
def concat {x y z : α} {e : β} (p : G.Walk x y) (h : G.IsLink e y z) : G.Walk x z := p.append (cons h nil)

theorem concat_eq_append {x y z : α} {e : β} (p : G.Walk x y) (h : G.IsLink e y z) :
    p.concat h = p.append (cons h nil) := rfl

/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def reverseAux {x y z : α} : G.Walk x y → G.Walk x z → G.Walk y z
  | nil, q => q
  | cons h p, q => Walk.reverseAux p (cons (h.symm) q)

/-- The walk in reverse. -/
@[symm]
def reverse {x y : α} (p : G.Walk x y) : G.Walk y x := p.reverseAux nil
