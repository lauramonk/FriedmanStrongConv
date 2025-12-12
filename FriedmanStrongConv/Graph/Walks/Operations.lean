/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk
-/

import Mathlib.Combinatorics.Graph.Basic
import FriedmanStrongConv.Graph.Walks.Basic

open Function

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

@[simp]
theorem cons_append {x y z u : α} {e : β} (h : G.IsLink e x y) (p : G.Walk y z) (q : G.Walk z u) :
    (cons h p).append q = cons h (p.append q) := rfl

@[simp]
theorem cons_nil_append {x y z : α} {e : β} (h : G.IsLink e x y) (p : G.Walk y z) :
    (cons h nil).append p = cons h p := rfl

@[simp]
theorem nil_append {x y : α} (p : G.Walk x y) : nil.append p = p :=
  rfl

@[simp]
theorem append_nil {x y : α} (p : G.Walk x y) : p.append nil = p := by
  induction p <;> simp [*]

theorem append_assoc {x y z u : α} (p : G.Walk x y) (q : G.Walk y z) (r : G.Walk z u) :
    p.append (q.append r) = (p.append q).append r := by
  induction p <;> simp [*]

@[simp]
theorem append_copy_copy {x y z x' y' z'} (p : G.Walk x y) (q : G.Walk y z)
    (hx : x = x') (hy : y = y') (hz : z = z') :
    (p.copy hx hy).append (q.copy hy hz) = (p.append q).copy hx hz := by
  subst_vars
  rfl

theorem concat_nil {x y : α} {e : β} (h : G.IsLink e x y) : nil.concat h = cons h nil := rfl

@[simp]
theorem concat_cons {x y z u : α} {e f : β} (h : G.IsLink e x y) (p : G.Walk y z) (h' : G.IsLink f z u) :
    (cons h p).concat h' = cons h (p.concat h') := rfl

theorem append_concat {x y z u : α} {e : β} (p : G.Walk x y) (q : G.Walk y z) (h : G.IsLink e z u) :
    p.append (q.concat h) = (p.append q).concat h := append_assoc _ _ _

theorem concat_append {x y z u : α} {e : β} (p : G.Walk x y) (h : G.IsLink e y z) (q : G.Walk z u) :
    (p.concat h).append q = p.append (cons h q) := by
  rw [concat_eq_append, ← append_assoc, cons_nil_append]

/-- A non-trivial `cons` walk is representable as a `concat` walk. -/
theorem exists_cons_eq_concat {x y z : α} {e : β} (h : G.IsLink e x y) (p : G.Walk y z) :
    ∃ (u : α) (f : β) (q : G.Walk x u) (h' : G.IsLink f u z), cons h p = q.concat h' := by
  induction p generalizing x e with
  | nil => exact ⟨_, _, nil, h, rfl⟩
  | cons h' p ih =>
    obtain ⟨v, g, q, h'', hc⟩ := ih h'
    exact ⟨v, g, cons h q, h'', hc ▸ concat_cons _ _ _ ▸ rfl⟩

/-- A non-trivial `concat` walk is representable as a `cons` walk. -/
theorem exists_concat_eq_cons {x y z : α} {e : β} :
    ∀ (p : G.Walk x y) (h : G.IsLink e y z),
      ∃ (u : α) (f : β) (h' : G.IsLink f x u) (q : G.Walk u z), p.concat h = cons h' q
  | nil, h => ⟨_, _, h, nil, rfl⟩
  | cons h' p, h => ⟨_, _, h', Walk.concat p h, concat_cons _ _ _⟩

@[simp]
theorem reverse_nil {x : α} : (nil : G.Walk x x).reverse = nil := rfl

theorem reverse_singleton {x y : α} {e : β} (h : G.IsLink e x y) : (cons h nil).reverse = cons (h.symm) nil := rfl

@[simp]
theorem cons_reverseAux {x y z u : α} {e : β} (p : G.Walk x y) (q : G.Walk z u) (h : G.IsLink e z x) :
    (cons h p).reverseAux q = p.reverseAux (cons (h.symm) q) := rfl

@[simp]
protected theorem append_reverseAux {x y z u : α}
    (p : G.Walk x y) (q : G.Walk y z) (r : G.Walk x u) :
    (p.append q).reverseAux r = q.reverseAux (p.reverseAux r) := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact ih q (cons (h.symm) r)

@[simp]
protected theorem reverseAux_append {x y z u : α}
    (p : G.Walk x y) (q : G.Walk x z) (r : G.Walk z u) :
    (p.reverseAux q).append r = p.reverseAux (q.append r) := by
  induction p with
  | nil => rfl
  | cons h _ ih => simp [ih (cons (h.symm) q)]

protected theorem reverseAux_eq_reverse_append {x y z : α} (p : G.Walk x y) (q : G.Walk x z) :
    p.reverseAux q = p.reverse.append q := by simp [reverse]

@[simp]
theorem reverse_cons {x y z : α} {e : β} (h : G.IsLink e x y) (p : G.Walk y z) :
    (cons h p).reverse = p.reverse.append (cons (h.symm) nil) := by simp [reverse]

@[simp]
theorem reverse_copy {x y x' y'} (p : G.Walk x y) (hx : x = x') (hy : y = y') :
    (p.copy hx hy).reverse = p.reverse.copy hy hx := by
  subst_vars
  rfl

@[simp]
theorem reverse_append {x y z : α} (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).reverse = q.reverse.append p.reverse := by simp [reverse]

@[simp]
theorem reverse_concat {x y z : α} {e : β} (p : G.Walk x y) (h : G.IsLink e y z) :
    (p.concat h).reverse = cons (h.symm) p.reverse := by simp [concat_eq_append]

@[simp]
theorem reverse_reverse {x y : α} (p : G.Walk x y) : p.reverse.reverse = p := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem reverse_surjective {x y : α} : Function.Surjective (reverse : G.Walk x y → _) :=
  RightInverse.surjective reverse_reverse

theorem reverse_injective {x y : α} : Function.Injective (reverse : G.Walk x y → _) :=
  RightInverse.injective reverse_reverse

theorem reverse_bijective {x y : α} : Function.Bijective (reverse : G.Walk x y → _) :=
  ⟨reverse_injective, reverse_surjective⟩

@[simp]
theorem length_copy {x y x' y'} (p : G.Walk x y) (hx : x = x') (hy : y = y') :
    (p.copy hx hy).length = p.length := by
  subst_vars
  rfl

@[simp]
theorem length_append {x y z : α} (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).length = p.length + q.length := by
  induction p <;> simp [*, add_comm, add_assoc]

@[simp]
theorem length_concat {x y z : α} {e : β} (p : G.Walk x y) (h : G.IsLink e y z) :
    (p.concat h).length = p.length + 1 := length_append _ _

@[simp]
protected theorem length_reverseAux {x y z : α} (p : G.Walk x y) (q : G.Walk x z) :
    (p.reverseAux q).length = p.length + q.length := by
  induction p with
  | nil => simp!
  | cons _ _ ih => simp [ih, Nat.succ_add, add_assoc]

@[simp]
theorem length_reverse {x y : α} (p : G.Walk x y) : p.reverse.length = p.length := by simp [reverse]
