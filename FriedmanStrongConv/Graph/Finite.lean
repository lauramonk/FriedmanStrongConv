import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.Graph.Basic

/-!
# Definitions for finite and locally finite graphs

This file defines finite versions of the sets associated to a
graph, as well as the notion of degree, and elementary properties.
We follow the approach from SimpleGraph and only use minimal hypotheses.

## Main definitions
[TODO]
-/

open Finset Function

namespace Graph

variable {α β : Type*} {G : Graph α β}
