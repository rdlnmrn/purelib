module

import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Geometry.Projective.Line.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite-request processes of CCL prefixes

This module packages the operational use of progressively longer finite CCL
prefixes.  A request supplies a natural-number block count and returns one
new finite state whose displayed prefixes extend the current ones and meet
that count.  There is no stream of states and no eventual CCL value.
-/

namespace Purelib.Data.CCL.Encoding.Cylinder

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
set_option genInjectivity false in
/-- Retain a process extending a family of realized finite block prefixes to requested lengths.

Each item keeps one stable projective witness across every state. Requests preserve the current block prefix and meet
the requested count; every retained state also extends the same initial prefix. -/
structure PrefixFamilyProcess (ι : Type) where
  /-- The retained process-state carrier. -/ State : Type
  /-- The exact block list retained for a state and family item. -/ blocks : State → ι → List Data.CCL.Encoding.Block
  /-- The stable projective witness retained for each family item. -/ witness : ι →
    Line.GaussianLine
  /-- Every state realizes its exact blocks at the same retained item witness. -/ realizes : ∀ state item,
    Cylinder.Basic.Realizes (blocks state item) (witness item)
  /-- The retained initial process state. -/ initial : State
  /-- Produce a state for the supplied block-count request. -/ request : State → Nat → State
  /-- Each request preserves the preceding item's exact block prefix. -/ request_extends : ∀ state count item,
    ∃ suffix, blocks (request state count) item = blocks state item ++ suffix
  /-- Each requested state has at least the supplied number of blocks for every item. -/ request_length : ∀ state count
    item,
    count ≤ (blocks (request state count) item).length
  /-- Every retained state extends each item's exact initial block prefix. -/ extendsInitial : ∀ state item,
    ∃ suffix, blocks state item = blocks initial item ++ suffix

constructive_injectivity PrefixFamilyProcess

namespace PrefixFamilyProcess
end PrefixFamilyProcess

end Purelib.Data.CCL.Encoding.Cylinder

end
