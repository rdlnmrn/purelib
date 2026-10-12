module
meta import Purelib.Elab.ConstructiveInjectivity

public import Purelib.Data.CCL.Transducer.Mode.Basic
public import Purelib.Data.List.Basic
import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace Purelib.Data.CCL.Transducer

open Purelib.Data.CCL.Transducer in
open Purelib.Data.List in
set_option genInjectivity false in
/-- Retain a nonempty emitted bit chunk and the exact next transducer mode.

The nonempty witness belongs to the stored word. The next mode carries its original process state and dependent
certificates for continuing after that same chunk. -/
structure Emission where
  /-- The exact finite bit chunk produced by this emission. -/ bits : Basic.BinaryWord
  /-- The retained emitted chunk contains at least one bit. -/ nonempty : bits ≠ []
  /-- The exact next mode retained after this chunk. -/ next : Mode

constructive_injectivity Emission

end Purelib.Data.CCL.Transducer

end
