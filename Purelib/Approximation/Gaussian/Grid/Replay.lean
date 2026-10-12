module

public import Init.Data.Int.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Checked replay of bounded Newton proposal traces

Saved integer grid coordinates are checked by multiplication and inequalities;
saved Newton updates are checked by multiplication.  Replay does not call the
floor or Newton proposal generators.  The starting proposal is explicit, so
diameter preparation can supply its checked warm-up result while ordinary
refinement supplies the box midpoint.  The existing finite candidate acceptance
check is retained, including its safe-side selection and winding.
All imports are already audited finite dependencies of checked shrinking.
-/

namespace Purelib.Approximation.Gaussian.Grid.Replay

set_option genInjectivity false in
/-- Integer grid coordinates retained for finite replay.

The record stores the proposed real and imaginary floors; a replay checker supplies the separate arithmetic validation.
-/
structure Witness where
  /-- The retained integer floor for the real coordinate. -/ realFloor : Int
  /-- The retained integer floor for the imaginary coordinate. -/ imaginaryFloor : Int

constructive_injectivity Witness

end Purelib.Approximation.Gaussian.Grid.Replay

end
