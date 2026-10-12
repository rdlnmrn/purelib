module
public import Purelib.Data.CCL.Transducer.Emission.Semantics.Basic
import Purelib.Data.CCL.Transducer.Emission.Semantics.Initial
import Purelib.Data.CCL.Transducer.Emission.Semantics.Loop
import Purelib.Data.CCL.Transducer.Emission.Semantics.Low
import Purelib.Data.CCL.Transducer.Emission.Semantics.Residual
public import Purelib.Data.CCL.Transducer.Emission.Step
import Purelib.Data.CCL.Transducer.Mode.Basic

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Data.CCL.Transducer.Emission.Semantics.Step

open Purelib.Data.CCL.Transducer in
/-- Every retained transducer mode emits a chunk preserving its exact projective parser representation. -/
theorem step_exact : ∀ mode : Data.CCL.Transducer.Mode,
  Emission.Semantics.Basic.ExactEmission mode (Emission.Step.step mode)
  | .initial current => Emission.Semantics.Initial.initialStep_exact current
  | .low current => Emission.Semantics.Low.lowStep_exact current
  | .loop current => Emission.Semantics.Loop.loopStep_exact current
  | .residual current => Emission.Semantics.Residual.residualStep_exact current

end Purelib.Data.CCL.Transducer.Emission.Semantics.Step

end
