module
import Purelib.Data.CCL.Transducer.Emission.Basic
public import Purelib.Data.CCL.Transducer.Emission.Initial
import Purelib.Data.CCL.Transducer.Emission.Loop
public import Purelib.Data.CCL.Transducer.Emission.Low
public import Purelib.Data.CCL.Transducer.Emission.Residual
import Purelib.Data.CCL.Transducer.Mode.Basic

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

namespace Purelib.Data.CCL.Transducer.Emission.Step

open Purelib.Data.CCL.Transducer in
/-- Dispatch the retained transducer mode to its exact certified nonempty emission procedure.

Initial, low, loop and residual cases keep their original dependent state records and use the corresponding constructor
without changing its selected witnesses or next process owner. -/
def step : Data.CCL.Transducer.Mode → Data.CCL.Transducer.Emission
  | .initial current => Emission.Initial.initialStep current
  | .low current => Emission.Low.lowStep current
  | .loop current => Emission.Loop.loopStep current
  | .residual current => Emission.Residual.residualStep current

end Purelib.Data.CCL.Transducer.Emission.Step

end
