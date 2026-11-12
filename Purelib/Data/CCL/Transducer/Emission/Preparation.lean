module

public import Purelib.Data.CCL.Transducer.Emission.Basic
public import Purelib.Data.CCL.Transducer.Mode.Observation
public import Purelib.Approximation.Gaussian.Process.Route

/-!
# Retained original emission work

The original nonempty emission keeps its own next mode. Its preparation
retains that same mode's observation, the original source route and the
actual number of source-interface calls paid by this finite transition.
-/

public section

namespace Purelib.Data.CCL.Transducer.Emission

open Purelib.Approximation.Gaussian

set_option genInjectivity false in
/-- One original nonempty emission with its exact next observation and paid source work retained.

The route has the same supplied source owner and the emission's original
next process. The next ball and witness are cached data, so downstream
snapshot construction and admission need no further source observation.
-/
structure Prepared (source : Process) where
  /-- The actual original nonempty emission. -/ emission : Emission
  /-- The same original source routed through the returned mode's owned chart. -/ route :
    Process.Route source emission.next.process
  /-- The exact returned mode's original observation. -/ observation : Mode.Observation emission.next
  /-- The actual opaque source-interface calls made by the retained preparation. -/ sourceCalls : Nat

end Purelib.Data.CCL.Transducer.Emission
