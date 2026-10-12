module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Gaussian.Process.Basic

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian

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

namespace Purelib.Approximation.Gaussian.Name.Basic

/-! ## Elementary arithmetic entry points -/

set_option genInjectivity false in
/-- A progressive process at one explicit finite state. -/
structure Named where
  /-- The retained progressive enclosure process. -/ process : Approximation.Gaussian.Process
  /-- The displayed finite state of that same retained process. -/ state : process.State

constructive_injectivity Named

namespace Named

/-- Name an exact Gaussian rational by its constant zero-radius process at the unit state. -/
def exact (value : Data.Gaussian.Basic.Canonical) :
  Approximation.Gaussian.Name.Basic.Named :=
  { process := Approximation.Gaussian.Process.exact value
    state := () }
end Named

end Purelib.Approximation.Gaussian.Name.Basic

end

section
section
@[expose] public section

/-!
# The integrated exponential family agrees with the existing `exp(1)-1` name

The right side below is the ordinary stateful subtraction of the existing
finite exponential name and exact one.  Its actual sampler retains the
exponential source index as the first component of its state.  We compare
through that index and its requested radius, rather than assuming equality
of independently selected samples or introducing a completed exponential.
-/

namespace Purelib.CCL.Progressive.ExponentialIntegrationEquivalence

open Purelib.Data.Gaussian

end Purelib.CCL.Progressive.ExponentialIntegrationEquivalence

end

end
