module

public import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Process.Apart

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

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
namespace Named

set_option genInjectivity false in
/-- Denominator apartness is an explicit input to constructive division. -/
structure Apart (name : Gaussian.Name.Basic.Named) where
  /-- The uniform whole-ball apartness certificate for this exact retained name's process. -/ certificate :
    Approximation.Gaussian.Process.Apart name.process

constructive_injectivity Apart

end Named

end Purelib.Approximation.Gaussian.Name.Basic

end
