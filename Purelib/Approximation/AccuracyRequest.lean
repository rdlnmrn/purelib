module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

@[expose] public section

/-!
# Finite batches of arbitrary-accuracy requests

This module isolates a useful replacement for an appeal to an infinite
limit: every displayed finite list of positive rational demands has one
explicit final state satisfying all of them.  Preservation comes from finite
refinement, not compactness or a completed intersection.
-/

namespace Purelib.Approximation

set_option genInjectivity false in
/-- One positive rational accuracy demand. -/
structure AccuracyRequest where
  /-- The retained rational tolerance of this request. -/ tolerance : Fraction.Rational
  /-- The requested tolerance is strictly positive. -/ positive : 0 < tolerance

constructive_injectivity AccuracyRequest

namespace BoundProcess
end BoundProcess

namespace ProgressiveObservation
end ProgressiveObservation

end Purelib.Approximation

end
