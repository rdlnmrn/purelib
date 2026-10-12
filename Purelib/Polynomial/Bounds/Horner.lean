module

public import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Compatibility
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

@[expose] public section

-- Preserve the surveyed value/slope Bounds carrier name.

namespace Purelib.Polynomial.Bounds

set_option genInjectivity false in
/-- The selected original Gaussian value/slope carrier; coefficient steps
remain at their distinct rational-square and Gaussian-norm owners. -/
structure Horner where
  /-- The retained rational ceiling for the value component. -/ value : Fraction.Rational
  /-- The retained rational ceiling for the slope component. -/ slope : Fraction.Rational
deriving DecidableEq

constructive_injectivity Horner

namespace Horner.mk

end Horner.mk

namespace Horner.mk

end Horner.mk

end Purelib.Polynomial.Bounds
