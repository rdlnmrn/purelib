module

public import Purelib.Data.GaussianInt.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

section
@[expose] public section

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Basic

set_option genInjectivity false in
/-- Gaussian-integer coefficients together with the positive real scale by
which the original finite Gaussian-rational list was multiplied. -/
structure ClearedCoefficients where
  /-- The natural real scale used for denominator clearing. -/ scale : Nat
  /-- The retained clearing scale is strictly positive. -/ scalePositive : 0 < scale
  /-- The displayed Gaussian-integer coefficient list after clearing denominators. -/ coefficients : List GaussianInt

constructive_injectivity ClearedCoefficients

end Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Basic

end
