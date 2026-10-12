module

public import Purelib.Data.Function.Rat.Algebra
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic

import Purelib.CCL.Measure.Basic
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Function

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line.Basic

section
@[expose] public section

/-!
# Covariance enclosures from finite CCL prefixes

Three finite variance enclosures, for two rational probes and their sum,
enclose covariance through the exact rational polarization identity.  This
uses only displayed prefix families, rational interval arithmetic, and
finite weighted sums.
-/

namespace Purelib.Geometry.Projective.Chordal.Probe

set_option genInjectivity false in
/-- The finite sensitivity data needed to enclose the variance of one rational probe from CCL prefixes. -/
structure ProbeVarianceData (probe :
  Line.GaussianLine → Fraction.Rational) where
  /-- The rational factor bounding separation of probe values. -/ meanFactor : Fraction.Rational
  /-- The first-moment sensitivity factor is nonnegative. -/ meanFactorNonnegative : 0 ≤ meanFactor
  /-- Probe-value separation is bounded by the factor times squared chordal quadrance. -/ meanSensitive : ∀ left right,
    Distance.rationalSeparation (probe left) (probe right) ≤
      meanFactor * Chordal.Basic.chordalSq left right
  /-- The rational factor bounding separation of squared probe values. -/ squareFactor : Fraction.Rational
  /-- The second-moment sensitivity factor is nonnegative. -/ squareFactorNonnegative : 0 ≤ squareFactor
  /-- Squared-probe separation is bounded by its factor times squared chordal quadrance. -/ squareSensitive : ∀ left
    right,
    Distance.rationalSeparation
        (Rat.squareProbe probe left) (Rat.squareProbe probe right) ≤
      squareFactor * Chordal.Basic.chordalSq left right

constructive_injectivity ProbeVarianceData

section
end
end Purelib.Geometry.Projective.Chordal.Probe

end
