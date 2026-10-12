module
import Purelib.Data.Rat.Interval.Proper
import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Resolution
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
import Purelib.Data.Rat.Interval.Width
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius

namespace Purelib.RootIsolation.Sturm.Event

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational

/-- Compute a positive leaf-width threshold for the polynomial and its derivative on a retained root cell.

The original coefficient-count squared radius is retained together with
the constant one. Their minimum permits the same interval width to
control its squared lower-endpoint displacement. -/
@[expose] public def eventLeafWidth (polynomial : Dense.Basic.RationalPolynomial) (root :
  Interval.Proper.Cell) : Fraction.Rational :=
  CauchyIndex.EventPartition.Resolution.eventLeafWidth
    (Dense.Derivative.derivative polynomial) polynomial root

/-- The coefficient-computed event leaf-width threshold is strictly positive.

The polynomial and its original derivative determine the same reduced
Cauchy pair on the retained root cell. Its positive event threshold
therefore supplies this identical Sturm leaf-width bound. -/
public theorem eventLeafWidth_pos (polynomial : Dense.Basic.RationalPolynomial) (root :
  Interval.Proper.Cell) :
    0 < eventLeafWidth polynomial root :=
  CauchyIndex.EventPartition.Resolution.eventLeafWidth_pos
    (Dense.Derivative.derivative polynomial) polynomial root

/-! ## Simultaneous leaf classifiers -/

/-- Certificate-retaining resolution from explicit refinement and width
evidence.  This direct interface is shared by the ordinary common partition
and its finer squarefree/Taylor specialization.

The supplied leaf refinement and width inequality control its original
squared endpoint radius. The same reduced polynomial/derivative clearance
then extracts the scanner-selected certificate without rebuilding it. -/
@[expose] public def polynomialEventResolutionOfBounds
    (event : Dense.Basic.RationalPolynomial) (root leaf : Interval.Proper.Cell)
    (refines : leaf.interval.Refines root.interval)
    (widthSmall : (Data.Rat.Interval.Bounds.width leaf.interval) < eventLeafWidth event root) :
    CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
      (Pair.Reduction.reducedNumerator (Dense.Derivative.derivative event) event)
      (Pair.Reduction.reducedDenominator (Dense.Derivative.derivative event) event)
      leaf.interval :=
  CauchyIndex.Events.Resolution.cauchyEventResolutionOfRefinedRadiusSq
    (CauchyIndex.EventPartition.Resolution.reducedClearance
      (Dense.Derivative.derivative event) event root)
    refines
    (Interval.Radius.EventPartition.sampleRadiusSq_lt_of_width_lt
      leaf.proper widthSmall)

end Purelib.RootIsolation.Sturm.Event
