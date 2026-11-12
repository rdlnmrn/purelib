module

public import Purelib.Riemann.Paths.OwnerTracePath
public import Purelib.Riemann.Paths.OwnerTraceReadings.Observation
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.RootContinuation.SquareRootTrace

/-! # Signed root agreement from a retained stationary trace link

The original OwnerLink already retains both exact owner tails, index
thresholds and its complete edge-realization operation. Its actual edge
certificate bounds the signed root displacement at every later pair.
That quantitative geometric evidence, together with the unchanged tracks'
square residuals, proves original root-name agreement. Equal base indices
alone supply no signed-root relation.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerLink

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Algebra.Quadratic.Pair.Polynomial.Expression (Denotation)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Paths.OwnerTraceReadings

/-- Derive signed operational agreement of both original Owners from this exact stationary link's edge realizations.

The stored realize function supplies the actual relative-distance proof;
no OwnerJoin, source preparation, polynomial continuation or root owner is
reconstructed. The new comparison requests only the original two tracks'
arbitrarily accurate square residuals and preserves their own thresholds.
-/
def equivalentStationary {polynomial : CoefficientPolynomial} {point : Canonical}
    {left right : Owner (polynomial.eval point)} (link : OwnerLink polynomial point point left right) :
    NamedEquivalent (ownerName left) (ownerName right) :=
  OwnerTail.equivalentOfNear link.leftTail link.rightTail link.leftIndex link.rightIndex link.left_ge link.right_ge (by
    intro first last firstLater lastLater
    have edge := link.realize first last firstLater lastLater
    have paid := edge.distance
    have nonnegative : 0 ≤ Basic.Canonical.normSq first.value := by
      rewrite [← first.norm_eq]
      exact link.leftTail.lower_positive.le.trans first.lower
    exact paid.trans (Fraction.Order.Field.divide_le_self nonnegative
      (Fraction.Cast.Order.natCast_le_direct (m := 1) (n := 1024) (by decide +kernel))))

/-- Compare both old coefficient observations using this same stationary link's actual signed realization evidence.

The original input link is retained unchanged. Its operational root
agreement is derived internally; the original denotation comparison reuses
both old observations and charges their actual state radii and tail target.
-/
def compareDenotations {polynomial : CoefficientPolynomial} {point : Canonical}
    {left right : Owner (polynomial.eval point)} (link : OwnerLink polynomial point point left right)
    {expression : Expression polynomial}
    (first : Denotation expression point (left.certificate left.parameterNonzero).value)
    (last : Denotation expression point (right.certificate right.parameterNonzero).value)
    (firstReading : Observation.Reading first.channel) (lastReading : Observation.Reading last.channel)
    (request : AccuracyRequest) : Observation.Comparison firstReading lastReading request.tolerance :=
  first.compare last link.equivalentStationary firstReading lastReading request

end Purelib.Riemann.Paths.OwnerTracePath.OwnerLink

end
