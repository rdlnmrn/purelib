module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Table.CCL.Request
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Approximation.Matrix.Operational.Integral.Action
public import Purelib.Curves.Legendre.GaussManin.StandardLoops
import Purelib.Curves.Legendre.Monodromy
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Examples.Curves.Legendre.Crossings.UpperZero
public import Purelib.Examples.Curves.Legendre.Loops.One
public import Purelib.Examples.Riemann.ExplicitLegendreNormalizedAcquisition
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Table.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Examples.Curves.Legendre.LoopBaseBranches
import Purelib.Riemann.Periods.PeriodMatrix

section
public section

/-!
# Concrete raw period transport for the rational Legendre loops

The explicit standard loops and explicit base-fibre branch tracks are joined
here without asserting an equality between periods on different fibres.
Closed-loop continuation evaluates the actual base period programs on the
transported homology basis, hence uses the transpose of the certified braid
matrix.  All displayed period observations remain caller-bounded finite
requests.
-/

namespace Purelib.Examples.Curves.Legendre.PeriodTransport

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data.Rat
open Purelib.Examples

open Purelib.Examples.Riemann

open Purelib.Approximation.Gaussian.Vector.Operational.Basic (VectorEquivalent)
open Purelib.Approximation.Gaussian.Table.CCL.Request (RequestContract)

/-- The retained actual period programs on the common rational Legendre base fibre.

The unit argument delays construction of the complete prepared cycles until requested. -/
@[expose] def baseFibre (_ : Unit) : Legendre.Periods.Fibre.FibreData
  Curves.Legendre.Crossings.UpperZero.sourceFrame where
  periods := (ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData

/-- The concrete continuations of the retained base period column around the two standard loops and their derived paths.
-/
@[expose] def continuations (_ : Unit) : Legendre.GaussManin.StandardLoops.StandardLoopContinuations
    Curves.Legendre.Loops.One.standardLoops where
  base := baseFibre ()

/-- Continuation around zero is operationally equivalent to the dual matrix [[1, 0], [−2, 1]] on the original period
column. -/
@[expose] def zeroTransport (_ : Unit) : VectorEquivalent (continuations ()).zero
    (Matrix.Operational.Integral.Action.matrixAction Legendre.Monodromy.zeroPeriodMatrix
      (baseFibre ()).rawPeriods) :=
  (continuations ()).zero_explicit

/-- Continuation around one is operationally equivalent to the dual matrix [[1, 2], [0, 1]] on the original period
column. -/
@[expose] def oneTransport (_ : Unit) : VectorEquivalent (continuations ()).one
    (Matrix.Operational.Integral.Action.matrixAction Legendre.Monodromy.onePeriodMatrix
      (baseFibre ()).rawPeriods) :=
  (continuations ()).one_explicit

/-- Continuation around the derived infinity path carries the retained inverse dual product matrix. -/
@[expose] def infinityTransport (_ : Unit) : VectorEquivalent (continuations
  ()).infinity
    (Matrix.Operational.Integral.Action.matrixAction Legendre.Monodromy.infinityPeriodMatrix
      (baseFibre ()).rawPeriods) :=
  (continuations ()).infinity_explicit

/-- Continuation around the concrete product loop returns the original raw base period column operationally. -/
@[expose] def productTransport (_ : Unit) :
    VectorEquivalent (continuations ()).product (baseFibre ()).rawPeriods :=
  (continuations ()).product_identity

/-! ## Caller-bounded finite observations -/

/-- The first A-period entry refined to the supplied positive squared-radius target. -/
@[expose] def baseARefined (target : Fraction.Rational) (positive : 0 < target) :=
  ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).refinedAEntry
    target positive 0 0

/-- The first B-period entry refined to the supplied positive squared-radius target. -/
@[expose] def baseBRefined (target : Fraction.Rational) (positive : 0 < target) :=
  ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).refinedBEntry
    target positive 0 0

/-- The rational Gaussian center returned by the finite A-period request. -/
@[expose] def baseACenter (target : Fraction.Rational) (positive : 0 < target) :=
  ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).aCenter
    target positive 0 0

/-- The rational Gaussian center returned by the finite B-period request. -/
@[expose] def baseBCenter (target : Fraction.Rational) (positive : 0 < target) :=
  ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).bCenter
    target positive 0 0

/-- The certified squared radius returned by the finite A-period request. -/
@[expose] def baseARadiusSq (target : Fraction.Rational) (positive : 0 < target) :=
  ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).aRadiusSq
    target positive 0 0

/-- The certified squared radius returned by the finite B-period request. -/
@[expose] def baseBRadiusSq (target : Fraction.Rational) (positive : 0 < target) :=
  ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).bRadiusSq
    target positive 0 0

/-- The requested A-period squared radius is below the original positive target. -/
theorem baseARadiusSq_lt (target : Fraction.Rational) (positive : 0 < target) :
    baseARadiusSq target positive < target :=
  ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).aRadiusSq_lt_target
    target positive 0 0

/-- The requested B-period squared radius is below the original positive target. -/
theorem baseBRadiusSq_lt (target : Fraction.Rational) (positive : 0 < target) :
    baseBRadiusSq target positive < target :=
  ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).bRadiusSq_lt_target
    target positive 0 0

/-- The bounded A-period request retains its certified enclosure, semantic allowance, persistent output prefix and exact
parser cursor. -/
theorem baseARequest (target : Fraction.Rational) (positive : 0 < target)
    (count : Nat) :
    RequestContract
      ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).table.channels
      (((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).aMatrix 0 0)
      target positive count :=
  ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).aEntry_sharedRequest
    0 0 target positive count

/-- The bounded B-period request retains its certified enclosure, semantic allowance, persistent output prefix and exact
parser cursor. -/
theorem baseBRequest (target : Fraction.Rational) (positive : 0 < target)
    (count : Nat) :
    RequestContract
      ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).table.channels
      (((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).bMatrix 0 0)
      target positive count :=
  ((ExplicitLegendreNormalizedAcquisition.normalized ()).toPeriodData).bEntry_sharedRequest
    0 0 target positive count

end Purelib.Examples.Curves.Legendre.PeriodTransport

end
