import CCL.Riemann.ExplicitLegendrePreparedPeriods
import CCL.Riemann.ExplicitLegendreOneLoop

/-!
# Concrete raw period transport for the rational Legendre loops

The explicit standard loops and explicit base-fibre branch tracks are joined
here without asserting an equality between periods on different fibres.
Closed-loop continuation evaluates the actual base period programs on the
transported homology basis, hence uses the transpose of the certified braid
matrix.  All displayed period observations remain caller-bounded finite
requests.
-/

namespace CCL.Riemann.ExplicitLegendrePeriodTransport

open CCL.Riemann.LegendreGaussManin
open CCL.Riemann.PeriodMatrix

abbrev Coordinate := RFAP.ConstructiveFraction.Rational

/-- Actual finite period programs on the common rational base fibre.  The
unit token prevents compiled clients from constructing the complete prepared
cycles merely by importing this module. -/
def baseFibre (_ : Unit) : FibreData
  CCL.Riemann.ExplicitLegendreSegment.sourceFrame where
  periods := CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()

/-- Concrete continuation of the displayed period column around both
standard loops and their derived infinity/product paths. -/
def continuations (_ : Unit) : StandardLoopContinuations
    CCL.Riemann.ExplicitLegendreOneLoop.standardLoops where
  base := baseFibre ()

/-- Around zero, the actual period column carries the exact dual matrix
`[[1,0],[-2,1]]`. -/
def zeroTransport (_ : Unit) : VectorEquivalent (continuations ()).zero
    (matrixAction CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix
      (baseFibre ()).rawPeriods) :=
  (continuations ()).zero_explicit

/-- Around one, the actual period column carries the exact dual matrix
`[[1,2],[0,1]]`. -/
def oneTransport (_ : Unit) : VectorEquivalent (continuations ()).one
    (matrixAction CCL.Riemann.LegendreMonodromy.onePeriodMatrix
      (baseFibre ()).rawPeriods) :=
  (continuations ()).one_explicit

/-- The derived infinity path carries the inverse dual product matrix. -/
def infinityTransport (_ : Unit) : VectorEquivalent (continuations ()).infinity
    (matrixAction CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
      (baseFibre ()).rawPeriods) :=
  (continuations ()).infinity_explicit

/-- The concrete product loop returns the raw base period column
operationally. -/
def productTransport (_ : Unit) :
    VectorEquivalent (continuations ()).product (baseFibre ()).rawPeriods :=
  (continuations ()).product_identity

/-! ## Caller-bounded finite observations -/

def baseARefined (target : Coordinate) (positive : 0 < target) :=
  (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).refinedAEntry
    target positive 0 0

def baseBRefined (target : Coordinate) (positive : 0 < target) :=
  (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).refinedBEntry
    target positive 0 0

/-- Rational centre returned for the concrete A-period at one chosen finite
request. -/
def baseACenter (target : Coordinate) (positive : 0 < target) :=
  (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).aCenter
    target positive 0 0

/-- Rational centre returned for the concrete B-period at the same form of
finite request. -/
def baseBCenter (target : Coordinate) (positive : 0 < target) :=
  (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).bCenter
    target positive 0 0

def baseARadiusSq (target : Coordinate) (positive : 0 < target) :=
  (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).aRadiusSq
    target positive 0 0

def baseBRadiusSq (target : Coordinate) (positive : 0 < target) :=
  (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).bRadiusSq
    target positive 0 0

theorem baseARadiusSq_lt (target : Coordinate) (positive : 0 < target) :
    baseARadiusSq target positive < target :=
  (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).aRadiusSq_lt_target
    target positive 0 0

theorem baseBRadiusSq_lt (target : Coordinate) (positive : 0 < target) :
    baseBRadiusSq target positive < target :=
  (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).bRadiusSq_lt_target
    target positive 0 0

/-- The A-period request returns its certified enclosure, semantic allowance,
persistent output prefix, and exact parser cursor. -/
theorem baseARequest (target : Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract
      (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).table.channels
      ((CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).aMatrix 0 0)
      target positive count :=
  (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).aEntry_sharedRequest
    0 0 target positive count

/-- The parallel finite request for the concrete B-period. -/
theorem baseBRequest (target : Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract
      (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).table.channels
      ((CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).bMatrix 0 0)
      target positive count :=
  (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodData ()).bEntry_sharedRequest
    0 0 target positive count

end CCL.Riemann.ExplicitLegendrePeriodTransport
