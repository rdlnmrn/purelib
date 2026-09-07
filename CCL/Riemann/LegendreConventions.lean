import CCL.Knot.FiniteBraid
import CCL.Riemann.CellularHomology

/-!
# Locked conventions for finite Legendre transport

The genus-one transport calculation is extremely sensitive to sign and order.
This module fixes those choices as finite data before any monodromy matrix is
introduced.  The executable checks at the end determine path traversal,
reversal, and the sign of the displayed cellular intersection form.
-/

namespace CCL.Riemann.LegendreConventions

open CCL.Knot.FiniteBraid

inductive PlaneOrientation
  | counterclockwisePositive
  | clockwisePositive
deriving DecidableEq, Repr

inductive ConcatenationOrder
  | firstThenSecond
  | secondThenFirst
deriving DecidableEq, Repr

inductive BraidMultiplicationOrder
  | headActsFirst
  | headActsLast
deriving DecidableEq, Repr

inductive HomologyCoordinates
  | columnVectors
  | rowVectors
deriving DecidableEq, Repr

inductive IntersectionConvention
  | aDotBPositive
  | bDotAPositive
deriving DecidableEq, Repr

inductive HalfTwistLift
  | positiveAdjacentLift
  | negativeAdjacentLift
deriving DecidableEq, Repr

inductive VanishingOrientation
  | increasingBranchLabel
  | decreasingBranchLabel
deriving DecidableEq, Repr

/-- The complete convention lock used by the Legendre calculation. -/
structure Convention where
  parameterPlane : PlaneOrientation
  branchProjection : PlaneOrientation
  pathConcatenation : ConcatenationOrder
  braidMultiplication : BraidMultiplicationOrder
  homologyCoordinates : HomologyCoordinates
  intersectionSign : IntersectionConvention
  halfTwistLift : HalfTwistLift
  vanishingCycle : VanishingOrientation
deriving DecidableEq, Repr

/-- The single convention record consumed by all later Legendre modules. -/
def standard : Convention where
  parameterPlane := .counterclockwisePositive
  branchProjection := .counterclockwisePositive
  pathConcatenation := .firstThenSecond
  braidMultiplication := .headActsFirst
  homologyCoordinates := .columnVectors
  intersectionSign := .aDotBPositive
  halfTwistLift := .positiveAdjacentLift
  vanishingCycle := .increasingBranchLabel

def lowerPositive : Generator 3 where
  index := 0
  sign := .positive

def upperPositive : Generator 3 where
  index := 1
  sign := .positive

/-- With head-first traversal, the lower crossing followed by the upper one
sends strand zero to strand two. -/
example :
    (Word.permutation ([lowerPositive, upperPositive] : Word 3)).forward 0 =
      (2 : Fin 3) := rfl

/-- Reversing the displayed path reverses the above strand transport. -/
example :
    (Word.permutation
      (Word.inverse ([lowerPositive, upperPositive] : Word 3))).forward 2 =
      (0 : Fin 3) := rfl

/-- List concatenation is path concatenation: the first singleton is
traversed before the second singleton. -/
example :
    (Word.permutation
      (([lowerPositive] : Word 3) ++ [upperPositive])).forward 0 =
      (2 : Fin 3) := rfl

/-- The locked cellular sign is `a · b = +1`. -/
theorem standard_intersection_sign :
    CCL.Riemann.CellularHomology.intersection
        (CCL.Riemann.CellularHomology.aCycle (0 : Fin 1))
        (CCL.Riemann.CellularHomology.bCycle (0 : Fin 1)) = 1 := by
  simpa using
    CCL.Riemann.CellularHomology.intersection_a_b
      (0 : Fin 1) (0 : Fin 1)

/-- The reverse ordered intersection is consequently negative. -/
theorem standard_reverse_intersection_sign :
    CCL.Riemann.CellularHomology.intersection
        (CCL.Riemann.CellularHomology.bCycle (0 : Fin 1))
        (CCL.Riemann.CellularHomology.aCycle (0 : Fin 1)) = -1 := by
  simpa using
    CCL.Riemann.CellularHomology.intersection_b_a
      (0 : Fin 1) (0 : Fin 1)

end CCL.Riemann.LegendreConventions
