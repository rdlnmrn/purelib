module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Topology.Knot.Braid.Word.Basic
public import Purelib.Topology.Knot.Braid.Basic

public import Purelib.Topology.Surface.CellularHomology
meta import Purelib.Elab.Deriving.Repr
import Init.Prelude

open Purelib

open Purelib.Topology.Knot

open Purelib.Topology.Surface

@[expose] public section

/-!
# Locked conventions for finite Legendre transport

The genus-one transport calculation is extremely sensitive to sign and order.
This module fixes those choices as finite data before any monodromy matrix is
introduced.  The executable checks at the end determine path traversal,
reversal, and the sign of the displayed cellular intersection form.
-/

namespace Purelib.Curves.Legendre.Conventions

open Purelib.Topology.Knot.Braid

/-- The chosen positive orientation for a plane. -/
inductive PlaneOrientation
  /-- Counterclockwise traversal is positively oriented. -/ | counterclockwisePositive
  /-- Clockwise traversal is positively oriented. -/ | clockwisePositive
deriving DecidableEq
derive_exposed_repr Purelib.Curves.Legendre.Conventions.PlaneOrientation

/-- The traversal order assigned to a concatenation of two paths. -/
inductive ConcatenationOrder
  /-- Traverse the first path before the second. -/ | firstThenSecond
  /-- Traverse the second path before the first. -/ | secondThenFirst
deriving DecidableEq
derive_exposed_repr Purelib.Curves.Legendre.Conventions.ConcatenationOrder

/-- The traversal order assigned to the head of a braid word. -/
inductive BraidMultiplicationOrder
  /-- The head braid generator acts before the remaining word. -/ | headActsFirst
  /-- The head braid generator acts after the remaining word. -/ | headActsLast
deriving DecidableEq
derive_exposed_repr Purelib.Curves.Legendre.Conventions.BraidMultiplicationOrder

/-- The row or column convention for homology coordinates. -/
inductive HomologyCoordinates
  /-- Homology coordinates are represented as column vectors. -/ | columnVectors
  /-- Homology coordinates are represented as row vectors. -/ | rowVectors
deriving DecidableEq
derive_exposed_repr Purelib.Curves.Legendre.Conventions.HomologyCoordinates

/-- The sign convention for the ordered intersection of the two basis cycles. -/
inductive IntersectionConvention
  /-- The ordered intersection of a with b is positive. -/ | aDotBPositive
  /-- The ordered intersection of b with a is positive. -/ | bDotAPositive
deriving DecidableEq
derive_exposed_repr Purelib.Curves.Legendre.Conventions.IntersectionConvention

/-- The orientation chosen for an adjacent half-twist lift. -/
inductive HalfTwistLift
  /-- Use the positive adjacent half-twist lift. -/ | positiveAdjacentLift
  /-- Use the negative adjacent half-twist lift. -/ | negativeAdjacentLift
deriving DecidableEq
derive_exposed_repr Purelib.Curves.Legendre.Conventions.HalfTwistLift

/-- The branch-label orientation assigned to a vanishing cycle. -/
inductive VanishingOrientation
  /-- Orient the vanishing cycle toward the increasing branch label. -/ | increasingBranchLabel
  /-- Orient the vanishing cycle toward the decreasing branch label. -/ | decreasingBranchLabel
deriving DecidableEq
derive_exposed_repr Purelib.Curves.Legendre.Conventions.VanishingOrientation

set_option genInjectivity false in
/-- The complete convention lock used by the Legendre calculation. -/
structure Convention where
  /-- The positive orientation of the parameter plane. -/ parameterPlane : Curves.Legendre.Conventions.PlaneOrientation
  /-- The positive orientation of the projected branch plane. -/ branchProjection :
    Curves.Legendre.Conventions.PlaneOrientation
  /-- The traversal order of concatenated paths. -/ pathConcatenation : Curves.Legendre.Conventions.ConcatenationOrder
  /-- The order in which listed braid generators act. -/ braidMultiplication :
    Curves.Legendre.Conventions.BraidMultiplicationOrder
  /-- The row or column representation of homology classes. -/ homologyCoordinates :
    Curves.Legendre.Conventions.HomologyCoordinates
  /-- The sign assigned to the ordered basis-cycle intersection. -/ intersectionSign :
    Curves.Legendre.Conventions.IntersectionConvention
  /-- The chosen orientation of an adjacent half-twist lift. -/ halfTwistLift :
    Curves.Legendre.Conventions.HalfTwistLift
  /-- The branch-label orientation of a vanishing cycle. -/ vanishingCycle :
    Curves.Legendre.Conventions.VanishingOrientation
deriving DecidableEq

constructive_injectivity Convention

derive_exposed_repr Purelib.Curves.Legendre.Conventions.Convention

/-- The single convention record consumed by all later Legendre modules. -/
def standard : Curves.Legendre.Conventions.Convention where
  parameterPlane := .counterclockwisePositive
  branchProjection := .counterclockwisePositive
  pathConcatenation := .firstThenSecond
  braidMultiplication := .headActsFirst
  homologyCoordinates := .columnVectors
  intersectionSign := .aDotBPositive
  halfTwistLift := .positiveAdjacentLift
  vanishingCycle := .increasingBranchLabel

/-- The positive crossing of the lower adjacent pair in a three-strand braid. -/
def lowerPositive : Braid.Generator 3 where
  index := 0
  sign := .positive

/-- The positive crossing of the upper adjacent pair in a three-strand braid. -/
def upperPositive : Braid.Generator 3 where
  index := 1
  sign := .positive

/-- With head-first traversal, the lower crossing followed by the upper one sends strand zero to strand two. -/
example :
    (Purelib.Topology.Knot.Braid.Word.permutation ([Curves.Legendre.Conventions.lowerPositive,
      Purelib.Curves.Legendre.Conventions.upperPositive] : Purelib.Topology.Knot.Braid.Word 3)).forward 0 =
      (2 : Fin 3) := rfl

/-- Reversing the displayed path reverses the above strand transport. -/
example :
    (Purelib.Topology.Knot.Braid.Word.permutation
      (Purelib.Topology.Knot.Braid.Word.inverse ([Curves.Legendre.Conventions.lowerPositive,
        Purelib.Curves.Legendre.Conventions.upperPositive] : Purelib.Topology.Knot.Braid.Word 3))).forward 2 =
      (0 : Fin 3) := rfl

/-- List concatenation is path concatenation: the first singleton is traversed before the second singleton. -/
example :
    (Purelib.Topology.Knot.Braid.Word.permutation
      (([Curves.Legendre.Conventions.lowerPositive] : Purelib.Topology.Knot.Braid.Word 3) ++
        [Purelib.Curves.Legendre.Conventions.upperPositive])).forward 0 =
      (2 : Fin 3) := rfl

/-- The locked cellular sign is `a · b = +1`. -/
theorem standard_intersection_sign :
    CellularHomology.intersection
        (CellularHomology.aCycle (0 : Fin 1))
        (CellularHomology.bCycle (0 : Fin 1)) = 1 := by
  have sign := CellularHomology.intersection_a_b (0 : Fin 1) (0 : Fin 1)
  rw [if_pos rfl] at sign
  exact sign

/-- The reverse ordered intersection is consequently negative. -/
theorem standard_reverse_intersection_sign :
    CellularHomology.intersection
        (CellularHomology.bCycle (0 : Fin 1))
        (CellularHomology.aCycle (0 : Fin 1)) = -1 := by
  have sign := CellularHomology.intersection_b_a (0 : Fin 1) (0 : Fin 1)
  rw [if_pos rfl] at sign
  exact sign

end Purelib.Curves.Legendre.Conventions
