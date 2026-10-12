module
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
public import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Integration.Algebraic.SquareFactor

open Purelib.Polynomial.Dense.Gaussian

@[expose] public section

/-!
Kernel tests of the actual raw-coefficient reduction, cancellation, and
uniform finite-path clearance constructors.  These do not execute numerical
period observations and are not a substitute for the paused Legendre runs.
-/

namespace Test.Integration.Algebraic.SquareFactor.Transport

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput (Segment)

/-- Classify the prepared square-factor weight at one exact Gaussian point for the finite regression table.

The tags distinguish preparation failure, regularity, a removed coordinate zero, a weight pole and a branch point. -/
private def pointTag (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
    (point : SquareFactor.Gaussian) : Nat :=
  match SquareFactor.prepare polynomial request with
  | .error _ => 0
  | .ok prepared =>
      match prepared.weight.checkPoint point with
      | .regular .. => 1
      | .removedCoordinateZero .. => 2
      | .weightPole .. => 3
      | .branchPoint .. => 4

open Test.Integration.Algebraic.SquareFactor.Transport in
/-- `p=x²(x+1)`: the original `dx/y` has weight proportional to `1/x`, whereas `x dx/y` has a nonzero constant weight.
The computed factors need not be monic. Neither a cancelled zero nor a normalized request is misreported as a pole of
the weight. -/
theorem cancellation_precedes_pole_tests :
    let pointTag (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
        (point : SquareFactor.Gaussian) : Nat :=
      match SquareFactor.prepare polynomial request with
      | .error _ => 0
      | .ok prepared =>
          match prepared.weight.checkPoint point with
          | .regular .. => 1
          | .removedCoordinateZero .. => 2
          | .weightPole .. => 3
          | .branchPoint .. => 4
    pointTag ⟨[1, 1, 0, 0]⟩ (.original 0) 0 = 3 ∧
      pointTag ⟨[1, 1, 0, 0]⟩ (.original 1) 0 = 2 ∧
      pointTag ⟨[1, 1, 0, 0]⟩ (.normalized 0) 0 = 2 ∧
      pointTag ⟨[1, 1, 0, 0]⟩ (.original 0) (-1) = 4 := by
  decide +kernel

/-- Read the finite segment-preparation outcome together with presence of original-coordinate clearance.

The result distinguishes acceptance, the two endpoint obstructions and an inconclusive finite cover. -/
private def pathTag (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
    (segment : PathInput.Segment) : Nat × Bool :=
  match PathInput.prepare polynomial request segment with
  | .error _ => (0, false)
  | .ok prepared =>
      let original := prepared.data.originalDomain?.isSome
      match prepared.outcome with
      | .accepted _ => (1, original)
      | .endpointObstruction _ (.weightPole ..) => (2, original)
      | .endpointObstruction _ (.branchPoint ..) => (3, original)
      | .inconclusive _ => (4, original)

section
open Test.Integration.Algebraic.SquareFactor.Transport
/-- Genuine repeated-factor input accepted on both orientations of the same nonconstant segment, with generated
original-coordinate clearance. -/
theorem repeated_factor_original_path_accepted :
    let pathTag (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
        (segment : PathInput.Segment) : Nat × Bool :=
      match PathInput.prepare polynomial request segment with
      | .error _ => (0, false)
      | .ok prepared =>
          let original := prepared.data.originalDomain?.isSome
          match prepared.outcome with
          | .accepted _ => (1, original)
          | .endpointObstruction _ (.weightPole ..) => (2, original)
          | .endpointObstruction _ (.branchPoint ..) => (3, original)
          | .inconclusive _ => (4, original)
    pathTag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨2, ⟨9/4, 0⟩⟩ = (1, true) ∧
      pathTag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨⟨9/4, 0⟩, 2⟩ = (1, true) := by
  decide +kernel

/-- Cancellation admits the reduced extension, explicitly without claiming that the original `0/0` coordinate expression
is defined at the endpoint. -/
theorem removed_coordinate_extension_is_distinct :
    let pathTag (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
        (segment : PathInput.Segment) : Nat × Bool :=
      match PathInput.prepare polynomial request segment with
      | .error _ => (0, false)
      | .ok prepared =>
          let original := prepared.data.originalDomain?.isSome
          match prepared.outcome with
          | .accepted _ => (1, original)
          | .endpointObstruction _ (.weightPole ..) => (2, original)
          | .endpointObstruction _ (.branchPoint ..) => (3, original)
          | .inconclusive _ => (4, original)
    pathTag ⟨[1, 1, 0, 0]⟩ (.original 1) ⟨0, ⟨1/4, 0⟩⟩ = (1, false) ∧
      pathTag ⟨[1, 1, 0, 0]⟩ (.normalized 0) ⟨0, ⟨1/4, 0⟩⟩ = (1, false) := by
  decide +kernel

/-- The repeated-factor test polynomial reports an actual weight pole at zero and a branch point at negative one. -/
theorem exact_endpoint_obstructions :
    let pathTag (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
        (segment : PathInput.Segment) : Nat × Bool :=
      match PathInput.prepare polynomial request segment with
      | .error _ => (0, false)
      | .ok prepared =>
          let original := prepared.data.originalDomain?.isSome
          match prepared.outcome with
          | .accepted _ => (1, original)
          | .endpointObstruction _ (.weightPole ..) => (2, original)
          | .endpointObstruction _ (.branchPoint ..) => (3, original)
          | .inconclusive _ => (4, original)
    (pathTag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨0, ⟨1/4, 0⟩⟩).1 = 2 ∧
      (pathTag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨-1, ⟨-3/4, 0⟩⟩).1 = 3 := by
  decide +kernel

/-- The sign-aware enclosure now certifies the wide pole-free segment that the previous sample/variation margin could
not certify, in both orientations. -/
theorem wide_repeated_factor_path_accepted :
    let pathTag (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
        (segment : PathInput.Segment) : Nat × Bool :=
      match PathInput.prepare polynomial request segment with
      | .error _ => (0, false)
      | .ok prepared =>
          let original := prepared.data.originalDomain?.isSome
          match prepared.outcome with
          | .accepted _ => (1, original)
          | .endpointObstruction _ (.weightPole ..) => (2, original)
          | .endpointObstruction _ (.branchPoint ..) => (3, original)
          | .inconclusive _ => (4, original)
    pathTag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨2, 100⟩ = (1, true) ∧
      pathTag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨100, 2⟩ = (1, true) := by
  constructor <;> decide +kernel

end

/-- Keep the old whole-path proposal's failure as an explicit low-level diagnostic, not the outcome of the improved
public constructor. -/
theorem coarse_quadratic_margin_is_still_inconclusive :
    (Path.Bounds.Basic.prepareCoarse ⟨[1, 0, 1]⟩ (-2) 4
      PathInput.unitInterval).lowerBound = 0 := by
  decide +kernel

section
open Test.Integration.Algebraic.SquareFactor.Transport
/-- The generated completing-square certificate resolves the old interval dependency failure on the unchanged path and
on its reversal. -/
theorem quadratic_dependency_is_resolved :
    let pathTag (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
        (segment : PathInput.Segment) : Nat × Bool :=
      match PathInput.prepare polynomial request segment with
      | .error _ => (0, false)
      | .ok prepared =>
          let original := prepared.data.originalDomain?.isSome
          match prepared.outcome with
          | .accepted _ => (1, original)
          | .endpointObstruction _ (.weightPole ..) => (2, original)
          | .endpointObstruction _ (.branchPoint ..) => (3, original)
          | .inconclusive _ => (4, original)
    pathTag ⟨[1, 0, 1]⟩ (.original 0) ⟨-2, 2⟩ = (1, true) ∧
      pathTag ⟨[1, 0, 1]⟩ (.original 0) ⟨2, -2⟩ = (1, true) := by
  constructor <;> decide +kernel

/-- Interior irrational branch locations need not be found by an exact endpoint test. An unresolved cover does not
fabricate an endpoint pole. -/
theorem unresolved_cover_remains_inconclusive :
    let pathTag (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
        (segment : PathInput.Segment) : Nat × Bool :=
      match PathInput.prepare polynomial request segment with
      | .error _ => (0, false)
      | .ok prepared =>
          let original := prepared.data.originalDomain?.isSome
          match prepared.outcome with
          | .accepted _ => (1, original)
          | .endpointObstruction _ (.weightPole ..) => (2, original)
          | .endpointObstruction _ (.branchPoint ..) => (3, original)
          | .inconclusive _ => (4, original)
    (pathTag ⟨[1, 0, -2]⟩ (.original 0) ⟨-2, 2⟩).1 = 4 := by
  decide +kernel

/-- The same segment interface handles reduced constant radicands and rejects the zero input polynomial. -/
theorem constant_radicands_use_the_path_interface :
    let pathTag (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
        (segment : PathInput.Segment) : Nat × Bool :=
      match PathInput.prepare polynomial request segment with
      | .error _ => (0, false)
      | .ok prepared =>
          let original := prepared.data.originalDomain?.isSome
          match prepared.outcome with
          | .accepted _ => (1, original)
          | .endpointObstruction _ (.weightPole ..) => (2, original)
          | .endpointObstruction _ (.branchPoint ..) => (3, original)
          | .inconclusive _ => (4, original)
    pathTag ⟨[1, 0, 0]⟩ (.original 0) ⟨2, ⟨9/4, 0⟩⟩ = (1, true) ∧
      pathTag ⟨[1, 0, 0]⟩ (.original 1) ⟨0, 1⟩ = (1, false) ∧
      pathTag ⟨[2]⟩ (.original 0) ⟨0, 1⟩ = (1, true) ∧
      pathTag ⟨[0]⟩ (.original 0) ⟨0, 1⟩ = (0, false) := by
  decide +kernel

end

/-- Evaluate the prepared weight and transported original coordinate when the supplied exact root squares to the reduced
radicand.

Preparation failure or an incorrect root produces no value; a successful result retains the computed square factor and
its actual scale. -/
private def transportedValue (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
    (point root : SquareFactor.Gaussian) : Option (SquareFactor.Gaussian × SquareFactor.Gaussian) :=
  match SquareFactor.prepare polynomial request with
  | .error _ => none
  | .ok prepared =>
      if root ^ 2 = prepared.reduction.radicand.eval point then
        some (prepared.weight.coefficient point root,
          SquareFactor.coordinate prepared.reduction point root)
      else none

open Test.Integration.Algebraic.SquareFactor.Transport in
/-- The actual factorization retains `s=-2x/9`, `q=81(x+1)/4`. At `x=3`, choose `z=-9`, hence `y=6`. Original `dx/y` is
`1/6`, whereas normalized `dx/z` is `-1/9`. No monic-factor or scalar-square-root convention is silently imposed on the
computed factorization. -/
theorem original_and_normalized_are_not_confused :
    let transportedValue (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
        (point root : SquareFactor.Gaussian) : Option (SquareFactor.Gaussian × SquareFactor.Gaussian) :=
      match SquareFactor.prepare polynomial request with
      | .error _ => none
      | .ok prepared =>
          if root ^ 2 = prepared.reduction.radicand.eval point then
            some (prepared.weight.coefficient point root,
              SquareFactor.coordinate prepared.reduction point root)
          else none
    transportedValue ⟨[1, 1, 0, 0]⟩ (.original 0) 3 (-9) = some (⟨1/6, 0⟩, 6) ∧
      transportedValue ⟨[1, 1, 0, 0]⟩ (.normalized 0) 3 (-9) = some (⟨-1/9, 0⟩, 6) ∧
      transportedValue ⟨[1, 1, 0, 0]⟩ (.original 0) 3 9 = some (⟨-1/6, 0⟩, -6) := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

end Test.Integration.Algebraic.SquareFactor.Transport
