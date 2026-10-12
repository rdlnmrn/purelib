module

meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Rational.SquareRoot.Radius.Scaled
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
public import Purelib.Polynomial.Geometry.PolynomialPathDiagnostics
import Purelib.Elab.Deriving.Repr
public import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Prepare
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

public section

/-!
# Checked finite paths for square-factor differential transport

This input layer retains the requested segment, cancels the rational weight,
and generates uniform denominator and radicand clearances.  A positive test
is evidence for every rational parameter on that segment, not just its ends.
A failed margin is explicitly inconclusive.  Exact endpoint obstructions are
reported separately and never used to claim divergence of an integral.

The accepted reduced expression can extend across removed coordinate zeros.
`originalDomain?` separately tests whether the original coordinate is uniformly
nonzero; without that extra successful test, transport is asserted only at
the points where the original quotient is defined.  No cycle is rerouted.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.PathInput

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- The rational carrier for segment parameters and certified path bounds. -/
abbrev Coordinate := Fraction.Rational
/-- The rational closed-interval carrier for path parameters. -/
abbrev Interval := Data.Rat.Interval.Bounds

/-- The retained closed rational interval from zero to one. -/
@[expose] def unitInterval : Interval := ⟨0, 1, by decide⟩

open Purelib.Curves.Hyperelliptic.Differentials in
set_option genInjectivity false in
/-- An oriented Gaussian segment specified by its original starting and finishing points. -/
structure Segment where
  /-- The original oriented segment start. -/ start : SquareFactor.Gaussian
  /-- The original oriented segment finish. -/ finish : SquareFactor.Gaussian
deriving DecidableEq

constructive_injectivity Segment

open Purelib in
/-- The exact finish-minus-start displacement of the retained segment. -/
@[expose] def Segment.direction (segment : Integration.Algebraic.SquareFactor.PathInput.Segment) : Gaussian :=
  segment.finish - segment.start

open Purelib in
open Purelib.Geometry.Rational in
/-- Evaluate the original segment's affine parameterization at the supplied rational parameter. -/
@[expose] def Segment.point (segment : Integration.Algebraic.SquareFactor.PathInput.Segment) (parameter :
  Integration.Algebraic.SquareFactor.PathInput.Coordinate) : Gaussian :=
  Affine.line segment.start segment.direction parameter

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Gaussian
/-- Parameter zero reads the original segment start. -/
theorem Segment.point_zero (segment : Integration.Algebraic.SquareFactor.PathInput.Segment) : segment.point 0 =
  segment.start := by
  change segment.start + (0 : SquareFactor.Gaussian) * segment.direction = segment.start
  rw [Basic.zero_mul, Basic.add_zero]

/-- Parameter one reads the original segment finish. -/
theorem Segment.point_one (segment : Integration.Algebraic.SquareFactor.PathInput.Segment) : segment.point 1 =
  segment.finish := by
  change segment.start + (1 : SquareFactor.Gaussian) * (segment.finish - segment.start) = segment.finish
  rw [Basic.one_mul]
  ring1

end

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- Polynomial value and movement bounds along the exact original segment on the unit interval. -/
abbrev Bounds (polynomial : SquareFactor.GaussianPolynomial) (segment :
  Integration.Algebraic.SquareFactor.PathInput.Segment) :=
  Polynomial.Dense.Gaussian.Path.Bounds.Basic.Data polynomial segment.start segment.direction
    Integration.Algebraic.SquareFactor.PathInput.unitInterval

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic.Differentials in
set_option genInjectivity false in
/-- Retained numerator, denominator, radicand and square-factor bounds along one prepared segment.

The root norm floor is cached with its exact maximum formula, keeping the three radicand lower estimates distinct. -/
structure Data {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
    (prepared : SquareFactor.Prepared polynomial request) (segment :
      Integration.Algebraic.SquareFactor.PathInput.Segment) where
  /-- The retained numerator polynomial bounds on this exact segment. -/ numerator :
    Integration.Algebraic.SquareFactor.PathInput.Bounds prepared.weight.numerator segment
  /-- The retained denominator polynomial bounds on this exact segment. -/ denominator :
    Integration.Algebraic.SquareFactor.PathInput.Bounds prepared.weight.denominator segment
  /-- The retained radicand polynomial bounds on this exact segment. -/ radicand :
    Integration.Algebraic.SquareFactor.PathInput.Bounds prepared.reduction.radicand segment
  /-- The retained square-factor polynomial bounds on the same segment. -/ squareFactor :
    Integration.Algebraic.SquareFactor.PathInput.Bounds prepared.reduction.squareFactor segment
  /-- The cached rational lower estimate for admissible root squared norms. -/ rootNormFloor :
    Integration.Algebraic.SquareFactor.PathInput.Coordinate
  /-- The floor equals the maximum of the baseline, scaled-radius and coordinate lower estimates. -/ rootNormFloor_eq :
    rootNormFloor = max (max (min 1 (radicand.lowerBound / 4))
    (SquareRoot.Radius.Scaled.radius (radicand.lowerBound / 2) / 2)) (radicand.coordinateLower / 2)

constructive_injectivity Data

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic.Differentials in
set_option backward.match.sparseCases false in
/-- Prepare coarse polynomial bounds, then sharpen the allowed denominator, radicand and square-factor bounds.

Endpoint poles and branch points block sharpening. Removed coordinate zeros also block it when the original domain is
required; the square factor is sharpened only for that original-domain request. -/
@[expose] def prepareData {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
    (prepared : SquareFactor.Prepared polynomial request) (segment :
      Integration.Algebraic.SquareFactor.PathInput.Segment)
    (requireOriginal : Bool := true) : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment :=
  let numerator : Integration.Algebraic.SquareFactor.PathInput.Bounds prepared.weight.numerator segment :=
    Polynomial.Dense.Gaussian.Path.Bounds.Basic.prepareCoarse _ _ _ _
  let denominator : Integration.Algebraic.SquareFactor.PathInput.Bounds prepared.weight.denominator segment :=
    Polynomial.Dense.Gaussian.Path.Bounds.Basic.prepareCoarse _ _ _ _
  let radicand : Integration.Algebraic.SquareFactor.PathInput.Bounds prepared.reduction.radicand segment :=
    Polynomial.Dense.Gaussian.Path.Bounds.Basic.prepareCoarse _ _ _ _
  let squareFactor : Integration.Algebraic.SquareFactor.PathInput.Bounds prepared.reduction.squareFactor segment :=
    Polynomial.Dense.Gaussian.Path.Bounds.Basic.prepareCoarse _ _ _ _
  let obstructed :=
    match prepared.weight.checkPoint segment.start, prepared.weight.checkPoint segment.finish with
    | .weightPole .., _ | .branchPoint .., _ | _, .weightPole .. | _, .branchPoint .. => true
    | .removedCoordinateZero .., _ | _, .removedCoordinateZero .. => requireOriginal
    | _, _ => false
  let denominator := if obstructed then denominator else denominator.sharpen
  let radicand := if obstructed then radicand else radicand.sharpen
  let squareFactor := if obstructed || !requireOriginal then squareFactor else squareFactor.sharpen
  { numerator
    denominator
    radicand
    squareFactor
    rootNormFloor := max (max (min 1 (radicand.lowerBound / 4))
      (SquareRoot.Radius.Scaled.radius (radicand.lowerBound / 2) / 2)) (radicand.coordinateLower / 2)
    rootNormFloor_eq := rfl }

namespace Data

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}

open Purelib in
/-- Positive retained denominator and radicand margins along the exact prepared segment. -/
structure Safe (data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment) : Type where
  /-- The retained denominator lower bound is strictly positive. -/ denominatorPositive : 0 <
    data.denominator.lowerBound
  /-- The retained radicand lower bound is strictly positive. -/ radicandPositive : 0 < data.radicand.lowerBound

section
open Purelib
/-- A certified positive denominator margin excludes a denominator zero at every retained in-range parameter. -/
theorem Safe.denominator_nonzero {data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment} (safe :
  data.Safe)
    {parameter : Integration.Algebraic.SquareFactor.PathInput.Coordinate} (inside :
      Integration.Algebraic.SquareFactor.PathInput.unitInterval.Contains parameter) :
    prepared.weight.denominator.eval (segment.point parameter) ≠ 0 :=
  data.denominator.eval_nonzero safe.denominatorPositive inside

/-- A certified positive radicand margin excludes a radicand zero at every retained in-range parameter. -/
theorem Safe.radicand_nonzero {data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment} (safe :
  data.Safe)
    {parameter : Integration.Algebraic.SquareFactor.PathInput.Coordinate} (inside :
      Integration.Algebraic.SquareFactor.PathInput.unitInterval.Contains parameter) :
    prepared.reduction.radicand.eval (segment.point parameter) ≠ 0 :=
  data.radicand.eval_nonzero safe.radicandPositive inside

end

open Purelib in
/-- Return the checked positive square-factor margin when the retained bounds establish it.

A missing result records only failure of this margin test, without asserting an original-domain obstruction. -/
@[expose] def originalDomain? (data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment) :
    Option (PLift (0 < data.squareFactor.lowerBound)) :=
  if positive : 0 < data.squareFactor.lowerBound then some ⟨positive⟩ else none

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- A positive original square-factor margin identifies the reduced coefficient with the original differential
coefficient.

The parameter remains inside the same segment and the supplied root is retained with its nonzero certificate. -/
theorem coefficient_transport (data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment)
    (originalDomain : 0 < data.squareFactor.lowerBound)
    {parameter : Integration.Algebraic.SquareFactor.PathInput.Coordinate} (inside :
      Integration.Algebraic.SquareFactor.PathInput.unitInterval.Contains parameter)
    (root : SquareFactor.Gaussian) (rootNonzero : root ≠ 0) :
    prepared.weight.coefficient (segment.point parameter) root =
      request.originalNumerator prepared.reduction (segment.point parameter) /
        SquareFactor.coordinate prepared.reduction (segment.point parameter) root :=
  prepared.weight.coefficient_transport _ root
    (data.squareFactor.eval_nonzero originalDomain inside) rootNonzero

/-- The initial or terminal endpoint of the exact segment. -/
inductive Endpoint where
  /-- Select the original segment starting endpoint. -/ | start
  /-- Select the original segment finishing endpoint. -/ | finish
deriving DecidableEq

derive_exposed_repr Purelib.Integration.Algebraic.SquareFactor.PathInput.Data.Endpoint

open Purelib in
/-- Read zero for the starting endpoint and one for the finishing endpoint. -/
@[expose] def Endpoint.parameter : Integration.Algebraic.SquareFactor.PathInput.Data.Endpoint →
  Integration.Algebraic.SquareFactor.PathInput.Coordinate
  | .start => 0
  | .finish => 1

section
open Purelib
/-- A certified weight pole or branch-point zero at one retained segment endpoint.

A weight pole retains both denominator vanishing and numerator nonvanishing; a branch obstruction retains the exact
radicand zero. -/
inductive EndpointObstruction (data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment) (endpoint :
  Integration.Algebraic.SquareFactor.PathInput.Data.Endpoint) : Type where
  /-- The original endpoint denominator vanishes while its numerator is nonzero. -/ | weightPole
      (zero : prepared.weight.denominator.eval (segment.point endpoint.parameter) = 0)
      (numeratorNonzero : prepared.weight.numerator.eval (segment.point endpoint.parameter) ≠ 0)
  /-- The original endpoint radicand vanishes. -/ | branchPoint (zero : prepared.reduction.radicand.eval (segment.point
    endpoint.parameter) = 0)

/-- Check the exact endpoint for a certified weight pole or radicand branch point.

Regular and removed-coordinate-zero outcomes return no such obstruction; absence is not a whole-segment safety
certificate. -/
@[expose] def endpointObstruction? (data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment) (endpoint
  : Integration.Algebraic.SquareFactor.PathInput.Data.Endpoint) :
    Option (data.EndpointObstruction endpoint) :=
  match prepared.weight.checkPoint (segment.point endpoint.parameter) with
  | .weightPole zero nonzero => some (.weightPole zero nonzero)
  | .branchPoint _ zero => some (.branchPoint zero)
  | .regular .. | .removedCoordinateZero .. => none

end

open Purelib in
set_option genInjectivity false in
/-- An inconclusive denominator or radicand margin certificate indexed by the retained path data.

A radicand failure also retains the already established positive denominator margin. -/
inductive MarginFailure (data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment) : Type where
  /-- The retained denominator margin check is inconclusive, with its original bound certificate. -/ | denominator
    (certificate : data.denominator.Inconclusive)
  /-- The denominator margin is positive but the retained radicand margin check is inconclusive. -/ | radicand
    (denominatorPositive : 0 < data.denominator.lowerBound)
      (certificate : data.radicand.Inconclusive)

constructive_injectivity MarginFailure

open Purelib in
set_option genInjectivity false in
/-- A certified safe path, an explicit endpoint obstruction, or an inconclusive retained margin check. -/
inductive Outcome (data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment) : Type where
  /-- The retained denominator and radicand margins certify safety. -/ | accepted (safe : data.Safe)
  /-- The selected original endpoint carries a checked pole or branch-point obstruction. -/ | endpointObstruction
    (endpoint : Integration.Algebraic.SquareFactor.PathInput.Data.Endpoint) (obstruction : data.EndpointObstruction
    endpoint)
  /-- The retained path bounds carry a specific unresolved margin certificate. -/ | inconclusive (failure :
    data.MarginFailure)

constructive_injectivity Outcome

section
open Purelib
/-- Check the retained positive margins, then inspect endpoints before returning a certified obstruction or inconclusive
margin failure.

The starting endpoint takes precedence when both endpoints are obstructed, and the denominator failure is retained when
its margin is not positive. -/
@[expose] def check (data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment) : data.Outcome :=
  if denominatorPositive : 0 < data.denominator.lowerBound then
    if radicandPositive : 0 < data.radicand.lowerBound then
      .accepted ⟨denominatorPositive, radicandPositive⟩
    else
      match data.endpointObstruction? .start, data.endpointObstruction? .finish with
      | some obstruction, _ => .endpointObstruction .start obstruction
      | _, some obstruction => .endpointObstruction .finish obstruction
      | none, none => .inconclusive (.radicand denominatorPositive
          (data.radicand.inconclusiveCertificate (le_of_not_gt radicandPositive)))
  else
    match data.endpointObstruction? .start, data.endpointObstruction? .finish with
    | some obstruction, _ => .endpointObstruction .start obstruction
    | _, some obstruction => .endpointObstruction .finish obstruction
    | none, none => .inconclusive (.denominator
        (data.denominator.inconclusiveCertificate (le_of_not_gt denominatorPositive)))

/-- Retained safety certificates force the exact checker result to be accepted. -/
theorem check_complete (data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment) (safe : data.Safe) :
    data.check = .accepted safe := by
  rw [Integration.Algebraic.SquareFactor.PathInput.Data.check, dif_pos safe.denominatorPositive, dif_pos
    safe.radicandPositive]

end

open Purelib in
/-- A safe retained path cannot have either certified endpoint obstruction. -/
theorem Safe.excludes_endpointObstruction {data : Integration.Algebraic.SquareFactor.PathInput.Data prepared segment}
  (safe : data.Safe)
    (endpoint : Integration.Algebraic.SquareFactor.PathInput.Data.Endpoint) (obstruction : data.EndpointObstruction
      endpoint) : False := by
  have inside : Integration.Algebraic.SquareFactor.PathInput.unitInterval.Contains endpoint.parameter := by
    cases endpoint <;> exact ⟨by decide, by decide⟩
  cases obstruction with
  | weightPole zero _ => exact safe.denominator_nonzero inside zero
  | branchPoint zero => exact safe.radicand_nonzero inside zero

end Data

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
set_option genInjectivity false in
/-- The exact square-factor preparation, its retained segment bounds and the outcome of checking those bounds. -/
structure PreparedPath (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request) (segment :
  Integration.Algebraic.SquareFactor.PathInput.Segment) where
  /-- The original square-factor differential preparation. -/ prepared : SquareFactor.Prepared polynomial request
  /-- The retained bounds indexed by that exact preparation and segment. -/ data :
    Integration.Algebraic.SquareFactor.PathInput.Data prepared segment
  /-- The checked safety, obstruction or inconclusive outcome for those exact bounds. -/ outcome : data.Outcome

constructive_injectivity PreparedPath

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- Prepare the square-factor reduction and segment bounds, retaining the complete checked path outcome.

A zero input polynomial returns its checked zero certificate. Successful algebraic preparation retains either safety,
endpoint obstruction or an inconclusive margin result. -/
@[expose] def prepare (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request) (segment :
  Integration.Algebraic.SquareFactor.PathInput.Segment) :
    Except (PLift (polynomial.isZero = true)) (Integration.Algebraic.SquareFactor.PathInput.PreparedPath polynomial
      request segment) :=
  match SquareFactor.prepare polynomial request with
  | .error zero => .error zero
  | .ok prepared =>
      let data := Integration.Algebraic.SquareFactor.PathInput.prepareData prepared segment
      .ok ⟨prepared, data, data.check⟩

end Purelib.Integration.Algebraic.SquareFactor.PathInput
