module
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
import Purelib.Integration.Algebraic.SquareFactor.PathInput
public import Purelib.Integration.Algebraic.SquareFactor.Accuracy
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Data.Rat

open Purelib.Integration.Algebraic.SquareFactor

@[expose] public section

/-!
Kernel regressions of the coefficient-generated numerical requests.  These
execute reduction, clearance, scale calculation and the bounded depth scan,
but deliberately do not execute a complete root continuation.  They are not
the repeated-factor observation or the paused Legendre acceptance runs.
-/

namespace Test.Riemann.SquareFactorAccuracyTests

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Riemann.Integration

/-- The exact canonical rational request scalar. -/
abbrev Coordinate := Fraction.Rational

/-- Check the computed finite accuracy resolution for an accepted original segment and positive target.

The result records positivity of the selected root diameter and payment of the combined parameter and root error;
rejected or unresolved inputs return no snapshot. -/
public def snapshot (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
    (segment : PathInput.Segment) (target : Coordinate) : Option Bool :=
  if positive : 0 < target then
    match PathInput.prepare polynomial request segment with
    | .error _ => none
    | .ok prepared =>
        match prepared.outcome with
        | .accepted safe =>
            let resolution := Accuracy.resolve safe
              (Data.Gaussian.Norm.Basic.normSq segment.direction)
              (Data.Gaussian.Norm.Basic.normSq_nonneg segment.direction) target positive
            some (decide (0 < resolution.rootDiameter ∧
              Geometric.Basic.quarterRadius resolution.parameterScale resolution.minimumDepth +
                resolution.rootScale * resolution.rootDiameter < target))
        | .endpointObstruction .. | .inconclusive .. => none
  else none

/-- The original repeated-factor path generates paid accuracy requests at both displayed targets and on reversal. -/
theorem repeated_factor_numerical_requests :
    snapshot ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨3, ⟨13/4, 0⟩⟩ 1 = some true ∧
      snapshot ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨3, ⟨13/4, 0⟩⟩ (1/64) = some true ∧
      snapshot ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨⟨13/4, 0⟩, 3⟩ (1/64) = some true := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

/-- Read the accepted original segment's computed root norm floor and parameter/root coefficient slopes. -/
public def coefficientBudget (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
    (segment : PathInput.Segment) : Option (Coordinate × Coordinate × Coordinate) :=
  match PathInput.prepare polynomial request segment with
  | .error _ => none
  | .ok prepared =>
      match prepared.outcome with
      | .accepted _ => some (prepared.data.rootNormFloor,
          CoefficientBounds.parameterSlope prepared.data,
          CoefficientBounds.rootSlope prepared.data)
      | .endpointObstruction .. | .inconclusive .. => none

/-- The actual raw positive-genus repeated-factor fixture gets its bounds from the new enclosures. These numbers are
computed, not supplied as a certificate or obtained by rescaling its reduced curve or shortening its path. -/
theorem positive_genus_repeated_factor_budget :
    coefficientBudget ⟨[1, 0, 0, 1, 0, 0]⟩ (.original 0) ⟨1, ⟨17/16, 0⟩⟩ =
      some (1/4, Fraction.Cast.fromInt 148270945 /
        Fraction.Cast.fromInt 268435456, 289/16) := by
  decide +kernel

/-- Zero movement and zero parameter slope need no division by those scales. -/
theorem vanishing_scales_are_supported :
    snapshot ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨3, 3⟩ (1/64) = some true ∧
      snapshot ⟨[2]⟩ (.original 0) ⟨0, 1⟩ (1/64) = some true ∧
      snapshot ⟨[1, 0, 0]⟩ (.original 1) ⟨0, 1⟩ (1/64) = some true := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

/-- A nonpositive target or an actual endpoint obstruction yields no successful accuracy snapshot. -/
theorem invalid_requests_and_obstructions_remain_explicit :
    snapshot ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨3, ⟨13/4, 0⟩⟩ 0 = none ∧
      snapshot ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨0, ⟨1/4, 0⟩⟩ 1 = none := by
  constructor <;> decide +kernel

end Test.Riemann.SquareFactorAccuracyTests
