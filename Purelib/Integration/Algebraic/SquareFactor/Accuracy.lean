module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
public import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Integration.Algebraic.SquareFactor.MeshBounds
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Requested accuracy for original-differential path models

The numerical request determines the root diameter and the minimum mesh
depth.  Continuation safety may increase that depth; the proved allowance
only improves.  The resulting bound concerns the actual owner-backed path
model.  Agreement between different runs is a separate refinement theorem,
not a consequence asserted here from small individual allowances.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.Accuracy

open Purelib.Integration.Algebraic.SquareFactor

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- The rational carrier for weighted accuracy requests. -/
abbrev Coordinate := Fraction.Rational

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}

open Purelib.Approximation.Rational in
set_option genInjectivity false in
/-- Cached parameter and root scales with a positive root-diameter request and a sufficient minimum dyadic depth.

The equations retain the original weight and target, allocating half the target to each of the parameter and root
contributions. -/
structure Resolution (data : PathInput.Data prepared segment) (weight target : Coordinate) where
  /-- The original weighting factor is nonnegative. -/ weightNonnegative : 0 ≤ weight
  /-- The cached weighted parameter slope. -/ parameterScale : Coordinate
  /-- The cached parameter scale equals weight times the original parameter slope. -/ parameterScale_eq : parameterScale
    = weight * CoefficientBounds.parameterSlope data
  /-- The cached weighted root slope. -/ rootScale : Coordinate
  /-- The cached root scale equals weight times the original root slope. -/ rootScale_eq : rootScale = weight *
    CoefficientBounds.rootSlope data
  /-- The retained positive root-diameter request. -/ rootDiameter : Coordinate
  /-- The retained diameter equals the original target divided by twice the sum of the root scale and one. -/
    rootDiameter_eq : rootDiameter = target / (2 * (rootScale + 1))
  /-- The retained root-diameter request is positive. -/ rootDiameterPositive : 0 < rootDiameter
  /-- The retained sufficient minimum dyadic depth. -/ minimumDepth : Nat
  /-- The retained depth equals the first quarter radius below half the original target. -/ minimumDepth_eq :
    minimumDepth = Geometric.Search.firstQuarterBelow parameterScale 0 (target / 2)

constructive_injectivity Resolution

/-- Adding one to a nonnegative rational scale gives a positive denominator factor. -/
public theorem scale_add_one_positive {scale : Coordinate} (nonnegative : 0 ≤ scale) :
    0 < scale + 1 := by
  have bound : (1 : Coordinate) ≤ scale + 1 := by
    simpa only [_root_.zero_add] using add_le_add nonnegative (le_refl (1 : Coordinate))
  exact (show (0 : Coordinate) < 1 by decide).trans_le bound

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Cache the weighted slopes and choose a positive root diameter and finite quarter-radius depth for the target.

The diameter divides the target by twice the sum of the root scale and one, while the depth is the first certified
parameter radius below half the target. -/
@[expose] def resolve {data : PathInput.Data prepared segment} (safe : data.Safe) (weight : Coordinate)
    (weightNonnegative : 0 ≤ weight) (target : Coordinate)
    (positive : 0 < target) : Resolution data weight target :=
  let parameterScale := weight * CoefficientBounds.parameterSlope data
  let rootScale := weight * CoefficientBounds.rootSlope data
  let diameter := target / (2 * (rootScale + 1))
  { weightNonnegative, parameterScale, parameterScale_eq := rfl
    rootScale, rootScale_eq := rfl
    rootDiameter := diameter
    rootDiameter_eq := rfl
    rootDiameterPositive := Fraction.Order.Field.div_pos_direct positive
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (scale_add_one_positive (Fraction.Order.Arithmetic.mul_nonneg_direct
          weightNonnegative (CoefficientBounds.rootSlope_nonnegative safe))))
    minimumDepth := Geometric.Search.firstQuarterBelow parameterScale 0 (target / 2)
    minimumDepth_eq := rfl }

namespace Resolution

variable {data : Purelib.Integration.Algebraic.SquareFactor.PathInput.Data prepared segment} {weight target :
  Purelib.Integration.Algebraic.SquareFactor.Accuracy.Coordinate}
  (resolution : Purelib.Integration.Algebraic.SquareFactor.Accuracy.Resolution data weight target)

section
open Purelib.Data.Rat
/-- Safety and the retained nonnegative weight make the cached parameter scale nonnegative. -/
theorem parameterScale_nonnegative (safe : data.Safe) : 0 ≤ resolution.parameterScale := by
  rw [resolution.parameterScale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct resolution.weightNonnegative
    (CoefficientBounds.parameterSlope_nonnegative safe)

/-- Safety and the retained nonnegative weight make the cached root scale nonnegative. -/
theorem rootScale_nonnegative (safe : data.Safe) : 0 ≤ resolution.rootScale := by
  rw [resolution.rootScale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct resolution.weightNonnegative
    (CoefficientBounds.rootSlope_nonnegative safe)

end

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Every depth meeting the retained minimum makes the parameter contribution strictly smaller than half the positive
target. -/
theorem parameter_error_lt (safe : data.Safe) (positive : 0 < target)
    (depth : Nat) (enough : resolution.minimumDepth ≤ depth) :
    Geometric.Basic.quarterRadius resolution.parameterScale depth < target / 2 := by
  have halfPositive := Fraction.Order.Field.div_pos_direct positive
    (show (0 : Accuracy.Coordinate) < 2 by decide)
  have accurate := Geometric.Search.firstQuarterBelow_accurate resolution.parameterScale
    (resolution.parameterScale_nonnegative safe) 0 (target / 2) halfPositive
  rw [← resolution.minimumDepth_eq] at accurate
  exact (quarterRadius_antitone
    (resolution.parameterScale_nonnegative safe) enough).trans_lt accurate

open Purelib.Data.Rat in
/-- The retained root-scale contribution is at most half the target. -/
theorem root_error_le (safe : data.Safe) :
    resolution.rootScale * resolution.rootDiameter ≤ target / 2 := by
  have scalePositive := Accuracy.scale_add_one_positive (resolution.rootScale_nonnegative safe)
  have denominatorPositive := Fraction.Order.Arithmetic.mul_pos_direct
    (show (0 : Accuracy.Coordinate) < 2 by decide) scalePositive
  have cancellation : (resolution.rootScale + 1) * resolution.rootDiameter = target / 2 := by
    apply Fraction.Field.mul_right_cancel_of_ne (show (2 : Accuracy.Coordinate) ≠ 0 by decide)
    calc
      ((resolution.rootScale + 1) * resolution.rootDiameter) * 2 =
          resolution.rootDiameter * (2 * (resolution.rootScale + 1)) := by ring1
      _ = target := by
        rw [resolution.rootDiameter_eq]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ (ne_of_gt denominatorPositive)
      _ = (target / 2) * 2 :=
        (Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)).symm
  calc
    resolution.rootScale * resolution.rootDiameter ≤
        (resolution.rootScale + 1) * resolution.rootDiameter :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_right (show (0 : Accuracy.Coordinate) ≤ 1 by decide)) resolution.rootDiameterPositive.le
    _ = target / 2 := cancellation

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- The combined weighted parameter and root error is strictly below the original positive target.

The depth meets the retained minimum, and the separate strict parameter bound and weak root bound preserve the original
target allocation. -/
theorem model_bound_lt (safe : data.Safe) (positive : 0 < target)
    (depth : Nat) (enough : resolution.minimumDepth ≤ depth) :
    weight *
      (CoefficientBounds.parameterSlope data * Geometric.Basic.quarterRadius 1 depth +
        CoefficientBounds.rootSlope data * resolution.rootDiameter) < target := by
  have splitBound : weight *
      (CoefficientBounds.parameterSlope data * Geometric.Basic.quarterRadius 1 depth +
        CoefficientBounds.rootSlope data * resolution.rootDiameter) =
      Geometric.Basic.quarterRadius resolution.parameterScale depth +
        resolution.rootScale * resolution.rootDiameter := by
    rw [resolution.parameterScale_eq, resolution.rootScale_eq,
      Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  rw [splitBound]
  have halfSum : target / 2 + target / 2 = target := by
    calc
      target / 2 + target / 2 = (target / 2) * 2 := by ring1
      _ = target := Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)
  have firstBound := Fraction.Order.Arithmetic.add_lt_add_right_direct
    (resolution.parameter_error_lt safe positive depth enough) (resolution.rootScale * resolution.rootDiameter)
  have secondBound := add_le_add (le_refl (target / 2)) (resolution.root_error_le safe)
  exact (firstBound.trans_le secondBound).trans_eq halfSum

end Resolution

open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- The exact original sheet run compiled from a retained direction-weighted target resolution.

The compiled owner and mesh remain indexed by that resolution's original diameter and minimum depth. -/
structure AccurateRun {data : PathInput.Data prepared segment} (safe : data.Safe)
    (sheet : Fin 2) (target : Coordinate) where
  /-- The retained target resolution weighted by the original segment direction's squared norm. -/ resolution :
    Resolution data (Data.Gaussian.Norm.Basic.normSq segment.direction) target
  /-- The exact compiled original-sheet run indexed by the retained resolution's diameter and minimum depth. -/ compiled
    : OwnedCells.CompiledRun safe sheet resolution.rootDiameter
    resolution.rootDiameterPositive resolution.minimumDepth

constructive_injectivity AccurateRun

open Purelib.Data.Gaussian in
/-- Resolve the original positive target using the segment direction norm and compile the exact selected-sheet run. -/
@[expose] def compile {data : PathInput.Data prepared segment} (safe : data.Safe) (sheet : Fin 2)
    (target : Coordinate) (positive : 0 < target) : AccurateRun safe sheet target :=
  let resolution := resolve safe (Data.Gaussian.Norm.Basic.normSq segment.direction) (Norm.Basic.normSq_nonneg
    segment.direction) target positive
  { resolution
    compiled := OwnedCells.compile sheet resolution.rootDiameter
      resolution.rootDiameterPositive resolution.minimumDepth }

/-- The exact retained compiled path allowance is strictly below the original positive target. -/
theorem aggregateAllowance_lt {data : PathInput.Data prepared segment} {safe : data.Safe}
    {sheet : Fin 2} {target : Coordinate} (run : AccurateRun safe sheet target)
    (positive : 0 < target) : run.compiled.pathModel.aggregateAllowance < target :=
  (MeshBounds.CompiledRun.aggregateAllowance_le run.compiled).trans_lt
    (run.resolution.model_bound_lt safe positive _ run.compiled.minimumDepth_le)

end Purelib.Integration.Algebraic.SquareFactor.Accuracy
