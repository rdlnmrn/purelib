module
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Power.Gaussian
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Square.Anchored
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Bounds
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Newton.Restart.Anchored.Basic
import Purelib.RootIsolation.Newton.Restart.Anchored.Budget
import Purelib.RootIsolation.Newton.Restart.Anchored.Prepare
import Purelib.RootIsolation.Newton.Restart.Anchored.Seed
import Purelib.RootIsolation.Newton.Restart.Seed.Geometry
public import Purelib.RootIsolation.Newton.Restart.Seed.Separated.State
import Purelib.RootIsolation.Newton.Restart.Uniform.Anchored
import Purelib.RootIsolation.Newton.Restart.Uniform.Budget
import Purelib.RootIsolation.Residual.Global.Assignment
import Purelib.RootIsolation.Residual.Global.Bounds
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Build

import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Interior
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.RootIsolation.Newton.Restart.Seed.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Sample
import Purelib.RootIsolation.Newton.Restart.Seed.Track
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.RootIsolation.Newton.Restart.Seed.State
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Path-controlled square-root preparation

Residual localization fixes the preparation radius before reading the retained
owner's sample. Global finite isolation data, the clear segment's uniform
degree-two derivative separation and the requested root diameter determine
this radius. The retained owner then supplies a sufficiently accurate rational
sample of that same root occurrence.
-/

namespace Purelib.Riemann.RootContinuation.RobustSquareRootPreparation

open Purelib.Data.Rat

/-- The exact rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- Dense Gaussian polynomials over exact rational coordinates. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The original rational box type with retained coordinate bounds. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root owner indexed by its exact radicand. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner

open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- The square-root quadratic for the polynomial value at the original segment parameter.

The segment and retained parameter determine its exact polynomial value.
The square-root quadratic keeps that radicand and the degree-two owner. -/
@[expose] def rootPolynomialAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) : GaussianPolynomial :=
  SquareRootReconditioning.rootPolynomial
    (polynomial.eval (segment.pointAt parameter))

open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
/-- The explicit squarefree root-isolation input at the retained interior segment parameter.

The supplied interval bounds certify that the segment's polynomial value
is nonzero. Its exact quadratic retains the squarefree and axis-elimination data. -/
@[expose] def inputAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    RootIsolation.FTA.Squarefree.Input (rootPolynomialAt segment parameter) :=
  SquareRootReconditioning.isolationInput
    (segment.pointAt_eval_ne_zero parameter inside)

open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation.Residual in
/-- The protected global root box belonging to the parameter's exact quadratic isolation input.

The exact quadratic input supplies its retained positive degree. Its large
square root box and boundary clearance form the same protected ambient owner. -/
@[expose] def parentAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    Region.ProtectedAmbient
      (rootPolynomialAt segment parameter)
      (Bounds.RootRadius.Box.largeSquareBox
        (rootPolynomialAt segment parameter)) :=
  Global.Assignment.largeSquareProtectedAmbient
    (inputAt segment parameter inside).degreePositive

section
open Purelib.Polynomial
open Purelib.RootIsolation
/-- The uniform anchored radius for the exact parameter quadratic and protected parent, capped at one.

The squarefree quadratic and its protected ambient box determine the
uniform radius. The fixed cap one is retained in this same scalar calculation. -/
@[expose] def radiusReference
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) : Coordinate :=
  Newton.Restart.Uniform.Budget.uniformAnchoredRadius
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside) 1

/-- The retained uniform reference radius is strictly positive. -/
theorem radiusReference_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    0 < radiusReference segment parameter inside :=
  Newton.Restart.Uniform.Budget.uniformAnchoredRadius_pos
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside) (by decide)

end

section
open Purelib.Approximation.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Branches
/-- Choose the minimum radius satisfying reference, residual, Taylor and requested-diameter bounds.

The caps use the same cleared segment, exact parameter quadratic and protected parent. The diameter cap is a positive
dyadic square radius of one eighth of the target. -/
@[expose] def preparationRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) : Coordinate :=
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  min (radiusReference segment parameter inside)
    (min
      (ClearSheetContinuation.squareRootDerivativeThreshold
          segment /
        (2 * Bounds.Box.denseLipschitzBound p parent.box))
      (min
        (ClearSheetContinuation.squareRootDerivativeMargin
            segment /
          (72 * Bounds.Box.Taylor.denseTaylorRemainderBound p parent.box))
        (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius (rootDiameter / 8))))

/-- The retained preparation radius is strictly positive for a positive diameter target.

Each of the four retained caps is positive under the supplied diameter
condition. The same nested rational minima therefore have a positive lower bound. -/
theorem preparationRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    {rootDiameter : Coordinate} (_rootDiameterPositive : 0 < rootDiameter) :
    0 < preparationRadius segment parameter inside rootDiameter := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  have thresholdPositive :=
    ClearSheetContinuation.squareRootDerivativeThreshold_positive
      segment
  have marginPositive :=
    ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment
  have lipschitzPositive :
      0 < Bounds.Box.denseLipschitzBound p parent.box :=
    Bounds.Box.denseLipschitzBound_pos p parent.box
  have taylorPositive :
      0 < Bounds.Box.Taylor.denseTaylorRemainderBound p parent.box :=
    Bounds.Box.Taylor.denseTaylorRemainderBound_pos p parent.box
  unfold preparationRadius
  exact Fraction.Order.Basic.lt_min (radiusReference_positive segment parameter inside)
    (Fraction.Order.Basic.lt_min
      (Fraction.Order.Field.div_pos_direct thresholdPositive
        (Fraction.Order.Arithmetic.mul_pos_direct
          (show (0 : Coordinate) < 2 by decide)
          lipschitzPositive))
      (Fraction.Order.Basic.lt_min
        (Fraction.Order.Field.div_pos_direct marginPositive
          (Fraction.Order.Arithmetic.mul_pos_direct
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 72) (by decide))
            taylorPositive))
        (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_positive _)))

end

open Purelib.Polynomial in
/-- The preparation radius is at most its exact uniform anchored reference.

The first branch of the retained minimum is the uniform anchored radius
of the same exact parameter quadratic and protected parent. -/
theorem preparationRadius_le_reference
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) :
    preparationRadius segment parameter inside rootDiameter ≤
      radiusReference segment parameter inside := by
  unfold preparationRadius
  exact Fraction.Order.Basic.min_le_left _ _

section
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Branches
/-- The preparation radius satisfies the derivative-threshold divided by twice-Lipschitz cap.

The retained radius is bounded by its twice-Lipschitz cap through the
same nested minimum, without changing the threshold or protected parent. -/
theorem preparationRadius_le_thresholdCap
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    preparationRadius segment parameter inside rootDiameter ≤
      ClearSheetContinuation.squareRootDerivativeThreshold
          segment /
        (2 * Bounds.Box.denseLipschitzBound p parent.box) := by
  dsimp only
  exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)

/-- The preparation radius satisfies the derivative-margin divided by seventy-two-times-Taylor cap.

The same nested minimum bounds the retained radius by the derivative
margin divided by seventy-two times the Taylor remainder majorant. -/
theorem preparationRadius_le_taylorCap
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    preparationRadius segment parameter inside rootDiameter ≤
      ClearSheetContinuation.squareRootDerivativeMargin segment /
        (72 * Bounds.Box.Taylor.denseTaylorRemainderBound p parent.box) := by
  dsimp only
  exact (Fraction.Order.Basic.min_le_right _ _).trans
    ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))

end

open Purelib.Approximation.Rational in
open Purelib.Polynomial in
/-- The preparation radius is at most the exact dyadic square radius of one eighth of the target.

The innermost retained cap is the dyadic square radius of one eighth
of the supplied diameter. The preparation minimum does not exceed that cap. -/
theorem preparationRadius_le_diameterCap
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) :
    preparationRadius segment parameter inside rootDiameter ≤
      SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius (rootDiameter / 8) := by
  unfold preparationRadius
  exact (Fraction.Order.Basic.min_le_right _ _).trans
    ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))

section
open Purelib.Polynomial
open Purelib.Riemann.RootContinuation
/-- The smaller of the original owner's interior request and one quarter of the preparation radius.

The minimum keeps the original interior request and one quarter of the
preparation radius as separate caps. Both concern the same retained root owner. -/
@[expose] def bridgeRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Coordinate :=
  min (SquareRootReconditioning.requestedRadius owner)
    ((1 / 4 : Coordinate) *
      preparationRadius segment parameter inside rootDiameter)

/-- The retained bridge radius is strictly positive for a positive diameter target.

The retained interior request is positive. A positive preparation radius
keeps its quarter-scaled cap positive in the same rational minimum. -/
theorem bridgeRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < bridgeRadius segment parameter inside owner rootDiameter :=
  Fraction.Order.Basic.lt_min
    (SquareRootReconditioning.requestedRadius_positive owner)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (preparationRadius_positive segment parameter inside
        rootDiameterPositive))

/-- The bridge radius is at most the original owner's residual interior request.

The bridge minimum retains the original root owner's interior request
as its first cap, so its value cannot exceed that same request. -/
theorem bridgeRadius_le_requested
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    bridgeRadius segment parameter inside owner rootDiameter ≤
      SquareRootReconditioning.requestedRadius owner :=
  Fraction.Order.Basic.min_le_left _ _

end

section
open Purelib.Polynomial
/-- The bridge radius is at most one quarter of the preparation radius.

The second bridge cap is one quarter of the retained preparation radius.
The same minimum bounds the bridge radius by that displayed scalar quantity. -/
theorem bridgeRadius_le_quarterPreparation
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    bridgeRadius segment parameter inside owner rootDiameter ≤
      (1 / 4 : Coordinate) *
        preparationRadius segment parameter inside rootDiameter :=
  Fraction.Order.Basic.min_le_right _ _

/-- The bridge radius is at most the positive preparation radius. -/
theorem bridgeRadius_le_preparation
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    bridgeRadius segment parameter inside owner rootDiameter ≤
      preparationRadius segment parameter inside rootDiameter := by
  let radius := preparationRadius segment parameter inside rootDiameter
  exact (bridgeRadius_le_quarterPreparation segment parameter inside owner
    rootDiameter).trans
      (by
        calc
          (1 / 4 : Coordinate) * radius ≤ 1 * radius :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              (by decide)
              (preparationRadius_positive segment parameter inside
                rootDiameterPositive).le
          _ = radius := by ring1)

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation.Residual in
/-- Combine global location, preparation, bridge, original-clearance and Newton displacement thresholds.

All five bounds concern the same parameter quadratic and original owner, with separate preparation and bridge radii
retained in their assignment thresholds. -/
@[expose] def sampleResidualTarget
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Coordinate :=
  let p := rootPolynomialAt segment parameter
  let input := inputAt segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  let localRadius := bridgeRadius segment parameter inside owner rootDiameter
  min (Global.Bounds.outsideResidualThreshold p)
    (min (Global.Assignment.insideResidualTarget input radius)
      (min (Global.Assignment.insideResidualTarget input localRadius)
        (min (owner.track.initial.clearance.bound / 4)
          (ClearSheetContinuation.squareRootDerivativeMargin
            segment * radius ^ 2))))

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.Residual in
/-- The combined sampling residual threshold is strictly positive for a positive diameter target.

The supplied diameter condition makes both localization radii positive.
The retained global, clearance and displacement caps are therefore all positive. -/
theorem sampleResidualTarget_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < sampleResidualTarget segment parameter inside owner rootDiameter := by
  let p := rootPolynomialAt segment parameter
  let input := inputAt segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  let localRadius :=
    SquareRootReconditioning.requestedRadius owner
  unfold sampleResidualTarget
  apply Fraction.Order.Basic.lt_min
  · exact Global.Bounds.outsideResidualThreshold_pos input.degreePositive
  · apply Fraction.Order.Basic.lt_min
    · exact Global.Assignment.insideResidualTarget_pos input
        (preparationRadius_positive segment parameter inside
          rootDiameterPositive)
    · apply Fraction.Order.Basic.lt_min
      · exact Global.Assignment.insideResidualTarget_pos input
          (bridgeRadius_positive segment parameter inside owner
            rootDiameterPositive)
      · apply Fraction.Order.Basic.lt_min
        · exact Fraction.Order.Field.div_pos_direct
            owner.track.initial.clearance.positive (by decide)
        · exact Fraction.Order.Arithmetic.mul_pos_direct
            (ClearSheetContinuation.squareRootDerivativeMargin_positive
              segment)
            (Fraction.Order.Arithmetic.pow_pos_direct
              (preparationRadius_positive segment parameter inside
                rootDiameterPositive) 2)

open Purelib.Approximation.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Search the original owner's geometric residual scale for the combined preparation threshold.

The finite search starts at zero with the owner's residual scale. Its
target is the combined localization and displacement threshold for that owner. -/
@[expose] def sampleIndex
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Nat :=
  Geometric.Search.firstQuarterBelow
    (CoherentRoot.residualScale
      (rootPolynomialAt segment parameter) owner.ambient owner.track)
    0 (sampleResidualTarget segment parameter inside owner rootDiameter)

open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Read the original root-track sample at the retained preparation search index.

The retained search index selects the sample of the original coherent
approximation. No new root, track or approximation is constructed by this read. -/
@[expose] def sample
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Gaussian :=
  (CoherentRoot.approximation owner.track).sample
    (sampleIndex segment parameter inside owner rootDiameter)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- The selected sample's squared residual lies below the exact combined threshold. -/
theorem sample_residual_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      sampleResidualTarget segment parameter inside owner rootDiameter := by
  exact (CoherentRoot.sample_residual_le owner.track (by
    rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
    exact SquareRootDegree.degreeTwo.positive)
      (sampleIndex segment parameter inside owner rootDiameter)).trans_lt
    (Geometric.Search.firstQuarterBelow_accurate
      (CoherentRoot.residualScale
        (rootPolynomialAt segment parameter) owner.ambient owner.track)
      (CoherentRoot.residualScale_nonneg
        (rootPolynomialAt segment parameter) owner.ambient owner.track)
      0 (sampleResidualTarget segment parameter inside owner rootDiameter)
      (sampleResidualTarget_positive segment parameter inside owner
        rootDiameterPositive))

open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- The selected sample remains in the original owner's initial box. -/
theorem sample_inside_owner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    owner.track.initial.box.Contains
      (sample segment parameter inside owner rootDiameter) := by
  rw [sample, CoherentRoot.approximation_sample]
  exact (CoherentRoot.state_refines_of_le owner.track
    (Nat.zero_le _)).contains
      (CoherentRoot.state owner.track
        (sampleIndex segment parameter inside owner rootDiameter)).box.contains_anchor

section
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.RootIsolation.Residual
/-- The selected residual meets the global assignment threshold for the preparation radius.

The combined residual minimum retains this preparation-radius assignment
cap. Its scalar projection transports the selected sample's strict residual bound. -/
theorem sample_residual_lt_insideTarget
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      Global.Assignment.insideResidualTarget
        (inputAt segment parameter inside)
        (preparationRadius segment parameter inside rootDiameter) :=
  (sample_residual_lt segment parameter inside owner rootDiameterPositive).trans_le
    ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))

/-- The selected residual meets the global assignment threshold for the bridge radius.

The combined residual minimum separately retains this bridge-radius
assignment cap. The selected sample obeys that same scalar threshold. -/
theorem sample_residual_lt_bridgeInsideTarget
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      Global.Assignment.insideResidualTarget
        (inputAt segment parameter inside)
        (bridgeRadius segment parameter inside owner rootDiameter) :=
  (sample_residual_lt segment parameter inside owner rootDiameterPositive).trans_le
    ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The selected residual lies below one quarter of the original owner's boundary clearance.

The original owner's boundary-clearance quarter is a retained residual
cap. Projecting that same cap preserves the strict selected-sample estimate. -/
theorem sample_residual_lt_ownerQuarter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      owner.track.initial.clearance.bound / 4 :=
  (sample_residual_lt segment parameter inside owner rootDiameterPositive).trans_le
    ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))))

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation.Residual in
/-- The selected sample lies in the exact quadratic's certified global root box.

An outside point has the retained global residual lower bound. The same
selected sample lies below that cap, which excludes the outside case. -/
theorem sample_inside_largeSquare
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (Bounds.RootRadius.Box.largeSquareBox
      (rootPolynomialAt segment parameter)).Contains
        (sample segment parameter inside owner rootDiameter) := by
  by_cases contained :
      (Bounds.RootRadius.Box.largeSquareBox
        (rootPolynomialAt segment parameter)).Contains
          (sample segment parameter inside owner rootDiameter)
  · exact contained
  · have outsideLower := Global.Bounds.outsideResidualThreshold_le
      (inputAt segment parameter inside).degreeAtLeastTwo
      (sample segment parameter inside owner rootDiameter) contained
    have residualBelowOutside :=
      (sample_residual_lt segment parameter inside owner
        rootDiameterPositive).trans_le (Fraction.Order.Basic.min_le_left _ _)
    exact ((not_lt_of_ge outsideLower) residualBelowOutside).elim

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The selected residual lies below one quarter of the protected parent's clearance.

The preparation assignment threshold retains this protected parent's
clearance quarter as its first cap. The selected residual obeys that scalar bound. -/
theorem sample_residual_lt_parentQuarter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      (parentAt segment parameter inside).clearance.bound / 4 :=
  (sample_residual_lt_insideTarget segment parameter inside owner
    rootDiameterPositive).trans_le (Fraction.Order.Basic.min_le_left _ _)

section
open Purelib.Polynomial
open Purelib.RootIsolation
/-- Prepare a localized anchored Newton input at the original sample and preparation radius.

The exact quadratic and protected parent are retained, using the same global containment and residual witnesses to
establish strict localization. -/
@[expose] def anchoredInput
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Newton.Restart.Anchored.Basic.AnchoredInput
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside) := by
  let point := sample segment parameter inside owner rootDiameter
  let radius := preparationRadius segment parameter inside rootDiameter
  have localized :=
    Newton.Restart.Uniform.Anchored.uniform_residual_strict_and_anchored
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside) point
      (sample_inside_largeSquare segment parameter inside owner
        rootDiameterPositive)
      (preparationRadius_positive segment parameter inside
        rootDiameterPositive)
      (sample_residual_lt_insideTarget segment parameter inside owner
        rootDiameterPositive)
  exact Newton.Restart.Anchored.Prepare.anchoredInputOfResidual
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside) point localized.1
    (preparationRadius_positive segment parameter inside
      rootDiameterPositive) localized.2

/-- The anchored input retains exactly the selected preparation radius. -/
theorem anchoredInput_radius_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (anchoredInput segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        preparationRadius segment parameter inside rootDiameter := by
  change Newton.Restart.Anchored.Budget.anchoredRadius
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside)
      (sample segment parameter inside owner rootDiameter)
      (preparationRadius segment parameter inside rootDiameter) =
    preparationRadius segment parameter inside rootDiameter
  exact Newton.Restart.Uniform.Anchored.anchoredRadius_eq_cap_of_le_uniformReference
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside)
    (sample segment parameter inside owner rootDiameter)
    (sample_inside_largeSquare segment parameter inside owner
      rootDiameterPositive)
    (preparationRadius_le_reference segment parameter inside rootDiameter)
    (sample_residual_lt_parentQuarter segment parameter inside owner
      rootDiameterPositive)

end

section
open Purelib.Polynomial
/-- Construct the explicit Newton restart seed from the retained preparation input and axis elimination.

The selected preparation input supplies its same radius and anchor. The
quadratic's retained axis-elimination witness determines this exact restart seed. -/
@[expose] def seed
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :=
  (anchoredInput segment parameter inside owner rootDiameter
    rootDiameterPositive).seed (inputAt segment parameter inside).elimination

/-- The restart seed retains exactly the selected preparation radius. -/
theorem seed_radius_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (seed segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        preparationRadius segment parameter inside rootDiameter := by
  change (anchoredInput segment parameter inside owner rootDiameter
    rootDiameterPositive).radius = _
  exact anchoredInput_radius_eq segment parameter inside owner
    rootDiameterPositive

end

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The preparation seed's source anchor is exactly the retained original track sample. -/
theorem seed_source_anchor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (seed segment parameter inside owner rootDiameter
        rootDiameterPositive).source.anchor =
      sample segment parameter inside owner rootDiameter := by
  rw [seed, Newton.Restart.Anchored.Basic.AnchoredInput.seed_source,
    Box.Square.Anchored.anchoredSquare_anchor]
  unfold anchoredInput
  rfl

section
open Purelib.Polynomial
open Purelib.RootIsolation
/-- Prepare a second localized anchored input at the same original sample using the smaller bridge radius.

This input retains the same quadratic and protected parent as the preparation input, while its separate radius supports
strict owner comparison. -/
@[expose] def bridgeAnchoredInput
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Newton.Restart.Anchored.Basic.AnchoredInput
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside) := by
  let point := sample segment parameter inside owner rootDiameter
  have localized :=
    Newton.Restart.Uniform.Anchored.uniform_residual_strict_and_anchored
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside) point
      (sample_inside_largeSquare segment parameter inside owner
        rootDiameterPositive)
      (bridgeRadius_positive segment parameter inside owner
        rootDiameterPositive)
      (sample_residual_lt_bridgeInsideTarget segment parameter inside owner
        rootDiameterPositive)
  exact Newton.Restart.Anchored.Prepare.anchoredInputOfResidual
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside) point localized.1
    (bridgeRadius_positive segment parameter inside owner
      rootDiameterPositive) localized.2

/-- The bridge input retains exactly the selected bridge radius.

The retained bridge radius satisfies both the uniform reference cap and
the same parent's clearance threshold, so anchored preparation keeps that radius. -/
theorem bridgeAnchoredInput_radius_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeAnchoredInput segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        bridgeRadius segment parameter inside owner rootDiameter := by
  change Newton.Restart.Anchored.Budget.anchoredRadius
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside)
      (sample segment parameter inside owner rootDiameter)
      (bridgeRadius segment parameter inside owner rootDiameter) =
    bridgeRadius segment parameter inside owner rootDiameter
  apply Newton.Restart.Uniform.Anchored.anchoredRadius_eq_cap_of_le_uniformReference
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside)
    (sample segment parameter inside owner rootDiameter)
    (sample_inside_largeSquare segment parameter inside owner
      rootDiameterPositive)
  · exact (bridgeRadius_le_preparation segment parameter inside owner
      rootDiameterPositive).trans
        (preparationRadius_le_reference segment parameter inside rootDiameter)
  · exact (sample_residual_lt_bridgeInsideTarget segment parameter inside owner
      rootDiameterPositive).trans_le (Fraction.Order.Basic.min_le_left _ _)

end

section
open Purelib.Polynomial
/-- Construct the bridge restart seed from the exact bridge input and original axis elimination.

The selected bridge input supplies its smaller radius at the same sample.
The quadratic's retained axis-elimination witness determines this restart seed. -/
@[expose] def bridgeSeed
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :=
  (bridgeAnchoredInput segment parameter inside owner rootDiameter
    rootDiameterPositive).seed (inputAt segment parameter inside).elimination

/-- The bridge seed retains exactly the selected bridge radius. -/
theorem bridgeSeed_radius_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeSeed segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        bridgeRadius segment parameter inside owner rootDiameter := by
  change (bridgeAnchoredInput segment parameter inside owner rootDiameter
    rootDiameterPositive).radius = _
  exact bridgeAnchoredInput_radius_eq segment parameter inside owner
    rootDiameterPositive

end

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The bridge seed's source anchor is the same retained original track sample. -/
theorem bridgeSeed_source_anchor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeSeed segment parameter inside owner rootDiameter
        rootDiameterPositive).source.anchor =
      sample segment parameter inside owner rootDiameter := by
  rw [bridgeSeed, Newton.Restart.Anchored.Basic.AnchoredInput.seed_source,
    Box.Square.Anchored.anchoredSquare_anchor]
  unfold bridgeAnchoredInput
  rfl

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- Read the certified bridge seed as a winding-one track in the exact global root box.

The bridge seed and its original degree witness determine the track in
the exact protected global root box. Its initial state retains the bridge seed. -/
@[expose] def bridgeTrack
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Track.Basic.WindingOneTrack
      (rootPolynomialAt segment parameter)
      (Bounds.RootRadius.Box.largeSquareBox (rootPolynomialAt segment parameter)) :=
  (bridgeSeed segment parameter inside owner rootDiameter
    rootDiameterPositive).track
      (inputAt segment parameter inside).degreeAtLeastTwo

open Purelib.Algebra in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Three times the retained bridge radius is below the original owner's residual interior radius. -/
theorem three_bridgeRadius_lt_ownerInterior
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    3 * bridgeRadius segment parameter inside owner rootDiameter <
      owner.track.initial.clearance.residualInteriorRadius := by
  let radius := bridgeRadius segment parameter inside owner rootDiameter
  let interior := owner.track.initial.clearance.residualInteriorRadius
  have interiorPositive : 0 < interior := by
    simpa only [interior] using
      owner.track.initial.clearance.residualInteriorRadius_pos
  have radiusLeRequested : radius ≤
      SquareRootReconditioning.requestedRadius owner :=
    bridgeRadius_le_requested segment parameter inside owner rootDiameter
  have requestedFormula :
      SquareRootReconditioning.requestedRadius owner =
        (1 / 8 : Coordinate) * interior := by
    dsimp only [SquareRootReconditioning.requestedRadius,
      interior]
    simp only [Field.ExplicitField.div_eq_mul_inv,
      Fraction.Field.one_mul]
    rw [Fraction.Field.mul_comm]
  calc
    3 * radius ≤
        3 * SquareRootReconditioning.requestedRadius owner :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        radiusLeRequested (by decide)
    _ = (3 * (1 / 8 : Coordinate)) * interior := by
      rw [requestedFormula]
      ring1
    _ < 1 * interior :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (by decide) interiorPositive
    _ = interior := by ring1

section
open Purelib.Polynomial
/-- The bridge track's initial box lies strictly inside the original owner's initial box.

The common sample and original interior margins combine with the bridge band's three-radius bounds to certify all four
strict inequalities. -/
theorem bridgeTrack_initial_strict_owner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeTrack segment parameter inside owner rootDiameter
      rootDiameterPositive).initial.box.StrictInterior
        owner.track.initial.box := by
  let common := bridgeSeed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let point := sample segment parameter inside owner rootDiameter
  let radius := bridgeRadius segment parameter inside owner rootDiameter
  let interior := owner.track.initial.clearance.residualInteriorRadius
  have margins := owner.track.initial.clearance.residualInteriorMargins
    (sample_inside_owner segment parameter inside owner rootDiameter)
    (sample_residual_lt_ownerQuarter segment parameter inside owner
      rootDiameterPositive)
  have bandBounds := common.anchor_band_coordinate_bounds
  have commonAnchor : common.source.anchor = point := by
    dsimp only [common, point]
    exact bridgeSeed_source_anchor segment parameter inside owner
      rootDiameterPositive
  have commonRadius : common.radius = radius := by
    dsimp only [common, radius]
    exact bridgeSeed_radius_eq segment parameter inside owner
      rootDiameterPositive
  have bandLeft : point.re - 3 * radius ≤ common.band.box.xLower := by
    rw [← commonAnchor, ← commonRadius]
    exact bandBounds.1
  have bandRight : common.band.box.xUpper ≤ point.re + 3 * radius := by
    rw [← commonAnchor, ← commonRadius]
    exact bandBounds.2.1
  have bandBottom : point.im - 3 * radius ≤ common.band.box.yLower := by
    rw [← commonAnchor, ← commonRadius]
    exact bandBounds.2.2.1
  have bandTop : common.band.box.yUpper ≤ point.im + 3 * radius := by
    rw [← commonAnchor, ← commonRadius]
    exact bandBounds.2.2.2
  have threeRadiusSmall : 3 * radius < interior :=
    three_bridgeRadius_lt_ownerInterior segment parameter inside owner
      rootDiameter
  have negatedSmall : -interior < -(3 * radius) :=
    Fraction.Order.Arithmetic.neg_lt_neg_direct threeRadiusSmall
  change common.band.box.StrictInterior owner.track.initial.box
  exact
    { left := by
        calc
          owner.track.initial.box.xLower < point.re - interior := by
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
              margins.1 (-interior)
            dsimp only [point, interior] at shifted ⊢
            convert shifted using 1 <;> ring1
          _ < point.re - 3 * radius := by
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
              negatedSmall point.re
            convert shifted using 1 <;> ring1
          _ ≤ common.band.box.xLower := bandLeft
      right := by
        calc
          common.band.box.xUpper ≤ point.re + 3 * radius := bandRight
          _ < point.re + interior := by
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
              threeRadiusSmall point.re
            convert shifted using 1 <;> ring1
          _ < owner.track.initial.box.xUpper := by
            simpa only [point, interior] using margins.2.1
      bottom := by
        calc
          owner.track.initial.box.yLower < point.im - interior := by
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
              margins.2.2.1 (-interior)
            dsimp only [point, interior] at shifted ⊢
            convert shifted using 1 <;> ring1
          _ < point.im - 3 * radius := by
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
              negatedSmall point.im
            convert shifted using 1 <;> ring1
          _ ≤ common.band.box.yLower := bandBottom
      top := by
        calc
          common.band.box.yUpper ≤ point.im + 3 * radius := bandTop
          _ < point.im + interior := by
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
              threeRadiusSmall point.im
            convert shifted using 1 <;> ring1
          _ < owner.track.initial.box.yUpper := by
            simpa only [point, interior] using margins.2.2.2 }

/-- Twice the bridge radius is strictly below the positive preparation radius. -/
theorem two_bridgeRadius_lt_preparationRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    2 * bridgeRadius segment parameter inside owner rootDiameter <
      preparationRadius segment parameter inside rootDiameter := by
  let radius := bridgeRadius segment parameter inside owner rootDiameter
  let preparation := preparationRadius segment parameter inside rootDiameter
  have radiusCap : radius ≤ (1 / 4 : Coordinate) * preparation :=
    bridgeRadius_le_quarterPreparation segment parameter inside owner
      rootDiameter
  have preparationPositive : 0 < preparation :=
    preparationRadius_positive segment parameter inside rootDiameterPositive
  calc
    2 * radius ≤ 2 * ((1 / 4 : Coordinate) * preparation) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusCap
        (by decide)
    _ = (2 * (1 / 4 : Coordinate)) * preparation := by ring1
    _ < 1 * preparation :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (by decide) preparationPositive
    _ = preparation := by ring1

end

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- The bridge state lies strictly inside the preparation seed's centered box.

Both seeds use the same original sample and hence the same Newton center; their retained radius inequality controls each
box side. -/
theorem bridgeSeed_state_strict_centered
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    ((bridgeSeed segment parameter inside owner rootDiameter
        rootDiameterPositive).state
      (inputAt segment parameter inside).degreeAtLeastTwo).box.StrictInterior
        (seed segment parameter inside owner rootDiameter
          rootDiameterPositive).centeredBox := by
  let common := bridgeSeed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let robust := seed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let radius := bridgeRadius segment parameter inside owner rootDiameter
  let preparation := preparationRadius segment parameter inside rootDiameter
  have commonAnchor : common.source.anchor =
      sample segment parameter inside owner rootDiameter := by
    dsimp only [common]
    exact bridgeSeed_source_anchor segment parameter inside owner
      rootDiameterPositive
  have robustAnchor : robust.source.anchor =
      sample segment parameter inside owner rootDiameter := by
    dsimp only [robust]
    exact seed_source_anchor segment parameter inside owner
      rootDiameterPositive
  have commonRadius : common.radius = radius := by
    dsimp only [common, radius]
    exact bridgeSeed_radius_eq segment parameter inside owner
      rootDiameterPositive
  have robustRadius : robust.radius = preparation := by
    dsimp only [robust, preparation]
    exact seed_radius_eq segment parameter inside owner rootDiameterPositive
  have centersEqual :
      Newton.Box.Anchor.anchorNewtonCenter
          (rootPolynomialAt segment parameter) common.source =
        Newton.Box.Anchor.anchorNewtonCenter
          (rootPolynomialAt segment parameter) robust.source := by
    rw [Newton.Box.Anchor.anchorNewtonCenter_eq,
      Newton.Box.Anchor.anchorNewtonCenter_eq,
      commonAnchor, robustAnchor]
  have twiceRadiusSmall : 2 * radius < preparation :=
    two_bridgeRadius_lt_preparationRadius segment parameter inside owner
      rootDiameterPositive
  change common.band.box.StrictInterior robust.centeredBox
  unfold RootIsolation.Newton.Restart.Seed.centeredBox
  unfold Box.Square.Centered.Affine.centeredSquare
  exact
    { left := by
        calc
          (Newton.Box.Anchor.anchorNewtonCenter
              (rootPolynomialAt segment parameter) robust.source).re -
                robust.radius <
              (Newton.Box.Anchor.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).re -
                  2 * common.radius := by
            rw [← centersEqual, commonRadius, robustRadius]
            have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct
              twiceRadiusSmall
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
              negated
              (Newton.Box.Anchor.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).re
            convert shifted using 1 <;> ring1
          _ ≤ common.band.box.xLower := common.band.left_lower
      right := by
        calc
          common.band.box.xUpper ≤
              (Newton.Box.Anchor.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).re +
                  2 * common.radius := common.band.right_upper
          _ < (Newton.Box.Anchor.anchorNewtonCenter
                (rootPolynomialAt segment parameter) robust.source).re +
              robust.radius := by
            rw [← centersEqual, commonRadius, robustRadius]
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
              twiceRadiusSmall
              (Newton.Box.Anchor.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).re
            convert shifted using 1 <;> ring1
      bottom := by
        calc
          (Newton.Box.Anchor.anchorNewtonCenter
              (rootPolynomialAt segment parameter) robust.source).im -
                robust.radius <
              (Newton.Box.Anchor.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).im -
                  2 * common.radius := by
            rw [← centersEqual, commonRadius, robustRadius]
            have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct
              twiceRadiusSmall
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
              negated
              (Newton.Box.Anchor.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).im
            convert shifted using 1 <;> ring1
          _ ≤ common.band.box.yLower := common.band.bottom_lower
      top := by
        calc
          common.band.box.yUpper ≤
              (Newton.Box.Anchor.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).im +
                  2 * common.radius := common.band.top_upper
          _ < (Newton.Box.Anchor.anchorNewtonCenter
                (rootPolynomialAt segment parameter) robust.source).im +
              robust.radius := by
            rw [← centersEqual, commonRadius, robustRadius]
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
              twiceRadiusSmall
              (Newton.Box.Anchor.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).im
            convert shifted using 1 <;> ring1 }

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The preparation radius is at most one. -/
theorem preparationRadius_le_one
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) :
    preparationRadius segment parameter inside rootDiameter ≤ 1 :=
  (preparationRadius_le_reference segment parameter inside rootDiameter).trans
    (Newton.Restart.Uniform.Budget.uniformAnchoredRadius_bounds
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside) 1).1

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The preparation seed's source box has squared diagonal twice its exact radius squared. -/
theorem seed_source_diagonalSq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (seed segment parameter inside owner rootDiameter
        rootDiameterPositive).source.diagonalSq =
      2 * preparationRadius segment parameter inside rootDiameter ^ 2 := by
  rw [seed, Newton.Restart.Anchored.Basic.AnchoredInput.seed_source,
    Box.Square.Anchored.anchoredSquare_diagonalSq,
    anchoredInput_radius_eq segment parameter inside owner
      rootDiameterPositive]

section
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Branches
/-- The preparation source's residual bound is at most the retained derivative-separation threshold. -/
theorem sourceThreshold
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    let source := (seed segment parameter inside owner rootDiameter
      rootDiameterPositive).source
    Bounds.Box.Residual.anchorResidualBound p parent.box source ≤
      ClearSheetContinuation.squareRootDerivativeThreshold
        segment := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  let source := (seed segment parameter inside owner rootDiameter
    rootDiameterPositive).source
  let lipschitz := Bounds.Box.denseLipschitzBound p parent.box
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment parameter inside rootDiameterPositive
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (preparationRadius_le_one segment parameter inside rootDiameter)
        radiusPositive.le
    exact scaled.trans_eq (one_mul radius)
  have radiusCap :=
    preparationRadius_le_thresholdCap segment parameter inside rootDiameter
  have scaledCap : radius * (2 * lipschitz) ≤
      ClearSheetContinuation.squareRootDerivativeThreshold
        segment :=
    (Fraction.Order.Field.le_div_iff_pos
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Bounds.Box.denseLipschitzBound_pos p parent.box))).1
      radiusCap
  dsimp only
  unfold Bounds.Box.Residual.anchorResidualBound
  rw [seed_source_diagonalSq segment parameter inside owner
    rootDiameterPositive]
  calc
    lipschitz * (2 * radius ^ 2) ≤ lipschitz * (2 * radius) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusSquareLe (by decide))
        (Bounds.Box.denseLipschitzBound_pos p parent.box).le
    _ = radius * (2 * lipschitz) := by ring1
    _ ≤ ClearSheetContinuation.squareRootDerivativeThreshold
          segment := scaledCap

/-- The retained preparation radius makes the scaled Taylor remainder at most the derivative margin. -/
theorem preparationTaylorSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    let radius := preparationRadius segment parameter inside rootDiameter
    2 * (36 * Bounds.Box.Taylor.denseTaylorRemainderBound p parent.box *
        radius ^ 2) ≤
      ClearSheetContinuation.squareRootDerivativeMargin segment := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  let taylor := Bounds.Box.Taylor.denseTaylorRemainderBound p parent.box
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment parameter inside rootDiameterPositive
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (preparationRadius_le_one segment parameter inside rootDiameter)
        radiusPositive.le
    exact scaled.trans_eq (one_mul radius)
  have radiusCap :=
    preparationRadius_le_taylorCap segment parameter inside rootDiameter
  have coefficientPositive : 0 < (72 : Coordinate) * taylor :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 72) (by decide))
      (Bounds.Box.Taylor.denseTaylorRemainderBound_pos p parent.box)
  have scaledCap : radius * (72 * taylor) ≤
      ClearSheetContinuation.squareRootDerivativeMargin segment :=
    (Fraction.Order.Field.le_div_iff_pos coefficientPositive).1 radiusCap
  calc
    2 * (36 * taylor * radius ^ 2) = (72 * taylor) * radius ^ 2 := by ring1
    _ ≤ (72 * taylor) * radius :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusSquareLe
        coefficientPositive.le
    _ = radius * (72 * taylor) := by ring1
    _ ≤ ClearSheetContinuation.squareRootDerivativeMargin segment :=
      scaledCap

/-- The exact restart seed satisfies the same scaled Taylor remainder bound. -/
theorem taylorSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    let radius := (seed segment parameter inside owner rootDiameter
      rootDiameterPositive).radius
    2 * (36 * Bounds.Box.Taylor.denseTaylorRemainderBound p parent.box *
        radius ^ 2) ≤
      ClearSheetContinuation.squareRootDerivativeMargin segment := by
  rw [seed_radius_eq segment parameter inside owner rootDiameterPositive]
  exact preparationTaylorSmall segment parameter inside rootDiameterPositive

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The selected residual is below the derivative margin times preparation radius squared.

The last residual cap is the retained derivative margin times the
preparation radius squared. The same selected sample lies strictly below it. -/
theorem sample_residual_lt_displacementBudget
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      ClearSheetContinuation.squareRootDerivativeMargin segment *
        preparationRadius segment parameter inside rootDiameter ^ 2 :=
  (sample_residual_lt segment parameter inside owner rootDiameterPositive).trans_le
    ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))))

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- The preparation seed's squared Newton displacement is at most its retained radius squared.

The derivative-separation certificate supplies a positive denominator, and the original sample residual pays the exact
displacement formula. -/
theorem displacementSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let source := (seed segment parameter inside owner rootDiameter
      rootDiameterPositive).source
    Data.Gaussian.Norm.Basic.normSq
        (Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor) ≤
      (seed segment parameter inside owner rootDiameter
        rootDiameterPositive).radius ^ 2 := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  let robustSeed := seed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let separation :=
    ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := parent.box) segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  have derivativeLower := separation.lower
    (robustSeed.sourceRefines.contains robustSeed.source.contains_anchor)
    (robustSeed.residual.trans
      (sourceThreshold segment parameter inside owner rootDiameterPositive))
  change separation.margin ≤
    Data.Gaussian.Norm.Basic.normSq
      ((GCD.derivative p).eval
        robustSeed.source.anchor) at derivativeLower
  have derivativeNonzero :
      (GCD.derivative p).eval robustSeed.source.anchor ≠ 0 := by
    intro zero
    rw [zero, Norm.Basic.normSq_zero] at derivativeLower
    exact (not_lt_of_ge derivativeLower)
      (ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment)
  have derivativePositive : 0 <
      Data.Gaussian.Norm.Basic.normSq
        ((GCD.derivative p).eval robustSeed.source.anchor) :=
    Norm.Basic.normSq_pos derivativeNonzero
  have inverseBound :
      (Data.Gaussian.Norm.Basic.normSq
        ((GCD.derivative p).eval
          robustSeed.source.anchor))⁻¹ ≤
      (ClearSheetContinuation.squareRootDerivativeMargin
        segment)⁻¹ :=
    Fraction.Order.Field.inv_le_inv_of_pos_direct
      (ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment) derivativeLower
  dsimp only
  rw [Newton.Box.Anchor.normSq_anchorNewtonCenter_sub_anchor
    derivativeNonzero]
  have residualBound :
      Data.Gaussian.Norm.Basic.normSq
          (p.eval robustSeed.source.anchor) ≤
        ClearSheetContinuation.squareRootDerivativeMargin segment *
          radius ^ 2 := by
    rw [seed_source_anchor segment parameter inside owner rootDiameterPositive]
    exact (sample_residual_lt_displacementBudget segment parameter inside owner
      rootDiameterPositive).le
  calc
    Data.Gaussian.Norm.Basic.normSq
          (p.eval robustSeed.source.anchor) *
        (Data.Gaussian.Norm.Basic.normSq
          ((GCD.derivative p).eval
            robustSeed.source.anchor))⁻¹ ≤
      (ClearSheetContinuation.squareRootDerivativeMargin segment *
          radius ^ 2) *
        (Data.Gaussian.Norm.Basic.normSq
          ((GCD.derivative p).eval
            robustSeed.source.anchor))⁻¹ :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct residualBound
        (Fraction.Order.Field.inv_pos_direct derivativePositive).le
    _ ≤ (ClearSheetContinuation.squareRootDerivativeMargin segment *
          radius ^ 2) *
        (ClearSheetContinuation.squareRootDerivativeMargin
          segment)⁻¹ :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inverseBound
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (ClearSheetContinuation.squareRootDerivativeMargin_positive
            segment).le
          (Fraction.Order.Arithmetic.sq_nonneg_direct radius))
    _ = radius ^ 2 := by
      rw [show
        (ClearSheetContinuation.squareRootDerivativeMargin segment *
            radius ^ 2) *
              (ClearSheetContinuation.squareRootDerivativeMargin
                segment)⁻¹ =
          radius ^ 2 *
            (ClearSheetContinuation.squareRootDerivativeMargin
              segment *
              (ClearSheetContinuation.squareRootDerivativeMargin
                segment)⁻¹) by ring1,
        Fraction.Field.mul_inv_cancel _
          (ClearSheetContinuation.squareRootDerivativeMargin_positive
            segment).ne', mul_one]
    _ = robustSeed.radius ^ 2 := by
      rw [seed_radius_eq segment parameter inside owner rootDiameterPositive]

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation in
/-- Build the separated centered winding-one state from the retained preparation seed.

The original residual, displacement and Taylor bounds feed an explicit positive linearization majorant, retaining the
seed's exact centered box as ambient. -/
@[expose] def state
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    State.WindingOne.Basic.WindingOneState
      (rootPolynomialAt segment parameter)
      (seed segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  let robustSeed := seed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let separation :=
    ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := parent.box) segment parameter inside
  have sourceThreshold' :=
    sourceThreshold segment parameter inside owner rootDiameterPositive
  change Bounds.Box.Residual.anchorResidualBound p parent.box
      robustSeed.source ≤ separation.threshold at sourceThreshold'
  have taylorSmall' :=
    taylorSmall segment parameter inside owner rootDiameterPositive
  change 2 * (36 *
      Bounds.Box.Taylor.denseTaylorRemainderBound p parent.box *
        robustSeed.radius ^ 2) ≤ separation.margin at taylorSmall'
  let majorant :=
    Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant p parent.box
      robustSeed.radius
  exact robustSeed.separatedCenteredStateWithMajorant
    (inputAt segment parameter inside).degreeAtLeastTwo separation
    sourceThreshold'
    (displacementSmall segment parameter inside owner rootDiameterPositive)
    taylorSmall' majorant
    (Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant_pos p parent.box
      robustSeed.radiusPositive)
    (fun _z boundary =>
      Newton.Box.Square.Bounds.newtonLinearization_boundary_le_majorant
        robustSeed.sourceRefines robustSeed.radiusPositive boundary)

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation in
/-- The constructed state's clearance is the exact separated dominance formula using its retained majorant. -/
theorem state_clearance_formula
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    let robustSeed := seed segment parameter inside owner rootDiameter
      rootDiameterPositive
    let separation :=
      ClearSheetContinuation.squareRootDerivativeSeparation
        (rootAmbient := parent.box) segment parameter inside
    (state segment parameter inside owner rootDiameter
        rootDiameterPositive).clearance.bound =
      Newton.Box.Square.Separated.separatedNewtonDominanceMargin separation
          robustSeed.radius ^ 2 /
        (4 * Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant
          p parent.box robustSeed.radius) := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  let robustSeed := seed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let separation :=
    ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := parent.box) segment parameter inside
  have sourceThreshold' :=
    sourceThreshold segment parameter inside owner rootDiameterPositive
  change Bounds.Box.Residual.anchorResidualBound p parent.box
      robustSeed.source ≤ separation.threshold at sourceThreshold'
  have taylorSmall' :=
    taylorSmall segment parameter inside owner rootDiameterPositive
  change 2 * (36 *
      Bounds.Box.Taylor.denseTaylorRemainderBound p parent.box *
        robustSeed.radius ^ 2) ≤ separation.margin at taylorSmall'
  let majorant :=
    Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant p parent.box
      robustSeed.radius
  let majorantPositive :=
    Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant_pos p parent.box
      robustSeed.radiusPositive
  let majorantUpper : ∀ z : Gaussian,
      Box.Boundary.OnBoxBoundary robustSeed.centeredBox z →
        Data.Gaussian.Norm.Basic.normSq
          ((Newton.Box.Linearization.newtonLinearization p robustSeed.source).eval z) ≤
            majorant := fun _z boundary =>
    Newton.Box.Square.Bounds.newtonLinearization_boundary_le_majorant
      robustSeed.sourceRefines robustSeed.radiusPositive boundary
  change
    (robustSeed.separatedCenteredStateWithMajorant
      (inputAt segment parameter inside).degreeAtLeastTwo separation
      sourceThreshold'
      (displacementSmall segment parameter inside owner rootDiameterPositive)
      taylorSmall' majorant majorantPositive majorantUpper).clearance.bound = _
  exact
    RootIsolation.Newton.Restart.Seed.separatedCenteredStateWithMajorant_clearance_bound
      (inputAt segment parameter inside).degreeAtLeastTwo robustSeed separation
      sourceThreshold'
      (displacementSmall segment parameter inside owner rootDiameterPositive)
      taylorSmall' majorant majorantPositive majorantUpper

section
open Purelib.Polynomial
open Purelib.RootIsolation in
/-- Start the original Newton refinement algorithm from the constructed centered winding-one state. -/
@[expose] def track
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Track.Basic.WindingOneTrack
      (rootPolynomialAt segment parameter)
      (seed segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox :=
  Track.Newton.Build.ofInitial
    (inputAt segment parameter inside).degreeAtLeastTwo
    (inputAt segment parameter inside).squarefree
    (inputAt segment parameter inside).elimination
    (state segment parameter inside owner rootDiameter rootDiameterPositive)

/-- Package the robustly prepared square-root owner at the original segment parameter.

The retained ambient box is the same preparation seed's centered box, and its track starts from the exact certified
state constructed there. -/
@[expose] def prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Owner (polynomial.eval (segment.pointAt parameter)) := by
  let robustSeed := seed segment parameter inside owner rootDiameter
    rootDiameterPositive
  exact
    { parameterNonzero :=
        segment.pointAt_eval_ne_zero parameter inside
      ambient := robustSeed.centeredBox
      track := track segment parameter inside owner rootDiameter
        rootDiameterPositive }

/-- The same bridge initial box lies strictly inside the robustly prepared owner's initial box. -/
theorem bridgeTrack_initial_strict_prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeTrack segment parameter inside owner rootDiameter
      rootDiameterPositive).initial.box.StrictInterior
        (prepared segment parameter inside owner rootDiameter
          rootDiameterPositive).track.initial.box := by
  change
    ((bridgeSeed segment parameter inside owner rootDiameter
        rootDiameterPositive).state
      (inputAt segment parameter inside).degreeAtLeastTwo).box.StrictInterior
        (seed segment parameter inside owner rootDiameter
          rootDiameterPositive).centeredBox
  exact bridgeSeed_state_strict_centered segment parameter inside owner
    rootDiameterPositive

section
open Purelib.Polynomial.Dense.Gaussian
/-- The explicit separated Newton linearization majorant at the exact preparation radius.

The exact quadratic, protected parent and selected preparation radius
supply the displayed separated Newton linearization majorant. -/
@[expose] def linearizationMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) : Coordinate :=
  Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant
    (rootPolynomialAt segment parameter) (parentAt segment parameter inside).box
    (preparationRadius segment parameter inside rootDiameter)

/-- The retained linearization majorant is strictly positive for a positive target. -/
theorem linearizationMajorant_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < linearizationMajorant segment parameter inside rootDiameter :=
  Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant_pos
    (rootPolynomialAt segment parameter) (parentAt segment parameter inside).box
    (preparationRadius_positive segment parameter inside rootDiameterPositive)

end

section
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Branches
/-- The separated dominance margin squared divided by four times the exact linearization majorant.

This formula depends on the retained segment parameter, protected parent and preparation radius, without choosing a new
root owner. -/
@[expose] def predictedClearance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) : Coordinate :=
  let separation :=
    ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := (parentAt segment parameter inside).box)
      segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  Newton.Box.Square.Separated.separatedNewtonDominanceMargin separation radius ^ 2 /
    (4 * linearizationMajorant segment parameter inside rootDiameter)

/-- The predicted boundary-clearance bound is strictly positive for a positive target. -/
theorem predictedClearance_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < predictedClearance segment parameter inside rootDiameter := by
  let separation :=
    ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := (parentAt segment parameter inside).box)
      segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  have taylor := preparationTaylorSmall segment parameter inside
    rootDiameterPositive
  change 2 * (36 * Bounds.Box.Taylor.denseTaylorRemainderBound
      (rootPolynomialAt segment parameter)
      (parentAt segment parameter inside).box * radius ^ 2) ≤
        separation.margin at taylor
  have dominancePositive :
      0 < Newton.Box.Square.Separated.separatedNewtonDominanceMargin separation radius :=
    Newton.Box.Square.Separated.separatedNewtonDominanceMargin_pos separation
      (preparationRadius_positive segment parameter inside
        rootDiameterPositive) taylor
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct dominancePositive 2)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (linearizationMajorant_positive segment parameter inside
        rootDiameterPositive))

/-- The seed's stored clearance formula equals the original predicted-clearance expression. -/
theorem storedFormula_eq_predictedClearance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    let robustSeed := seed segment parameter inside owner rootDiameter
      rootDiameterPositive
    let separation :=
      ClearSheetContinuation.squareRootDerivativeSeparation
        (rootAmbient := parent.box) segment parameter inside
    Newton.Box.Square.Separated.separatedNewtonDominanceMargin separation
          robustSeed.radius ^ 2 /
        (4 * Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant
          p parent.box robustSeed.radius) =
      predictedClearance segment parameter inside rootDiameter := by
  dsimp only
  rw [seed_radius_eq segment parameter inside owner rootDiameterPositive]
  rfl

end

/-- The prepared owner's actual boundary clearance equals the exact predicted bound. -/
theorem prepared_clearance_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
        rootDiameterPositive).track.initial.clearance.bound =
      predictedClearance segment parameter inside rootDiameter := by
  change (state segment parameter inside owner rootDiameter
    rootDiameterPositive).clearance.bound = _
  exact (state_clearance_formula segment parameter inside owner
    rootDiameterPositive).trans
      (storedFormula_eq_predictedClearance segment parameter inside owner
        rootDiameterPositive)

open Purelib.RootIsolation in
/-- The prepared initial box has squared diagonal eight times the preparation radius squared. -/
theorem prepared_diagonalSq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
        rootDiameterPositive).track.initial.box.diagonalSq =
      8 * preparationRadius segment parameter inside rootDiameter ^ 2 := by
  change (seed segment parameter inside owner rootDiameter
    rootDiameterPositive).centeredBox.diagonalSq = _
  rw [RootIsolation.Newton.Restart.Seed.centeredBox_diagonalSq,
    seed_radius_eq segment parameter inside owner rootDiameterPositive]

end

open Purelib.Approximation.Rational in
open Purelib.Polynomial in
/-- The prepared initial box's squared diagonal is strictly below the requested positive target. -/
theorem prepared_diagonal_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.box.diagonalSq < rootDiameter := by
  let radius := preparationRadius segment parameter inside rootDiameter
  let diameterCap :=
    SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius (rootDiameter / 8)
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment parameter inside rootDiameterPositive
  have radiusLe :=
    preparationRadius_le_diameterCap segment parameter inside rootDiameter
  have squareLe : radius ^ 2 ≤ diameterCap ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le radiusLe 2
  have targetPositive : 0 < rootDiameter / 8 :=
    Fraction.Order.Field.div_pos_direct rootDiameterPositive (by decide)
  have capSquareLt : diameterCap ^ 2 < rootDiameter / 8 :=
    SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_sq_lt targetPositive
  rw [prepared_diagonalSq segment parameter inside owner
    rootDiameterPositive]
  calc
    8 * radius ^ 2 ≤ 8 * diameterCap ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe
        (by decide)
    _ < 8 * (rootDiameter / 8) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide) capSquareLt
    _ = rootDiameter := by
      calc
        8 * (rootDiameter / 8) = (rootDiameter / 8) * 8 :=
          Fraction.Field.mul_comm _ _
        _ = rootDiameter :=
          Fraction.Field.div_mul_cancel_of_ne rootDiameter 8
            (by decide)

attribute [irreducible] prepared

end Purelib.Riemann.RootContinuation.RobustSquareRootPreparation

end
