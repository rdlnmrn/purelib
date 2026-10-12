module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value
public import Purelib.Curves.Hyperelliptic.Differentials.Wedge
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
import Purelib.Curves.Hyperelliptic.Sheets.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring

open Purelib.Integration.Polynomial.Gaussian

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration.Polynomial.Gaussian.Cell.Basic

open Purelib.Polynomial

open Purelib.Polynomial.Approximation.Gaussian.Evaluation

open Purelib.Polynomial.Ascending.Gaussian

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.Branches

open Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib.Riemann.Branches.PreparedSheetContinuation

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology

open Purelib.RootIsolation.SquareRoot.Clearance

@[expose] public section

/-!
# Uniform algebraic models on prepared continuation cells

This module connects the diameter-prepared square-root continuation with the
uniform integration semantics.  Every rational point query is answered from
the owner transported from the prepared left endpoint, so it cannot silently
choose the other square root by a fresh pointwise isolation.

The first constructor intentionally uses the zero polynomial.  It is a coarse
but honest local model: after one finite refinement of the differential CCL,
its displayed allowance pays for the complete enclosure and the zero-model
discrepancy.  Later constructors can replace this model by midpoint or Taylor
polynomials while reusing the owner-backed query machinery.
-/

namespace Purelib.Curves.Hyperelliptic.Differentials.PreparedModels

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

/-- Exact rational parameters, error allowances and quantitative bounds. -/
abbrev Coordinate := Fraction.Rational
/-- Exact Gaussian rational points and differential samples. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- The original finite dense Gaussian polynomial defining the curve radicand. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- A retained finite rational rectangular ambient. -/
abbrev Box := Rational.Box
/-- The original square-root continuation owner indexed by its exact radicand. -/
abbrev Owner := SquareRootContinuationChain.Owner
/-- A retained rational unit-interval endpoint of the original subdivision. -/
abbrev Endpoint := Subdivision.Endpoint
/-- The original prepared continuation step with its retained endpoint and root precision. -/
abbrev StepRequest := PreparedSheetContinuation.StepRequest
/-- A finite Gaussian integration cell with polynomial approximation and local error allowance. -/
abbrev CellModel := Cell.Basic.CellModel

/-- Residual-only denominator floor retained as one component of the coordinate-line estimate. -/
def residualDenominatorLower {polynomial : GaussianPolynomial}
  {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  min 1 (segment.clearanceBound / 4) / 8

/-- Dyadic magnitude floor obtained from the same positive radicand norm-square clearance, without extracting a
completed square root. -/
def magnitudeDenominatorLower {polynomial : GaussianPolynomial}
  {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  (Geometric.dyadicSquareRadius (segment.clearanceBound / 2) / 2) / 8

/-- A single positive denominator lower bound valid at every rational point of the certified coordinate line. The
residual component preserves the original proof, while the dyadic component uses the dominant rational coordinate
exposed by `Purelib.Riemann.Branches.SquareRootSheets.sampleNormLower`. -/
def denominatorLower {polynomial : GaussianPolynomial} {ambient :
  Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  max (residualDenominatorLower segment)
    (magnitudeDenominatorLower segment)

/-- The combined residual and dyadic line-clearance floor is strictly positive.

The positive original clearance supplies the residual minimum floor. The
unchanged maximum retains that floor alongside the dyadic magnitude estimate. -/
theorem denominatorLower_positive {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) :
    0 < denominatorLower segment :=
  (Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Basic.lt_min (by decide)
        (Fraction.Order.Field.div_pos_direct
          segment.clearanceBound_positive (by decide)))
      (by decide)).trans_le (Fraction.Order.Basic.le_max_left _ _)

/-- The retained line-clearance floor bounds each productive square-root denominator query on the certified line.

The original clearance bounds the radicand quadrance at that same point.
Both the residual and dyadic estimates lie below its retained sample norm floor. -/
theorem denominatorLower_le_point {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish value :
      Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (onLine : segment.OnCertifiedLine value) :
    denominatorLower segment <=
      Purelib.Riemann.Branches.SquareRootSheets.sampleNormLower
        (polynomial.eval value) / 8 := by
  have evaluationLower := segment.clearanceBound_le_eval_normSq onLine
  apply Fraction.Order.Basic.max_le
  · have divided : segment.clearanceBound / 4 <=
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval value) / 4 := by
      rw [Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.div_eq_mul_inv_direct]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        evaluationLower (by decide)
    have minimum := Fraction.Order.Basic.min_le_min (le_refl (1 :
      Coordinate)) divided
    have residualLower : residualDenominatorLower segment <=
        min 1 (Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval value) / 4) / 8 := by
      unfold residualDenominatorLower
      rw [Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.div_eq_mul_inv_direct]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        minimum (by decide)
    have sampledLower : min 1 (Data.Gaussian.Norm.Basic.normSq (polynomial.eval value) / 4) ≤
        SquareRootSheets.sampleNormLower (polynomial.eval value) := by
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      unfold SquareRootSheets.sampleNormLower
        SquareRootSheets.residualTarget
      exact Fraction.Order.Basic.le_max_left _ _
    exact residualLower.trans (by
      rw [Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.div_eq_mul_inv_direct]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        sampledLower (by decide))
  · have dyadicLower :=
      SquareRootSheets.dyadicSquareRadius_half_le_coordinateNormLower
        segment.clearanceBound_positive (by
            simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
              using evaluationLower)
    have halfLower :
        Geometric.dyadicSquareRadius
              (segment.clearanceBound / 2) / 2 <=
            SquareRootSheets.coordinateNormLower
              (polynomial.eval value) / 2 := by
      rw [Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.div_eq_mul_inv_direct]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        dyadicLower (by decide)
    have sampleLower :
        Geometric.dyadicSquareRadius
              (segment.clearanceBound / 2) / 2 <=
            SquareRootSheets.sampleNormLower
              (polynomial.eval value) := by
      exact halfLower.trans (Fraction.Order.Basic.le_max_right _ _)
    unfold magnitudeDenominatorLower
    rw [Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      sampleLower (by decide)

/-- A rational lower estimate for the radicand norm on one displayed clear segment. It is sampled at the segment's left
endpoint and pays the complete finite polynomial-variation budget across that segment. Unlike the coordinate-line
clearance inherited from the ambient box, this estimate can improve when a path is geometrically subdivided. -/
def segmentRadicandNormLower {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt 0)) / 2 -
    ClearSheetContinuation.variationBound segment 0 1

/-- Midpoint-sampled radicand lower estimate. Every parameter of the unit segment is at squared distance at most `1/4`
from the midpoint, so this pays only one quarter of the complete variation budget. -/
def segmentMidpointRadicandNormLower
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt (1 / 2))) / 2 -
    ClearSheetContinuation.variationBound segment 0 1 / 4

/-- Best of the left-endpoint and midpoint finite radicand estimates. -/
def segmentLocalRadicandNormLower
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  max (segmentRadicandNormLower segment)
    (segmentMidpointRadicandNormLower segment)

/-- Square-root-scaled denominator floor derived from the sampled local radicand bound. A nonpositive sampled bound
contributes zero, leaving the unconditional coordinate-line floor in control. When it is positive, the finite dyadic
square radius has the correct magnitude for the norm-square of the square root. -/
def segmentMagnitudeDenominatorLower
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  if _positive : 0 < segmentLocalRadicandNormLower segment then
    (Geometric.dyadicSquareRadius
      (segmentLocalRadicandNormLower segment / 2) / 2) / 8
  else
    0

/-- Denominator lower bound specialized to one geometrically refined clear segment. Taking the maximum with the
coordinate-line bound preserves unconditional positivity. The two sampled terms retain the residual-only estimate and
add the stronger square-root-scaled estimate when the local radicand bound is positive. -/
def segmentDenominatorLower {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  max
    (max (denominatorLower segment)
      (min 1 (segmentRadicandNormLower segment / 4) / 8))
    (segmentMagnitudeDenominatorLower segment)

/-- The local segment denominator floor is positive.

Its two unchanged maxima retain the positive original line-clearance floor
alongside both local endpoint and midpoint estimates. -/
theorem segmentDenominatorLower_positive
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) :
    0 < segmentDenominatorLower segment :=
  (denominatorLower_positive segment).trans_le
    ((Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_left _ _))

open Purelib.Data.Gaussian in
/-- The sampled endpoint radicand estimate bounds every displayed segment point.

The original endpoint quadrance pays the complete retained polynomial variation
budget. The supplied ambient containment and unit parameter bounds certify that budget. -/
theorem segmentRadicandNormLower_le_point
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    segmentRadicandNormLower segment <=
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt parameter)) := by
  have differenceBound :
      Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt 0) -
            polynomial.eval (segment.pointAt parameter)) <=
        ClearSheetContinuation.variationBound segment 0 1 :=
    (ClearSheetContinuation.evaluation_variation_le segment
      within 0 parameter (by decide) inside).trans
        (ClearSheetContinuation.variationBound_le_of_between
          segment inside.1 inside.2)
  have triangle :=
    Data.Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub
      (polynomial.eval (segment.pointAt 0))
      (polynomial.eval (segment.pointAt parameter))
  have rearranged :
      Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt 0)) / 2 -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt 0) - polynomial.eval (segment.pointAt parameter)) <=
      Data.Gaussian.Norm.Basic.normSq (polynomial.eval (segment.pointAt parameter)) := by
    calc
      _ = (Data.Gaussian.Norm.Basic.normSq
              (polynomial.eval (segment.pointAt 0)) / 2 -
            Data.Gaussian.Norm.Basic.normSq (polynomial.eval (segment.pointAt parameter))) +
          (Data.Gaussian.Norm.Basic.normSq (polynomial.eval (segment.pointAt parameter)) -
            Data.Gaussian.Norm.Basic.normSq
              (polynomial.eval (segment.pointAt 0) - polynomial.eval (segment.pointAt parameter))) := by ring1
      _ <= Data.Gaussian.Norm.Basic.normSq
              (polynomial.eval (segment.pointAt 0) - polynomial.eval (segment.pointAt parameter)) +
          (Data.Gaussian.Norm.Basic.normSq (polynomial.eval (segment.pointAt parameter)) -
            Data.Gaussian.Norm.Basic.normSq
              (polynomial.eval (segment.pointAt 0) - polynomial.eval (segment.pointAt parameter))) :=
        Fraction.Order.Arithmetic.add_le_add_direct triangle le_rfl
      _ = _ := by ring1
  unfold segmentRadicandNormLower
  exact (Fraction.Order.Arithmetic.sub_le_sub_left_direct differenceBound _).trans rearranged

/-- Midpoint-to-parameter polynomial variation is bounded by one quarter of the complete segment variation.

Every supplied unit-interval parameter is within one half of the midpoint.
The same retained nonnegative Lipschitz slope scales this squared-distance bound. -/
theorem variationBound_midpoint_le_quarter
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    Purelib.Riemann.Branches.ClearSheetContinuation.variationBound segment (1 / 2)
        parameter <=
      Purelib.Riemann.Branches.ClearSheetContinuation.variationBound segment 0 1 / 4 := by
  have squareLe : ((1 / 2 : Coordinate) - parameter) ^ 2 <= 1 / 4 :=
    by
    by_cases lowerHalf : parameter <= (1 / 2 : Coordinate)
    · have differenceNonnegative :
          (0 : Coordinate) <= 1 / 2 - parameter :=
        Fraction.Order.Arithmetic.sub_nonneg_direct lowerHalf
      have differenceLe : 1 / 2 - parameter <= (1 / 2 : Coordinate) :=
        by
          have translated := Fraction.Order.Arithmetic.sub_le_sub_left_direct inside.1
            (1 / 2 : Coordinate)
          exact translated.trans_eq (by ring1)
      exact (Fraction.Order.Arithmetic.pow_le_pow_direct
        differenceNonnegative differenceLe 2).trans_eq (by decide)
    · have halfLe : (1 / 2 : Coordinate) <= parameter :=
        (Fraction.Order.Arithmetic.lt_of_not_ge_direct lowerHalf).le
      have differenceNonnegative :
          (0 : Coordinate) <= parameter - 1 / 2 :=
        Fraction.Order.Arithmetic.sub_nonneg_direct halfLe
      have differenceLe : parameter - 1 / 2 <= (1 / 2 : Coordinate) :=
        by
        calc
          parameter - 1 / 2 <= 1 - 1 / 2 :=
            Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2 _
          _ = 1 / 2 := by decide
      calc
        (1 / 2 - parameter) ^ 2 = (parameter - 1 / 2) ^ 2 := by ring1
        _ <= (1 / 2 : Coordinate) ^ 2 :=
          Fraction.Order.Arithmetic.pow_le_pow_direct
            differenceNonnegative differenceLe 2
        _ = 1 / 4 := by decide
  unfold ClearSheetContinuation.variationBound
  calc
    Dense.Gaussian.Bounds.Box.denseLipschitzBound
          (ClearSheetContinuation.segmentPolynomial segment)
          ClearSheetContinuation.parameterAmbient *
        (1 / 2 - parameter) ^ 2 <=
      Dense.Gaussian.Bounds.Box.denseLipschitzBound
          (ClearSheetContinuation.segmentPolynomial segment)
          ClearSheetContinuation.parameterAmbient * (1 / 4) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos
          (ClearSheetContinuation.segmentPolynomial segment)
          ClearSheetContinuation.parameterAmbient).le
    _ = Dense.Gaussian.Bounds.Box.denseLipschitzBound
          (ClearSheetContinuation.segmentPolynomial segment)
          ClearSheetContinuation.parameterAmbient *
            (0 - 1) ^ 2 / 4 := by
      rw [show ((0 : Coordinate) - 1) ^ 2 = 1 by decide]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1

open Purelib.Data.Gaussian in
/-- The midpoint radicand estimate bounds every displayed segment point.

The retained midpoint quadrance pays one quarter of the original variation
budget, under the supplied ambient containment and unit parameter bounds. -/
theorem segmentMidpointRadicandNormLower_le_point
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    segmentMidpointRadicandNormLower segment <=
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt parameter)) := by
  have midpointInside :
      (0 : Coordinate) <= 1 / 2 ∧ (1 / 2 :
        Coordinate) <= 1 := by decide
  have differenceBound :
      Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt (1 / 2)) -
            polynomial.eval (segment.pointAt parameter)) <=
        ClearSheetContinuation.variationBound segment 0 1 / 4 :=
    (ClearSheetContinuation.evaluation_variation_le segment
      within (1 / 2) parameter midpointInside inside).trans
        (variationBound_midpoint_le_quarter segment parameter inside)
  have triangle :=
    Data.Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub
      (polynomial.eval (segment.pointAt (1 / 2)))
      (polynomial.eval (segment.pointAt parameter))
  have rearranged :
      Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt (1 / 2))) / 2 -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt (1 / 2)) - polynomial.eval (segment.pointAt parameter)) <=
      Data.Gaussian.Norm.Basic.normSq (polynomial.eval (segment.pointAt parameter)) := by
    calc
      _ = (Data.Gaussian.Norm.Basic.normSq
              (polynomial.eval (segment.pointAt (1 / 2))) / 2 -
            Data.Gaussian.Norm.Basic.normSq (polynomial.eval (segment.pointAt parameter))) +
          (Data.Gaussian.Norm.Basic.normSq (polynomial.eval (segment.pointAt parameter)) -
            Data.Gaussian.Norm.Basic.normSq
              (polynomial.eval (segment.pointAt (1 / 2)) - polynomial.eval (segment.pointAt parameter))) := by ring1
      _ <= Data.Gaussian.Norm.Basic.normSq
              (polynomial.eval (segment.pointAt (1 / 2)) - polynomial.eval (segment.pointAt parameter)) +
          (Data.Gaussian.Norm.Basic.normSq (polynomial.eval (segment.pointAt parameter)) -
            Data.Gaussian.Norm.Basic.normSq
              (polynomial.eval (segment.pointAt (1 / 2)) - polynomial.eval (segment.pointAt parameter))) :=
        Fraction.Order.Arithmetic.add_le_add_direct triangle le_rfl
      _ = _ := by ring1
  unfold segmentMidpointRadicandNormLower
  exact (Fraction.Order.Arithmetic.sub_le_sub_left_direct differenceBound _).trans rearranged

/-- The best local sample remains a valid lower bound throughout the segment.

Both retained endpoint and midpoint estimates bound the same pointwise
radicand quadrance. Their unchanged maximum therefore retains that bound. -/
theorem segmentLocalRadicandNormLower_le_point
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    segmentLocalRadicandNormLower segment <=
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt parameter)) := by
  unfold segmentLocalRadicandNormLower
  exact Fraction.Order.Basic.max_le
    (segmentRadicandNormLower_le_point segment within parameter
      inside)
    (segmentMidpointRadicandNormLower_le_point segment within
      parameter inside)

/-- The locally sampled denominator floor bounds every productive segment query.

The same original radicand sample controls the line, endpoint and positive
local dyadic floors; both unchanged maxima combine their certified bounds. -/
theorem segmentDenominatorLower_le_point
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    segmentDenominatorLower segment <=
      Purelib.Riemann.Branches.SquareRootSheets.sampleNormLower
        (polynomial.eval (segment.pointAt parameter)) / 8 := by
  apply Fraction.Order.Basic.max_le
  · apply Fraction.Order.Basic.max_le
    · exact denominatorLower_le_point segment
        (segment.pointAt_onCertifiedLine parameter inside)
    · have radicandLower := segmentRadicandNormLower_le_point segment
        within
        parameter inside
      have quarterLower : segmentRadicandNormLower segment / 4 <=
          Data.Gaussian.Norm.Basic.normSq
              (polynomial.eval (segment.pointAt parameter)) / 4 := by
        rw [Fraction.Field.div_eq_mul_inv_direct,
          Fraction.Field.div_eq_mul_inv_direct]
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          radicandLower (by decide)
      have sampledLower :
          min 1 (segmentRadicandNormLower segment / 4) <=
            SquareRootSheets.sampleNormLower
              (polynomial.eval (segment.pointAt parameter)) := by
        unfold SquareRootSheets.sampleNormLower
          SquareRootSheets.residualTarget
        rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at quarterLower
        exact (Fraction.Order.Basic.min_le_min le_rfl quarterLower).trans (Fraction.Order.Basic.le_max_left _ _)
      rw [Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.div_eq_mul_inv_direct]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        sampledLower (by decide)
  · have radicandLower := segmentLocalRadicandNormLower_le_point
      segment within
      parameter inside
    by_cases positive : 0 < segmentLocalRadicandNormLower segment
    · have dyadicLower :=
        SquareRootSheets.dyadicSquareRadius_half_le_coordinateNormLower
          positive (by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using radicandLower)
      have halfLower :
          Geometric.dyadicSquareRadius
                (segmentLocalRadicandNormLower segment / 2) / 2 <=
              SquareRootSheets.coordinateNormLower
                (polynomial.eval (segment.pointAt parameter)) / 2 := by
        rw [Fraction.Field.div_eq_mul_inv_direct,
          Fraction.Field.div_eq_mul_inv_direct]
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          dyadicLower (by decide)
      have sampleLower :
          Geometric.dyadicSquareRadius
                (segmentLocalRadicandNormLower segment / 2) / 2 <=
              SquareRootSheets.sampleNormLower
                (polynomial.eval (segment.pointAt parameter)) :=
        halfLower.trans (Fraction.Order.Basic.le_max_right _ _)
      rw [segmentMagnitudeDenominatorLower, dif_pos positive,
        Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.div_eq_mul_inv_direct]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        sampleLower (by decide)
    · rw [segmentMagnitudeDenominatorLower, dif_neg positive]
      exact (denominatorLower_positive segment).le.trans
        (denominatorLower_le_point segment
          (segment.pointAt_onCertifiedLine parameter inside))

/-- The restricted geometric edge represented by one prepared move. -/
def edge {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (request : StepRequest) :
    ClearPath.ClearSegment curve.polynomial ambient
      (segment.pointAt left.parameter)
      (segment.pointAt request.endpoint.parameter) :=
  segment.restrict within left.parameter request.endpoint.parameter
    left.inside request.endpoint.inside

/-- The division-ready square-root certificate returned by one inherited point query. Keeping this certificate separate
from the algebraic-sheet package makes operational transport proofs normalize only the root data they actually compare.
-/
def rootAt {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CertifiedSquareRoot.Certificate
      (curve.polynomial.eval (segment.pointAt
        (PreparedSheetContinuation.parameterAt left request
          fraction))) :=
  (PreparedSheetContinuation.transportedAt segment within left
    owner request ordered small fraction inside).certificate
      (segment.pointAt_eval_ne_zero
        (PreparedSheetContinuation.parameterAt left request
          fraction)
        (PreparedSheetContinuation.parameterAt_inside left request
          ordered fraction inside))

/-- The same inherited root query using the prepared source already cached in the accepted subdivision node. Its proof
input remains the canonical smallness theorem, while its executable owner is reused rather than rebuilt. -/
def rootAtCached {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CertifiedSquareRoot.Certificate
      (curve.polynomial.eval (segment.pointAt
        (PreparedSheetContinuation.parameterAt left request
          fraction))) := by
  let parameter :=
    PreparedSheetContinuation.parameterAt left request fraction
  let parameterNonzero := segment.pointAt_eval_ne_zero parameter
    (PreparedSheetContinuation.parameterAt_inside left request
      ordered fraction inside)
  have pointSmall : Data.Gaussian.Norm.Basic.normSq
      (curve.polynomial.eval (segment.pointAt left.parameter) -
        curve.polynomial.eval (segment.pointAt parameter)) <
        cached.preparedOwner.track.initial.clearance.bound := by
    rw [cached.preparedOwner_eq]
    exact PreparedSheetContinuation.pointNormSmall segment within
      left owner request ordered small fraction inside
  exact
    (ExactQuadraticOwnerClearance.reservedTransport
      cached.preparedOwner parameterNonzero pointSmall
        (PreparedSheetContinuation.transportReserve segment left
          request)).certificate parameterNonzero

/-- At the right endpoint, a query through the cached prepared owner has the same productive root name as the accepted
edge's transported endpoint owner. -/
theorem rootAtCached_one_name_eq_transportedRootName {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (inside : (0 : Coordinate) <= 1 ∧ (1 :
      Coordinate) <= 1) :
    (rootAtCached curve segment within left owner request
      cached ordered small
      1 inside).value.name =
      PreparedSheetContinuation.transportedRootName segment within
        left owner request small := by
  rw [CachedSource.eq_canonical cached]
  unfold rootAtCached
    PreparedSheetContinuation.transportedRootName
    PreparedSheetContinuation.transported
  apply
    PreparedSheetContinuation.reservedTransportRootName_proof_irrel

/-- At the left endpoint, a query through the cached prepared owner has the same productive root name as the canonical
zero-displacement query. -/
theorem rootAtCached_zero_name_eq_zeroMoveRootName {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (inside : (0 : Coordinate) <= 0 ∧ (0 :
      Coordinate) <= 1) :
    (rootAtCached curve segment within left owner request
      cached ordered small
      0 inside).value.name =
      PreparedSheetContinuation.zeroMoveRootName segment left owner
        request := by
  rw [CachedSource.eq_canonical cached]
  unfold rootAtCached
    PreparedSheetContinuation.zeroMoveRootName
  apply
    PreparedSheetContinuation.reservedTransportRootName_proof_irrel

/-- The productive name of the inherited point-query root. This nondependent projection is the lightweight interface
used by operational boundary comparisons. -/
@[irreducible] def rootNameAt {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Gaussian.Name.Basic.Named :=
  (rootAt curve segment within left owner request ordered small
    fraction
    inside).value.name

/-- A local point-query name is exactly the owner root obtained by the direct advance from the prepared left occurrence.
-/
theorem rootNameAt_eq_directOwnerRootName {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    rootNameAt curve segment within left owner request ordered
      small fraction
        inside =
      SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero
          (PreparedSheetContinuation.parameterAt left request
            fraction)
          (PreparedSheetContinuation.parameterAt_inside left
            request ordered fraction inside))
        (ExactQuadraticOwnerClearance.reservedTransport
          (PreparedSheetContinuation.prepared segment left owner
            request)
          (segment.pointAt_eval_ne_zero
            (PreparedSheetContinuation.parameterAt left request
              fraction)
            (PreparedSheetContinuation.parameterAt_inside left
              request ordered fraction inside))
          (PreparedSheetContinuation.pointNormSmall segment within
            left owner request ordered small fraction inside)
          (PreparedSheetContinuation.transportReserve segment left
            request)) := by
  unfold PreparedModels.rootNameAt rootAt
  rw [PreparedSheetContinuation.transportedAt_eq_directAdvance]
  rfl

/-- At the right endpoint, the generic point-query name is definitionally the name of the transported endpoint owner;
only the rational parameter presentation differs. -/
theorem rootNameAt_one_eq_transportedRootName {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (inside : (0 : Coordinate) <= 1 ∧ (1 :
      Coordinate) <= 1) :
    rootNameAt curve segment within left owner request ordered
      small 1 inside =
      PreparedSheetContinuation.transportedRootName segment within
        left owner request small := by
  unfold PreparedModels.rootNameAt rootAt
  unfold PreparedSheetContinuation.transportedAt
    PreparedSheetContinuation.transportedRootName
    PreparedSheetContinuation.transported
  rfl

/-- At the left endpoint, the generic point-query name is the explicit zero-displacement move from the prepared source
owner. -/
theorem rootNameAt_zero_eq_zeroMoveRootName {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (inside : (0 : Coordinate) <= 0 ∧ (0 :
      Coordinate) <= 1) :
    rootNameAt curve segment within left owner request ordered
      small 0 inside =
      PreparedSheetContinuation.zeroMoveRootName segment left owner
        request := by
  unfold PreparedModels.rootNameAt rootAt
    PreparedSheetContinuation.transportedAt
    PreparedSheetContinuation.transportedQuery
    PreparedSheetContinuation.zeroMoveRootName
  rfl

/-- Algebraic sheet value at a queried local parameter, inherited from the prepared source owner by one Rouché
transport. -/
def sheetValueAt {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (_differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Sheets.Basic.AlgebraicSheetValue curve ((edge curve segment within
      left request).pointAt
      fraction) := by
  let originalParameter :=
    PreparedSheetContinuation.parameterAt left request fraction
  let originalPoint := segment.pointAt originalParameter
  let point := (edge curve segment within left request).pointAt
    fraction
  have pointEqual : originalPoint = point :=
    PreparedSheetContinuation.pointAt_parameterAt
      segment within left request fraction
  let root := rootAt curve segment within left owner request ordered
    small
    fraction inside
  exact
    { value := root.value
      apart := root.apart
      sheet := sheet
      curveEquation :=
        NamedEquivalent.trans
          (by
            rw [← pointEqual]
            exact root.square)
          (NamedEquivalent.symm
            (Horner.polynomialEval_exact
              curve.polynomial point)) }

/-- Algebraic sheet value backed by the prepared source cached in the accepted subdivision node. -/
def sheetValueAtCached {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (_differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Sheets.Basic.AlgebraicSheetValue curve ((edge curve segment within
      left request).pointAt
      fraction) := by
  let originalParameter :=
    PreparedSheetContinuation.parameterAt left request fraction
  let originalPoint := segment.pointAt originalParameter
  let point := (edge curve segment within left request).pointAt
    fraction
  have pointEqual : originalPoint = point :=
    PreparedSheetContinuation.pointAt_parameterAt
      segment within left request fraction
  let root := rootAtCached curve segment within left owner request
    cached
    ordered small fraction inside
  exact
    { value := root.value
      apart := root.apart
      sheet := sheet
      curveEquation :=
        NamedEquivalent.trans
          (by
            rw [← pointEqual]
            exact root.square)
          (NamedEquivalent.symm
            (Horner.polynomialEval_exact
              curve.polynomial point)) }

/-- The cached inherited sheet query retains exactly one eighth of the original radicand sample lower bound. -/
@[simp] theorem sheetValueAtCached_apart_lowerSq {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (sheetValueAtCached curve differential segment within left owner
      request
      cached ordered small sheet fraction inside).apart.certificate.lowerSq =
      SquareRootSheets.sampleNormLower
        (curve.polynomial.eval (segment.pointAt
          (PreparedSheetContinuation.parameterAt left request
            fraction))) / 8 := by
  rfl

/-- Every candidate of a cached sheet query remains in the canonical prepared source box specified by the accepted edge.
-/
theorem sheetValueAtCached_candidate_in_prepared_box {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (sheetValueAtCached curve differential segment within
      left owner
      request cached ordered small sheet fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (sheetValueAtCached curve differential segment within
      left
      owner request cached ordered small sheet fraction inside).value.name.process.Possible
        state candidate) :
    (PreparedSheetContinuation.prepared segment left owner
      request).track.initial.box.Contains candidate := by
  let parameter :=
    PreparedSheetContinuation.parameterAt left request fraction
  let parameterNonzero := segment.pointAt_eval_ne_zero parameter
    (PreparedSheetContinuation.parameterAt_inside left request
      ordered fraction inside)
  have pointSmall : Data.Gaussian.Norm.Basic.normSq
      (curve.polynomial.eval (segment.pointAt left.parameter) -
        curve.polynomial.eval (segment.pointAt parameter)) <
        cached.preparedOwner.track.initial.clearance.bound := by
    rw [cached.preparedOwner_eq]
    exact PreparedSheetContinuation.pointNormSmall segment within
      left owner request ordered small fraction inside
  let inherited := ExactQuadraticOwnerClearance.reservedTransport
    cached.preparedOwner parameterNonzero pointSmall
      (PreparedSheetContinuation.transportReserve segment left
        request)
  have candidateInside : inherited.track.initial.box.Contains candidate := by
    apply inherited.certificate_candidate_in_initial_box parameterNonzero state
    simpa only [sheetValueAtCached,
      rootAtCached, inherited, parameter,
      parameterNonzero, pointSmall] using possible
  have inheritedRefines : inherited.track.initial.box.Refines
      cached.preparedOwner.track.initial.box :=
    ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines
      cached.preparedOwner parameterNonzero pointSmall
        (PreparedSheetContinuation.transportReserve segment left
          request)
  have cachedContains := inheritedRefines.contains candidateInside
  rw [cached.preparedOwner_eq] at cachedContains
  exact cachedContains

/-- The algebraic sheet value retains the exact inherited root-query value. -/
@[simp] theorem sheetValueAt_value {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (sheetValueAt curve differential segment within left owner request
      ordered
      small sheet fraction inside).value =
        (rootAt curve segment within left owner request ordered small
          fraction
          inside).value := by
  rfl

/-- The inherited sheet query retains exactly one eighth of the original radicand sample lower bound. -/
@[simp] theorem sheetValueAt_apart_lowerSq {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (sheetValueAt curve differential segment within left owner request
      ordered
      small sheet fraction inside).apart.certificate.lowerSq =
      SquareRootSheets.sampleNormLower
        (curve.polynomial.eval (segment.pointAt
          (PreparedSheetContinuation.parameterAt left request
            fraction))) / 8 := by
  rfl

/-- Every finite denominator candidate returned at any rational point of an accepted edge lies in the single prepared
source root box. This is stronger than closeness of the displayed endpoint anchors: it controls all later CCL
refinements used by an integration query. -/
theorem sheetValueAt_candidate_in_prepared_box {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (sheetValueAt curve differential segment within left
      owner
      request ordered small sheet fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (sheetValueAt curve differential segment within left
      owner
      request ordered small sheet fraction inside).value.name.process.Possible
        state candidate) :
    (PreparedSheetContinuation.prepared segment left owner
      request).track.initial.box.Contains
      candidate := by
  let parameter :=
    PreparedSheetContinuation.parameterAt left request fraction
  let inherited := PreparedSheetContinuation.transportedAt
    segment within left owner request ordered small fraction inside
  have parameterNonzero : curve.polynomial.eval
      (segment.pointAt parameter) ≠ 0 :=
    segment.pointAt_eval_ne_zero parameter
      (PreparedSheetContinuation.parameterAt_inside left request
        ordered fraction inside)
  have candidateInside : inherited.track.initial.box.Contains candidate :=
    inherited.certificate_candidate_in_initial_box parameterNonzero state
      possible
  have inheritedRefines : inherited.track.initial.box.Refines
      (PreparedSheetContinuation.prepared segment left owner
        request).track.initial.box :=
    PreparedSheetContinuation.transportedAt_initial_box_refines
      segment within left owner request ordered small fraction inside
  exact inheritedRefines.contains candidateInside

/-- The owner-backed coherent coefficient `x^k/y` at one queried point. -/
def coefficientAt {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (_sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Coherent.CoherentNamed :=
  let point := (edge curve segment within left request).pointAt
    fraction
  let root := rootAt curve segment within left owner request ordered
    small
    fraction inside
  Value.differentialValue differential point root.value root.apart

/-- Owner-backed coefficient using the already cached prepared source. -/
def coefficientAtCached {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (_sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Coherent.CoherentNamed :=
  let point := (edge curve segment within left request).pointAt
    fraction
  let root := rootAtCached curve segment within left owner request
    cached
    ordered small fraction inside
  Value.differentialValue differential point root.value root.apart

/-- Local antisymmetric product of two standard differentials on one accepted prepared edge. The root owner and sheet
continuation are shared before the two differential exponents are evaluated. -/
def wedgeCoefficientAt {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Coherent.CoherentNamed :=
  let point := (edge curve segment within left request).pointAt
    fraction
  let root := sheetValueAt curve leftDifferential segment within left
    owner
    request ordered small sheet fraction inside
  Wedge.differentialWedgeCoefficient leftDifferential rightDifferential point
    root.value root.apart

/-- Every finite prepared chart computes zero for the wedge of two hyperelliptic basis differentials. This is the local
holomorphic input for a future cellwise Stokes assembly, now tied to the actual owner-backed root used by the
integration model. -/
def wedgeCoefficientAt_zero {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Gaussian.Equivalence.NamedEquivalent
      (wedgeCoefficientAt curve leftDifferential
        rightDifferential segment
        within left owner request ordered small sheet fraction inside).name
      (Coherence.exact 0).name := by
  unfold wedgeCoefficientAt
  exact Wedge.differentialWedgeCoefficient_zero leftDifferential rightDifferential
    ((edge curve segment within left request).pointAt fraction)
    (sheetValueAt curve leftDifferential segment within left owner
      request
      ordered small sheet fraction inside).value
    (sheetValueAt curve leftDifferential segment within left owner
      request
      ordered small sheet fraction inside).apart

set_option genInjectivity false in
/-- A uniform rational bound on owner-backed differential process centers along one edge.

The curve, differential, clear segment, left owner and prepared continuation
request index the same pointwise processes. Their retained center readings
obey the supplied nonnegative bound at every rational unit parameter. -/
structure CoefficientBound {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) where
  /-- The retained uniform upper bound for every original owner-backed coefficient center. -/ bound :
    Coordinate
  /-- The retained coefficient-center upper bound is nonnegative. -/ boundNonnegative : 0 <= bound
  /-- Every rational unit-interval query of the original owner-backed coefficient process satisfies the same retained
    bound. -/ centerBound_le : forall fraction : Coordinate,
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) ->
    (coefficientAt curve differential segment within left owner
      request
      ordered small sheet fraction inside).name.process.centerBound <= bound

constructive_injectivity CoefficientBound

/-- The coefficient bound computed solely from the fixed base ambient and the line's positive polynomial clearance. -/
def automaticBoundValue {genus : Nat}
    (differential : Differentials.Basic.Differential genus)
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  ambient.normSqBound ^ differential.exponent / denominatorLower
    segment

/-- The ambient-power numerator divided by the retained positive denominator floor is nonnegative. -/
theorem automaticBoundValue_nonnegative {genus : Nat}
    (differential : Differentials.Basic.Differential genus)
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) :
    0 <= automaticBoundValue differential segment :=
  Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.pow_nonneg_direct
      ambient.normSqBound_nonneg differential.exponent)
    (denominatorLower_positive segment).le

/-- Every prepared owner-backed differential cell has an automatic finite uniform coefficient bound. Its denominator
estimate comes from the fixed line clearance, not from a pointwise root choice or a completed minimum. -/
def automaticCoefficientBound {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) :
    CoefficientBound curve differential segment within left owner
      request
      ordered small sheet where
  bound := automaticBoundValue differential segment
  boundNonnegative := automaticBoundValue_nonnegative differential
    segment
  centerBound_le := by
    intro fraction inside
    let parameter :=
      PreparedSheetContinuation.parameterAt left request fraction
    let originalPoint := segment.pointAt parameter
    let localPoint := (edge curve segment within left request).pointAt
      fraction
    let sheetValue := sheetValueAt curve differential segment within
      left owner
      request ordered small sheet fraction inside
    have parameterInside :=
      PreparedSheetContinuation.parameterAt_inside left request
        ordered fraction inside
    have pointEqual : originalPoint = localPoint :=
      PreparedSheetContinuation.pointAt_parameterAt
        segment within left request fraction
    have localContains : ambient.Contains localPoint := by
      rw [← pointEqual]
      exact segment.pointAt_contains within parameter parameterInside
    have pointNormBound :
        Data.Gaussian.Norm.Basic.normSq localPoint <=
          ambient.normSqBound :=
      ambient.normSq_le_normSqBound localContains
    have numeratorBound :
        Data.Gaussian.Norm.Basic.normSq localPoint ^
            differential.exponent <=
          ambient.normSqBound ^ differential.exponent :=
      Fraction.Order.Arithmetic.pow_le_pow_direct
        (Data.Gaussian.Norm.Basic.normSq_nonneg localPoint)
        pointNormBound differential.exponent
    have denominatorBound : denominatorLower segment <=
        sheetValue.apart.certificate.lowerSq := by
      rw [sheetValueAt_apart_lowerSq]
      exact denominatorLower_le_point segment
        (segment.pointAt_onCertifiedLine parameter parameterInside)
    have actualPositive : 0 < sheetValue.apart.certificate.lowerSq :=
      (denominatorLower_positive segment).trans_le denominatorBound
    change
      (Value.differentialValue differential localPoint sheetValue.value
        sheetValue.apart).name.process.centerBound <=
          automaticBoundValue differential segment
    rw [Value.differentialValue_centerBound]
    unfold automaticBoundValue
    calc
      Data.Gaussian.Norm.Basic.normSq localPoint ^
            differential.exponent /
            sheetValue.apart.certificate.lowerSq <=
          ambient.normSqBound ^ differential.exponent /
            sheetValue.apart.certificate.lowerSq := by
        rw [Fraction.Field.div_eq_mul_inv_direct,
          Fraction.Field.div_eq_mul_inv_direct]
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          numeratorBound
          (Fraction.Order.Field.inv_pos_direct actualPositive).le
      _ <= ambient.normSqBound ^ differential.exponent /
            denominatorLower segment :=
        Fraction.Order.Field.div_le_div_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            ambient.normSqBound_nonneg differential.exponent)
          (denominatorLower_positive segment) denominatorBound

/-- Coarse fixed allowance used by the honest zero-polynomial model. -/
def zeroAllowance {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {ambient : Box} {start finish :
      Gaussian}
    {segment : ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter))}
    {request : StepRequest}
    {ordered : left.parameter <= request.endpoint.parameter}
    {small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound}
    {sheet : Fin 2}
    (coefficientBound : CoefficientBound curve differential segment
      within
      left owner request ordered small sheet) : Coordinate :=
  12 + 4 * coefficientBound.bound

/-- The zero-model allowance is nonnegative for the retained nonnegative coefficient bound. -/
theorem zeroAllowance_nonnegative {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {ambient : Box} {start finish :
      Gaussian}
    {segment : ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter))}
    {request : StepRequest}
    {ordered : left.parameter <= request.endpoint.parameter}
    {small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound}
    {sheet : Fin 2}
    (coefficientBound : CoefficientBound curve differential segment
      within
      left owner request ordered small sheet) :
    0 <= zeroAllowance coefficientBound :=
  add_nonneg (by decide)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      coefficientBound.boundNonnegative)

/-- The displayed integration cell for the coarse uniform model. -/
def zeroModel {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {ambient : Box} {start finish :
      Gaussian}
    {segment : ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter))}
    {request : StepRequest}
    {ordered : left.parameter <= request.endpoint.parameter}
    {small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound}
    {sheet : Fin 2}
    (coefficientBound : CoefficientBound curve differential segment
      within
      left owner request ordered small sheet) : CellModel :=
  { start := segment.pointAt left.parameter
    finish := segment.pointAt request.endpoint.parameter
    polynomial := Ascending.Gaussian.Basic.zero
    localAllowance := zeroAllowance coefficientBound
    localAllowance_nonneg := zeroAllowance_nonnegative
      coefficientBound
    observations := [] }

/-- Refine the original coherent coefficient name once to the positive unit target. -/
def unitState (value : Coherent.CoherentNamed) :
    value.name.process.State :=
  value.name.process.refine value.name.state 1 (by decide)

/-- Read the retained witness at the original coefficient name unit-target refinement. -/
def unitReading (value : Coherent.CoherentNamed) : Gaussian :=
  (value.name.process.witness (unitState value)).val

/-- The unit-target witness squared norm is at most twice one plus the retained coefficient-center bound. -/
private theorem reading_norm_le
    (value : Coherent.CoherentNamed)
    (bound : Coordinate)
    (centerBound : value.name.process.centerBound <= bound) :
    Data.Gaussian.Norm.Basic.normSq (unitReading value) <=
      2 * (1 + bound) := by
  let state := unitState value
  let reading := unitReading value
  let ball := value.name.process.ball state
  have possible : value.name.process.Possible state reading :=
    (value.name.process.witness state).property
  have inside : ball.Contains reading := value.name.process.possible_inside possible
  have radiusSmall : ball.radiusSq < 1 :=
    value.name.process.accurate value.name.state 1 (by decide)
  have identity : reading = (reading - ball.center) + ball.center := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  change Data.Gaussian.Norm.Basic.normSq reading <= _
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (inside.trans radiusSmall.le)
        (value.name.process.center_bounded state |>.trans centerBound))
      (by decide))

/-- The coarse zero model has uniform semantics from the original continued owner.

Each rational cell query retains the original sheet value, coefficient name
and unit-target reading. Its nonnegative bound pays the same cached zero-model error. -/
def uniformZeroCertificate {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish :
      Gaussian}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2)
    (coefficientBound : CoefficientBound curve differential segment
      within
      left owner request ordered small sheet) :
    Basis.UniformCellCertificate curve differential
      (ClearSegment.liftOnSheet sheet (edge curve segment within left
        request))
      (zeroModel coefficientBound) where
  query := by
    intro fraction lower upper
    let inside : (0 : Coordinate) <= fraction ∧ fraction <= 1 :=
      ⟨lower, upper⟩
    let point := (edge curve segment within left request).pointAt
      fraction
    let sheetValue := sheetValueAt curve differential segment within
      left owner
      request ordered small sheet fraction inside
    let coefficient := coefficientAt curve differential segment within
      left
      owner request ordered small sheet fraction inside
    let state := unitState coefficient
    let reading := unitReading coefficient
    let observation : Cell.Basic.LocalObservation
        (zeroModel coefficientBound).polynomial
        (zeroModel coefficientBound).localAllowance :=
      { parameter := fraction
        integrandReading := reading
        error := reading
        decomposition := by
          change reading -
              Evaluation.eval
                Ascending.Gaussian.Basic.zero ⟨fraction, 0⟩ = reading
          rw [Evaluation.eval_zero]
          apply Data.Gaussian.Basic.ext <;>
            simp only [Purelib.Data.Gaussian.Basic.sub_re,
              Purelib.Data.Gaussian.Basic.sub_im,
              Purelib.Data.Gaussian.Basic.zero_re,
              Purelib.Data.Gaussian.Basic.zero_im] <;> ring1
        error_le := by
          have readingBound := reading_norm_le coefficient
            coefficientBound.bound
            (coefficientBound.centerBound_le fraction inside)
          rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at readingBound
          change Data.Gaussian.Basic.Canonical.normSq reading <=
            zeroAllowance coefficientBound
          exact readingBound.trans (by
            unfold zeroAllowance
            apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
            have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
              (by decide : (0 : Coordinate) <= 2)
              coefficientBound.boundNonnegative
            calc
              (0 : Coordinate) = 0 + 0 := by ring1
              _ <= 10 + 2 * coefficientBound.bound :=
                Fraction.Order.Arithmetic.add_le_add_direct (by decide) nonnegative
              _ = (12 + 4 * coefficientBound.bound) - 2 * (1 + coefficientBound.bound) := by ring1) }
    let algebraic : Basis.AlgebraicObservation curve differential
        (ClearSegment.liftOnSheet sheet (edge curve segment within
          left request))
        (zeroModel coefficientBound) observation :=
      { point := point
        point_eq := by
          apply Data.Gaussian.Basic.ext <;>
            simp only [point, Cell.Basic.CellModel.observationPoint,
              zeroModel,
              CellModel.displacement,
              ClearSegment.pointAt,
              Purelib.Data.Gaussian.Scale.scale_re, Purelib.Data.Gaussian.Scale.scale_im,
              Purelib.Data.Gaussian.Basic.add_re,
              Purelib.Data.Gaussian.Basic.add_im,
              Purelib.Data.Gaussian.Basic.sub_re,
              Purelib.Data.Gaussian.Basic.sub_im] <;> ring1
        sheetValue := sheetValue
        chosenSheet_eq := rfl
        readingState := state
        readingPossible := by
          change coefficient.name.process.Possible state reading
          exact (coefficient.name.process.witness state).property }
    exact
      { observation := observation
        parameter_eq := rfl
        algebraic := algebraic
        semantic_error_le := by
          let ball := coefficient.name.process.ball state
          have radiusSmall : ball.radiusSq < 1 :=
            coefficient.name.process.accurate coefficient.name.state 1
              (by decide)
          have readingBound := reading_norm_le coefficient
            coefficientBound.bound
            (coefficientBound.centerBound_le fraction inside)
          change 2 * (4 * ball.radiusSq +
              Data.Gaussian.Norm.Basic.normSq reading) <=
            zeroAllowance coefficientBound
          calc
            2 * (4 * ball.radiusSq +
                Data.Gaussian.Norm.Basic.normSq reading) <=
                2 * (4 * 1 + 2 * (1 + coefficientBound.bound)) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add
                  (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                    radiusSmall.le (by decide)) readingBound) (by decide)
            _ = zeroAllowance coefficientBound := by
              unfold zeroAllowance
              ring1 }

end Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
