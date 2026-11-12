module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonSignChain
import Purelib.Integration.Path.DyadicPairedIncrementComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric

public section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

/-! Uncorrected full paired areas on the retained common intervals. The
shared polynomial pair removes local origins before counting increments. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest

open Purelib.Data.Rat.Fraction.Order

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus count otherCount : Nat} {curve : Basic.HyperellipticCurve genus} {differential other :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : UniformReciprocalModels.Data patch count} {otherData :
    UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : UniformReciprocalCover.Cover data} {secondCover :
    UniformReciprocalCover.Cover otherData}
  {regular : RegularBounds.Data cap} {common :
    UniformReciprocalCommonCover.CommonCover firstCover secondCover}
  {target : Coordinate} {minimum stage depth : Nat} {box otherBox :
    Rational.Box}
  {sample : Cap.Primitives.Sample cap differential stage box}
  {otherSample : Cap.Primitives.Sample cap other stage otherBox}
  {source : UniformReciprocalPrimitives.SourcePrimitive data stage} {otherSource :
    UniformReciprocalPrimitives.SourcePrimitive otherData stage}
  {request : CommonRibbonRequest regular common target minimum}
  {evaluated : Evaluation request sample
    otherSample source otherSource depth}

/-- Evaluate the retained common polynomial pair at the inverse original parent-edge coordinate. -/
@[expose] def Evaluation.SharedPair.values (shared :
  Evaluation.SharedPair evaluated)
  (parameter : Coordinate) : PrimitivePoint :=
  ⟨shared.first.eval (parent.edge.point parameter)⁻¹, shared.second.eval (parent.edge.point parameter)⁻¹⟩

/-- Take the larger original geometric comparison error of the retained paired interval. -/
@[expose] def Entry.incrementError (entry :
  Entry request sample otherSample source
  otherSource depth) : Coordinate :=
  max (Basic.quarterRadius (RegularComparison.Data.regularScale
    entry.plan.first) stage) (Basic.quarterRadius
    (RegularComparison.Data.regularScale entry.plan.second) stage)

/-- Bound original and cap increments by the maximum of both retained source slopes and error-adjusted cap slopes. -/
@[expose] def Entry.incrementSlope (entry :
  Entry request sample otherSample source
  otherSource depth) : Coordinate :=
  max (max data.sourceSlope otherData.sourceSlope)
    (max (2 * (data.sourceSlope + Basic.quarterRadius
      (RegularComparison.Data.regularScale entry.plan.first) stage))
      (2 * (otherData.sourceSlope + Basic.quarterRadius
        (RegularComparison.Data.regularScale entry.plan.second) stage)))

/-- Subtracting two readings relative to one origin gives their original unshifted difference. -/
private theorem unanchor (first last origin : Gaussian.Basic.Canonical) : (last - origin) - (first - origin) = last -
  first := by ring1

/-- The full paired dyadic increment-area comparison on the original common interval.

Retain the exact factor sixteen, increment error, common slope and fourth power of interval length at every finite
depth. -/
@[expose] def Evaluation.SharedPair.IntervalAreaBound (shared :
  Evaluation.SharedPair evaluated)
    (entry : Entry request sample
      otherSample source otherSource depth) (fine : Nat) : Prop :=
    Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
      (Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (sourceValues source otherSource) fine
        entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter) -
      Path.PairedIncrementArea.area (Path.Dyadic.DyadicPairedPrimitivePaths.increments shared.values fine
        entry.plan.interval.edge.left.parameter entry.plan.interval.edge.right.parameter)) ≤
      16 * entry.incrementError * entry.incrementSlope *
        (entry.plan.interval.edge.right.parameter - entry.plan.interval.edge.left.parameter)^4

/-- All intermediate excursions are included. The error bound is independent
of the requested spatial subdivision depth and contains no endpoint term. -/
theorem Evaluation.SharedPair.interval_area_bound (shared :
  Evaluation.SharedPair evaluated)
    (entry : Entry request sample
      otherSample source otherSource depth) (member : entry ∈ evaluated.entries) (fine : Nat) :
    shared.IntervalAreaBound entry fine := open Purelib.Data.Rat in by
  have errorNonnegative : 0 ≤ entry.incrementError :=
    (Basic.quarterRadius_nonneg
      (RegularComparison.Data.regularScale_nonnegative entry.plan.first)
      stage).trans (Fraction.Order.Basic.le_max_left ..)
  have slopeNonnegative : 0 ≤ entry.incrementSlope :=
    (data.sourceSlope_nonnegative.trans (Fraction.Order.Basic.le_max_left ..)).trans (Fraction.Order.Basic.le_max_left
      ..)
  have sourceFirst : data.sourceSlope ≤ entry.incrementSlope := (Fraction.Order.Basic.le_max_left ..).trans
    (Fraction.Order.Basic.le_max_left ..)
  have sourceSecond : otherData.sourceSlope ≤ entry.incrementSlope := (Fraction.Order.Basic.le_max_right ..).trans
    (Fraction.Order.Basic.le_max_left ..)
  have capFirst : 2 * (data.sourceSlope + Basic.quarterRadius
    (RegularComparison.Data.regularScale entry.plan.first) stage) ≤
    entry.incrementSlope :=
    (Fraction.Order.Basic.le_max_left ..).trans (Fraction.Order.Basic.le_max_right ..)
  have capSecond : 2 * (otherData.sourceSlope + Basic.quarterRadius
    (RegularComparison.Data.regularScale entry.plan.second) stage) ≤
    entry.incrementSlope :=
    (Fraction.Order.Basic.le_max_right ..).trans (Fraction.Order.Basic.le_max_right ..)
  apply Path.DyadicPairedIncrementComparison.increments_area_difference_bound _ _ errorNonnegative slopeNonnegative
    (lower := entry.plan.interval.edge.left.parameter) (upper := entry.plan.interval.edge.right.parameter)
    _ _ _ fine ⟨le_rfl, entry.plan.interval.ordered⟩ ⟨entry.plan.interval.ordered, le_rfl⟩ entry.plan.interval.ordered
  · intro first last firstInside lastInside
    have firstUnit := And.intro (entry.plan.interval.edge.left.inside.1.trans firstInside.1)
      (firstInside.2.trans entry.plan.interval.edge.right.inside.2)
    have lastUnit := And.intro (entry.plan.interval.edge.left.inside.1.trans lastInside.1)
      (lastInside.2.trans entry.plan.interval.edge.right.inside.2)
    have firstScalar := source.increment_bound firstUnit lastUnit
    have secondScalar := otherSource.increment_bound firstUnit lastUnit
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
    exact ⟨firstScalar.trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct sourceFirst
        (Arithmetic.sq_nonneg_direct _)),
      secondScalar.trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct sourceSecond
        (Arithmetic.sq_nonneg_direct _))⟩
  · intro first last firstInside lastInside
    have left := RegularArea.RegularAlignment.cap_increment_bound source entry.left
      ⟨entry.plan.interval.first.lower.trans firstInside.1, firstInside.2.trans entry.plan.interval.first.upper⟩
      ⟨entry.plan.interval.first.lower.trans lastInside.1, lastInside.2.trans entry.plan.interval.first.upper⟩
    have right := RegularArea.RegularAlignment.cap_increment_bound otherSource
      entry.right
      ⟨entry.plan.interval.second.lower.trans firstInside.1, firstInside.2.trans entry.plan.interval.second.upper⟩
      ⟨entry.plan.interval.second.lower.trans lastInside.1, lastInside.2.trans entry.plan.interval.second.upper⟩
    dsimp only [RegularArea.RegularAlignment.capValue] at left right
    rw [shared.first_owner entry member,
      unanchor] at left
    rw [shared.second_owner entry member,
      unanchor] at right
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at left right
    exact ⟨left.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct capFirst
      (Arithmetic.sq_nonneg_direct _)),
      right.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct capSecond
        (Arithmetic.sq_nonneg_direct _))⟩
  · intro first last firstInside lastInside
    have estimates := shared.increment_errors entry member firstInside lastInside
    obtain ⟨left, right⟩ := estimates
    have rearrange (a b c d : Gaussian.Basic.Canonical) : (b - a) - (d - c) = (b - d) - (a - c) := by ring1
    rw [rearrange] at left right
    have firstError : Basic.quarterRadius
      (RegularComparison.Data.regularScale entry.plan.first) stage ≤
      entry.incrementError := Fraction.Order.Basic.le_max_left ..
    have secondError : Basic.quarterRadius
      (RegularComparison.Data.regularScale entry.plan.second) stage ≤
      entry.incrementError := Fraction.Order.Basic.le_max_right ..
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at left right
    exact ⟨left.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct firstError
      (Arithmetic.sq_nonneg_direct _)),
      right.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct secondError
        (Arithmetic.sq_nonneg_direct _))⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
