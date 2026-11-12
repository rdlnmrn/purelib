module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Edges
public import Purelib.Riemann.Paths.OwnerTracePath.Dyadic.Advance
public import Purelib.Riemann.Paths.OwnerTracePath.Pullback
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.DependentProduct
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Tactic.Ring
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Joint
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Spatial
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Vertices
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Multiplication.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTracePath.Dyadic
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.RootContinuation.SquareRootTrace.Pullback
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

/-! # Genuine paid traces of the SAME retained strip-grid advances

The polynomial variable below is the local edge parameter u. Time edges
retain the actual affine Legendre radicand; spatial edges retain the exact
composeLine of their fixed-fibre cubic. The original target-word scale
payment admits every interior advance. An additional trace-depth search
and residual requests precede all new interior Owners and readings.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside PathData)
open Purelib.Riemann.Paths.OwnerTracePath
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter)
open Purelib.Riemann.RootContinuation.SquareRootTrace

namespace EdgePolynomial

/-- The original oriented affine interval fraction, without interpolation of roots. -/
@[expose] def fraction (left right : Endpoint) (value : Rational) : Rational :=
  left.parameter + value * (right.parameter - left.parameter)

/-- Every actual unit parameter stays in the same original interval. -/
theorem fraction_inside (left right value : Endpoint) : Inside (fraction left right value.parameter) :=
  Box.coordinate_between left.inside right.inside value.inside

/-- The oriented interval map retains its literal first scalar endpoint. -/
theorem fraction_zero (left right : Endpoint) : fraction left right 0 = left.parameter := by
  unfold fraction
  ring1

/-- The oriented interval map retains its literal last scalar endpoint. -/
theorem fraction_one (left right : Endpoint) : fraction left right 1 = right.parameter := by
  unfold fraction
  ring1

/-- Differences of actual interval fractions retain the complete original oriented interval factor. -/
theorem fraction_sub (left right : Endpoint) (first last : Rational) :
    fraction left right last - fraction left right first = (right.parameter - left.parameter) * (last - first) := by
  unfold fraction
  ring1

/-- The actual affine Legendre radicand polynomial for one original temporal edge at a fixed spatial point. -/
@[expose] def temporal (parameter increment point : Canonical) (left right : Endpoint) : CoefficientPolynomial :=
  constant ((Paths.polynomial (parameter + (⟨left.parameter, 0⟩ : Canonical) * increment)).eval point) -
    constant (((⟨right.parameter - left.parameter, 0⟩ : Canonical) * increment) * point * (point - 1)) *
      Monomial.Coordinate.coordinatePolynomial

/-- The actual temporal polynomial evaluates at the SAME affine parameter map of the original Legendre cubic. -/
theorem temporal_eval (parameter increment point : Canonical) (left right : Endpoint) (value : Rational) :
    (temporal parameter increment point left right).eval (Cast.Path.ofCoordinate value) =
      (Paths.polynomial (parameter + (⟨fraction left right value, 0⟩ : Canonical) * increment)).eval point := by
  have affine : (⟨fraction left right value, 0⟩ : Canonical) =
      (⟨left.parameter, 0⟩ : Canonical) + (⟨value, 0⟩ : Canonical) *
        (⟨right.parameter - left.parameter, 0⟩ : Canonical) := by
    apply Basic.ext <;>
      simp only [fraction, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1
  unfold temporal
  rewrite [eval_sub, eval_mul, eval_constant, eval_constant, Monomial.Coordinate.coordinatePolynomial_eval,
    Paths.polynomial_eval, Paths.polynomial_eval, affine]
  simp only [Cast.Path.ofCoordinate]
  ring1

/-- The original Gaussian chord of a spatial subinterval is its literal parent point at the oriented fraction. -/
theorem spatial_point {polynomial : CoefficientPolynomial} {ambient : Box} {start finish : Canonical}
    (segment : ClearSegment polynomial ambient start finish) (left right : Endpoint) (value : Rational) :
    Affine.line (segment.pointAt left.parameter) (segment.pointAt right.parameter - segment.pointAt left.parameter)
      value = segment.pointAt (fraction left right value) := by
  apply Basic.ext <;>
    simp only [Affine.line, ClearSegment.pointAt, fraction, Cast.Path.ofCoordinate,
      Scale.scale_re, Scale.scale_im, Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im,
      Basic.mul_re, Basic.mul_im] <;> ring1

/-- The actual composeLine polynomial of the SAME oriented spatial subinterval at a fixed parameter. -/
@[expose] def spatial (parameter increment : Canonical) (time : Endpoint)
    {ambient : Box} {start finish : Canonical}
    (segment : ClearSegment (Paths.polynomial parameter) ambient start finish) (left right : Endpoint) :
    CoefficientPolynomial :=
  Substitution.Affine.composeLine (Paths.polynomial (parameter + (⟨time.parameter, 0⟩ : Canonical) * increment))
    (segment.pointAt left.parameter) (segment.pointAt right.parameter - segment.pointAt left.parameter)

/-- The actual spatial polynomial uses the SAME fixed-fibre cubic and literal original oriented parent map. -/
theorem spatial_eval (parameter increment : Canonical) (time : Endpoint)
    {ambient : Box} {start finish : Canonical}
    (segment : ClearSegment (Paths.polynomial parameter) ambient start finish) (left right : Endpoint)
    (value : Rational) :
    (spatial parameter increment time segment left right).eval (Cast.Path.ofCoordinate value) =
      (Paths.polynomial (parameter + (⟨time.parameter, 0⟩ : Canonical) * increment)).eval
        (segment.pointAt (fraction left right value)) :=
  (Substitution.Affine.eval_composeLine _ _ _ value).trans
    (congrArg (Paths.polynomial (parameter + (⟨time.parameter, 0⟩ : Canonical) * increment)).eval
      (spatial_point segment left right value))

end EdgePolynomial

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {range : Range patch} {budget : FixedRootBoxBudget.Budget patch.base.seed.owner}
    {factory : budget = range.seedBudget}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment (Paths.polynomial parameter) ambient start finish}
    {firstInside : patch.box.Contains start} {lastInside : patch.box.Contains finish}
    {increment : Canonical} {admitted : Norm.Basic.normSq increment ≤ range.stripBound}
    {firstPath lastPath : PathData budget budget}
    {firstDepth lastDepth : Nat} {left right : Endpoint}
    {grid : JointGrid (range := range) (budget := budget) increment firstPath lastPath
      firstDepth lastDepth left right}
    (cached : Vertices range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid)
    (ordered : left.parameter ≤ right.parameter)

/-- The actual temporal source endpoint belonging to the retained target occurrence. -/
@[expose] def timeFirst (timeIndex : Fin cached.times.length) : Endpoint :=
  (left :: cached.times)[timeIndex.castSucc.val]'timeIndex.castSucc.isLt

/-- The actual temporal target endpoint belonging to that SAME retained occurrence. -/
@[expose] def timeLast (timeIndex : Fin cached.times.length) : Endpoint :=
  (left :: cached.times)[timeIndex.succ.val]'timeIndex.succ.isLt

/-- The actual spatial source endpoint belonging to the retained target occurrence. -/
@[expose] def spaceFirst (spaceIndex : Fin cached.spaces.length) : Endpoint :=
  (left :: cached.spaces)[spaceIndex.castSucc.val]'spaceIndex.castSucc.isLt

/-- The actual spatial target endpoint belonging to that SAME retained occurrence. -/
@[expose] def spaceLast (spaceIndex : Fin cached.spaces.length) : Endpoint :=
  (left :: cached.spaces)[spaceIndex.succ.val]'spaceIndex.succ.isLt

/-- The genuine coarse temporal squared-Lipschitz scale of one original edge. -/
@[expose] def timeScale (timeIndex : Fin cached.times.length) : Rational :=
  (Norm.Basic.normSq increment * range.coefficient) *
    ((timeLast cached timeIndex).parameter - (timeFirst cached timeIndex).parameter) ^ 2

/-- The genuine coarse spatial squared-Lipschitz scale of one original edge. -/
@[expose] def spaceScale (spaceIndex : Fin cached.spaces.length) : Rational :=
  spatialScale (budget := budget) firstPath lastPath *
    ((spaceLast cached spaceIndex).parameter - (spaceFirst cached spaceIndex).parameter) ^ 2

/-- The actual temporal scale is nonnegative. -/
theorem timeScale_nonnegative (timeIndex : Fin cached.times.length) : 0 ≤ timeScale cached timeIndex :=
  Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg increment) range.coefficient_nonnegative)
    (Order.Arithmetic.sq_nonneg_direct _)

/-- The actual spatial scale is nonnegative. -/
theorem spaceScale_nonnegative (spaceIndex : Fin cached.spaces.length) : 0 ≤ spaceScale cached spaceIndex :=
  Order.Arithmetic.mul_nonneg_direct (spatialScale_nonnegative (budget := budget) firstPath lastPath)
    (Order.Arithmetic.sq_nonneg_direct _)

/-- The actual time-edge polynomial, retaining its original fixed spatial occurrence. -/
@[expose] def timePolynomial (timeIndex : Fin cached.times.length)
    (spaceIndex : Fin (left :: cached.spaces).length) : CoefficientPolynomial :=
  EdgePolynomial.temporal parameter increment
    (segment.pointAt ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt).parameter)
    (timeFirst cached timeIndex) (timeLast cached timeIndex)

/-- The actual spatial-edge polynomial, retaining its original fixed temporal occurrence. -/
@[expose] def spacePolynomial (timeIndex : Fin (left :: cached.times).length)
    (spaceIndex : Fin cached.spaces.length) : CoefficientPolynomial :=
  EdgePolynomial.spatial parameter increment ((left :: cached.times)[timeIndex.val]'timeIndex.isLt) segment
    (spaceFirst cached spaceIndex) (spaceLast cached spaceIndex)

namespace Time

variable (timeIndex : Fin cached.times.length) (spaceIndex : Fin (left :: cached.spaces).length)

/-- Every actual local edge parameter is nonzero by the original whole-rectangle strip admission. -/
theorem nonzero (endpoint : Endpoint) :
    OwnerPath.Dyadic.value (timePolynomial cached timeIndex spaceIndex) endpoint ≠ 0 := by
  have original := range.rectangle_nonzero segment firstInside lastInside increment admitted
    (EdgePolynomial.fraction (timeFirst cached timeIndex) (timeLast cached timeIndex) endpoint.parameter)
    ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt).parameter
    (EdgePolynomial.fraction_inside _ _ endpoint)
    ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt).inside
  exact Eq.mpr (congrArg (fun value : Canonical => value ≠ 0)
    (EdgePolynomial.temporal_eval parameter increment _ _ _ endpoint.parameter)) original

/-- The original Range temporal estimate pays the full local polynomial with its retained interval factor. -/
theorem variation (first last : Endpoint) :
    Norm.Basic.normSq (OwnerPath.Dyadic.value (timePolynomial cached timeIndex spaceIndex) first -
      OwnerPath.Dyadic.value (timePolynomial cached timeIndex spaceIndex) last) ≤
        timeScale cached timeIndex * (last.parameter - first.parameter) ^ 2 := by
  have varied := range.temporal_variation segment firstInside lastInside increment
    (EdgePolynomial.fraction (timeFirst cached timeIndex) (timeLast cached timeIndex) first.parameter)
    (EdgePolynomial.fraction (timeFirst cached timeIndex) (timeLast cached timeIndex) last.parameter)
    ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt).parameter
    ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt).inside
  have values := congrArg₂ (fun first last : Canonical => Norm.Basic.normSq (first - last))
    (EdgePolynomial.temporal_eval parameter increment
      (segment.pointAt ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt).parameter)
      (timeFirst cached timeIndex) (timeLast cached timeIndex) first.parameter)
    (EdgePolynomial.temporal_eval parameter increment
      (segment.pointAt ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt).parameter)
      (timeFirst cached timeIndex) (timeLast cached timeIndex) last.parameter)
  have scales : (Norm.Basic.normSq increment * range.coefficient) *
      (EdgePolynomial.fraction (timeFirst cached timeIndex) (timeLast cached timeIndex) last.parameter -
        EdgePolynomial.fraction (timeFirst cached timeIndex) (timeLast cached timeIndex) first.parameter) ^ 2 =
      timeScale cached timeIndex * (last.parameter - first.parameter) ^ 2 := by
    rewrite [EdgePolynomial.fraction_sub]
    unfold timeScale
    ring1
  exact values.trans_le (varied.trans_eq scales)

/-- The SAME whole time polynomial begins at its actual stored source vertex radicand. -/
theorem first_eq : radicand (segment := segment) increment (timeFirst cached timeIndex)
    ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt) =
      OwnerPath.Dyadic.value (timePolynomial cached timeIndex spaceIndex) OwnerPath.Dyadic.first :=
  ((EdgePolynomial.temporal_eval parameter increment _ _ _ 0).trans
    (congrArg (fun time : Rational => (Paths.polynomial
      (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
        (segment.pointAt ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt).parameter))
      (EdgePolynomial.fraction_zero _ _))).symm

/-- The SAME whole time polynomial ends at its actual stored target vertex radicand. -/
theorem last_eq : radicand (segment := segment) increment (timeLast cached timeIndex)
    ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt) =
      OwnerPath.Dyadic.value (timePolynomial cached timeIndex spaceIndex) OwnerPath.Dyadic.last :=
  ((EdgePolynomial.temporal_eval parameter increment _ _ _ 1).trans
    (congrArg (fun time : Rational => (Paths.polynomial
      (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
        (segment.pointAt ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt).parameter))
      (EdgePolynomial.fraction_one _ _))).symm

include ordered in
/-- The genuine whole temporal scale is within the SAME stored source Owner's original clearance. -/
theorem scale_small : timeScale cached timeIndex <
    (cached.owner timeIndex.castSucc spaceIndex).track.initial.clearance.bound := by
  rewrite [cached.owner_clearance]
  have paid := cached.time_scale_lt ordered timeIndex
  have eighth : budget.clearance / 8 ≤ budget.clearance :=
    Order.Field.divide_le_self budget.clearance_positive.le (by decide +kernel)
  exact paid.trans_le eighth

/-- The actual retained advance and one genuine trace-paid subdivision, with the final stationary handoff kept. -/
@[expose] def Trace (given : TimeEdge cached ordered timeIndex spaceIndex) :=
  (_polynomial : { value : CoefficientPolynomial // value = timePolynomial cached timeIndex spaceIndex }) ×
  OwnerPath.Dyadic.AdvanceTrace patch (cached.owner timeIndex.castSucc spaceIndex)
    (cached.owner timeIndex.succ spaceIndex) (cached.time_boxes timeIndex spaceIndex)
    (cached.time_small ordered timeIndex spaceIndex) given
    (first_eq cached timeIndex spaceIndex) (last_eq cached timeIndex spaceIndex)
    (Eq.mpr (congrArg (fun box : Box => box.Refines patch.base.seed.owner.track.initial.box)
      (cached.owner_box timeIndex.castSucc spaceIndex)) (Box.refines_refl _))
    (nonzero cached timeIndex spaceIndex) (timeScale cached timeIndex) (timeScale_nonnegative cached timeIndex)
    (variation cached timeIndex spaceIndex) (scale_small cached ordered timeIndex spaceIndex)

/-- Realize the GIVEN time advance once, selecting the extra trace depth before all new root work. -/
def realize (given : TimeEdge cached ordered timeIndex spaceIndex) : Trace cached ordered timeIndex spaceIndex given :=
  let polynomial := timePolynomial cached timeIndex spaceIndex
  let result := OwnerPath.Dyadic.realizeAdvance (polynomial := polynomial) patch
    (cached.owner timeIndex.castSucc spaceIndex)
    (cached.owner timeIndex.succ spaceIndex) (cached.time_boxes timeIndex spaceIndex)
    (cached.time_small ordered timeIndex spaceIndex) given
    (first_eq cached timeIndex spaceIndex) (last_eq cached timeIndex spaceIndex)
    (Eq.mpr (congrArg (fun box : Box => box.Refines patch.base.seed.owner.track.initial.box)
      (cached.owner_box timeIndex.castSucc spaceIndex)) (Box.refines_refl _))
    (nonzero cached timeIndex spaceIndex) (timeScale cached timeIndex) (timeScale_nonnegative cached timeIndex)
    (variation cached timeIndex spaceIndex) (scale_small cached ordered timeIndex spaceIndex)

  ⟨⟨polynomial, rfl⟩, result⟩

end Time

variable (zeroInside : Inside 0) (oneInside : Inside 1)
    (firstFactory : firstPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 0 zeroInside)
    (lastFactory : lastPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 1 oneInside)

namespace Space

variable (timeIndex : Fin (left :: cached.times).length) (spaceIndex : Fin cached.spaces.length)

/-- The actual spatial polynomial keeps its original fixed-fibre affine substitution factory. -/
theorem polynomial_eq :
    spacePolynomial cached timeIndex spaceIndex =
      Substitution.Affine.composeLine
        (Paths.polynomial (parameter +
          (⟨((left :: cached.times)[timeIndex.val]'timeIndex.isLt).parameter, 0⟩ : Canonical) * increment))
        (segment.pointAt (spaceFirst cached spaceIndex).parameter)
        (segment.pointAt (spaceLast cached spaceIndex).parameter -
          segment.pointAt (spaceFirst cached spaceIndex).parameter) := rfl

/-- Every actual spatial edge parameter is nonzero by the SAME original whole-rectangle admission. -/
theorem nonzero (endpoint : Endpoint) :
    OwnerPath.Dyadic.value (spacePolynomial cached timeIndex spaceIndex) endpoint ≠ 0 := by
  have original := range.rectangle_nonzero segment firstInside lastInside increment admitted
    ((left :: cached.times)[timeIndex.val]'timeIndex.isLt).parameter
    (EdgePolynomial.fraction (spaceFirst cached spaceIndex) (spaceLast cached spaceIndex) endpoint.parameter)
    ((left :: cached.times)[timeIndex.val]'timeIndex.isLt).inside
    (EdgePolynomial.fraction_inside _ _ endpoint)
  exact Eq.mpr (congrArg (fun value : Canonical => value ≠ 0)
    (EdgePolynomial.spatial_eval parameter increment _ segment _ _ endpoint.parameter)) original

include firstFactory lastFactory in
/-- The actual spatial polynomial retains the original two endpoint path scales and literal interval factor. -/
theorem variation (first last : Endpoint) :
    Norm.Basic.normSq (OwnerPath.Dyadic.value (spacePolynomial cached timeIndex spaceIndex) first -
      OwnerPath.Dyadic.value (spacePolynomial cached timeIndex spaceIndex) last) ≤
        spaceScale cached spaceIndex * (last.parameter - first.parameter) ^ 2 := by
  have varied := spatial_variation range budget factory segment firstInside lastInside increment admitted
    zeroInside oneInside firstPath lastPath firstFactory lastFactory
    ((left :: cached.times)[timeIndex.val]'timeIndex.isLt).parameter
    (EdgePolynomial.fraction (spaceFirst cached spaceIndex) (spaceLast cached spaceIndex) first.parameter)
    (EdgePolynomial.fraction (spaceFirst cached spaceIndex) (spaceLast cached spaceIndex) last.parameter)
    ((left :: cached.times)[timeIndex.val]'timeIndex.isLt).inside
    (EdgePolynomial.fraction_inside _ _ first) (EdgePolynomial.fraction_inside _ _ last)
  have values := congrArg₂ (fun first last : Canonical => Norm.Basic.normSq (first - last))
    (EdgePolynomial.spatial_eval parameter increment
      ((left :: cached.times)[timeIndex.val]'timeIndex.isLt) segment
      (spaceFirst cached spaceIndex) (spaceLast cached spaceIndex) first.parameter)
    (EdgePolynomial.spatial_eval parameter increment
      ((left :: cached.times)[timeIndex.val]'timeIndex.isLt) segment
      (spaceFirst cached spaceIndex) (spaceLast cached spaceIndex) last.parameter)
  have scales : spatialScale (budget := budget) firstPath lastPath *
      (EdgePolynomial.fraction (spaceFirst cached spaceIndex) (spaceLast cached spaceIndex) last.parameter -
        EdgePolynomial.fraction (spaceFirst cached spaceIndex) (spaceLast cached spaceIndex) first.parameter) ^ 2 =
      spaceScale cached spaceIndex * (last.parameter - first.parameter) ^ 2 := by
    rewrite [EdgePolynomial.fraction_sub]
    unfold spaceScale
    ring1
  exact values.trans_le (varied.trans_eq scales)

/-- The SAME composeLine polynomial begins at its actual stored source vertex radicand. -/
theorem first_eq : radicand (segment := segment) increment
    ((left :: cached.times)[timeIndex.val]'timeIndex.isLt) (spaceFirst cached spaceIndex) =
    OwnerPath.Dyadic.value (spacePolynomial cached timeIndex spaceIndex) OwnerPath.Dyadic.first :=
  ((EdgePolynomial.spatial_eval parameter increment _ segment _ _ 0).trans
    (congrArg (fun fraction : Rational => (Paths.polynomial
      (parameter + (⟨((left :: cached.times)[timeIndex.val]'timeIndex.isLt).parameter, 0⟩ :
        Canonical) * increment)).eval
        (segment.pointAt fraction)) (EdgePolynomial.fraction_zero _ _))).symm

/-- The SAME composeLine polynomial ends at its actual stored target vertex radicand. -/
theorem last_eq : radicand (segment := segment) increment
    ((left :: cached.times)[timeIndex.val]'timeIndex.isLt) (spaceLast cached spaceIndex) =
    OwnerPath.Dyadic.value (spacePolynomial cached timeIndex spaceIndex) OwnerPath.Dyadic.last :=
  ((EdgePolynomial.spatial_eval parameter increment _ segment _ _ 1).trans
    (congrArg (fun fraction : Rational => (Paths.polynomial
      (parameter + (⟨((left :: cached.times)[timeIndex.val]'timeIndex.isLt).parameter, 0⟩ :
        Canonical) * increment)).eval
        (segment.pointAt fraction)) (EdgePolynomial.fraction_one _ _))).symm

include ordered in
/-- The genuine spatial scale is within the SAME stored source Owner's original clearance. -/
theorem scale_small : spaceScale cached spaceIndex <
    (cached.owner timeIndex spaceIndex.castSucc).track.initial.clearance.bound := by
  rewrite [cached.owner_clearance]
  have paid := cached.space_scale_lt ordered spaceIndex
  have eighth : budget.clearance / 8 ≤ budget.clearance :=
    Order.Field.divide_le_self budget.clearance_positive.le (by decide +kernel)
  exact paid.trans_le eighth

/-- The GIVEN spatial advance and one genuine trace-paid subdivision with the actual stationary target handoff. -/
@[expose] def Trace
    (given : SpaceEdge cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex) :=
  (_polynomial : { value : CoefficientPolynomial // value = spacePolynomial cached timeIndex spaceIndex }) ×
  OwnerPath.Dyadic.AdvanceTrace patch (cached.owner timeIndex spaceIndex.castSucc)
    (cached.owner timeIndex spaceIndex.succ) (cached.space_boxes timeIndex spaceIndex)
    (cached.space_small ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex) given
    (first_eq cached timeIndex spaceIndex) (last_eq cached timeIndex spaceIndex)
    (Eq.mpr (congrArg (fun box : Box => box.Refines patch.base.seed.owner.track.initial.box)
      (cached.owner_box timeIndex spaceIndex.castSucc)) (Box.refines_refl _))
    (nonzero cached timeIndex spaceIndex) (spaceScale cached spaceIndex) (spaceScale_nonnegative cached spaceIndex)
    (variation cached zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex)
    (scale_small cached ordered timeIndex spaceIndex)

/-- Realize the GIVEN spatial advance once, preserving its exact composeLine and physical interval maps. -/
def realize (given : SpaceEdge cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex) :
    Trace cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex given :=
  let polynomial := spacePolynomial cached timeIndex spaceIndex
  let result := OwnerPath.Dyadic.realizeAdvance (polynomial := polynomial) patch
    (cached.owner timeIndex spaceIndex.castSucc)
    (cached.owner timeIndex spaceIndex.succ) (cached.space_boxes timeIndex spaceIndex)
    (cached.space_small ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex) given
    (first_eq cached timeIndex spaceIndex) (last_eq cached timeIndex spaceIndex)
    (Eq.mpr (congrArg (fun box : Box => box.Refines patch.base.seed.owner.track.initial.box)
      (cached.owner_box timeIndex spaceIndex.castSucc)) (Box.refines_refl _))
    (nonzero cached timeIndex spaceIndex) (spaceScale cached spaceIndex) (spaceScale_nonnegative cached spaceIndex)
    (variation cached zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex)
    (scale_small cached ordered timeIndex spaceIndex)

  ⟨⟨polynomial, rfl⟩, result⟩

variable {cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex}
    {given : SpaceEdge cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex}
    (retained : Trace cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex given)

/-- Map the SAME realized spatial OwnerPath to its actual fixed-fibre base chord, without new observations.

The whole original trace remains in retained. Exact composeLine evaluation
transports its two original endpoint Owners and every ordered intermediate
vertex. This is no assertion about the independent member Stage RootChain.
-/
def spatialPath :
    let origin := segment.pointAt (spaceFirst cached spaceIndex).parameter
    let direction := segment.pointAt (spaceLast cached spaceIndex).parameter - origin
    let polynomial := Paths.polynomial
      (parameter + (⟨((left :: cached.times)[timeIndex.val]'timeIndex.isLt).parameter, 0⟩ : Canonical) * increment)
    OwnerPath polynomial (AffineImage.point origin direction (Cast.Path.ofCoordinate OwnerPath.Dyadic.first.parameter))
      (castOwnerParameter (AffineImage.eval polynomial (spacePolynomial cached timeIndex spaceIndex)
        origin direction rfl (Cast.Path.ofCoordinate OwnerPath.Dyadic.first.parameter))
        (OwnerPath.Dyadic.sourceOwner (source := cached.owner timeIndex spaceIndex.castSucc)
          (firstEq := first_eq cached timeIndex spaceIndex)))
      (AffineImage.point origin direction (Cast.Path.ofCoordinate OwnerPath.Dyadic.last.parameter))
      (castOwnerParameter (AffineImage.eval polynomial (spacePolynomial cached timeIndex spaceIndex)
        origin direction rfl (Cast.Path.ofCoordinate OwnerPath.Dyadic.last.parameter))
        (OwnerPath.Dyadic.targetOwner (target := cached.owner timeIndex spaceIndex.succ)
          (lastEq := last_eq cached timeIndex spaceIndex))) :=
  retained.2.2.whole.affineImage (segment.pointAt (spaceFirst cached spaceIndex).parameter)
    (segment.pointAt (spaceLast cached spaceIndex).parameter -
      segment.pointAt (spaceFirst cached spaceIndex).parameter) rfl

/-- Map the SAME stored root/base realization through that actual affine factory, retaining all edge caches. -/
def spatialRealization : OwnerPath.Realization (spatialPath (retained := retained)) 0 0 :=
  retained.2.2.realized.affineImage (segment.pointAt (spaceFirst cached spaceIndex).parameter)
    (segment.pointAt (spaceLast cached spaceIndex).parameter -
      segment.pointAt (spaceFirst cached spaceIndex).parameter) rfl

end Space

namespace Edges

variable {cached ordered zeroInside oneInside firstFactory lastFactory}
    (retained : Edges cached ordered zeroInside oneInside firstFactory lastFactory)

/-- One actual realized temporal trace for every SAME retained unique temporal advance. -/
@[expose] def TimeTraces := DependentProduct retained.original.times (fun timeIndex =>
  DependentProduct (left :: retained.original.spaces) (fun spaceIndex =>
    Time.Trace retained.original ordered timeIndex spaceIndex (retained.time timeIndex spaceIndex)))

/-- One actual realized spatial trace for every SAME retained unique spatial advance. -/
@[expose] def SpaceTraces := DependentProduct (left :: retained.original.times) (fun timeIndex =>
  DependentProduct retained.original.spaces (fun spaceIndex =>
    Space.Trace retained.original ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex
      (retained.space timeIndex spaceIndex)))

/-- Bind each temporal edge realization once on its SAME given advance/comparison cache. -/
def timeTraces : TimeTraces retained :=
  DependentProduct.ofFn retained.original.times (fun timeIndex =>
    DependentProduct.ofFn (left :: retained.original.spaces) (fun spaceIndex =>
      Time.realize retained.original ordered timeIndex spaceIndex (retained.time timeIndex spaceIndex)))

/-- Bind each spatial edge realization once on its SAME given advance/comparison cache. -/
def spaceTraces : SpaceTraces retained :=
  DependentProduct.ofFn (left :: retained.original.times) (fun timeIndex =>
    DependentProduct.ofFn retained.original.spaces (fun spaceIndex =>
      Space.realize retained.original ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex
        (retained.space timeIndex spaceIndex)))

/-- The SAME original edge/vertex caches and both once-built tables of genuine realized edge traces. -/
@[expose] def Traces :=
  (_original : { value : Edges cached ordered zeroInside oneInside firstFactory lastFactory // value = retained }) ×
  (_times : { value : TimeTraces retained // value = timeTraces retained }) ×
    { spaces : SpaceTraces retained // spaces = spaceTraces retained }

/-- Materialize both unique trace tables once, retaining the whole original edges and both complete factories. -/
def traces : Traces retained :=
  let times := timeTraces retained
  let spaces := spaceTraces retained
  ⟨⟨retained, rfl⟩, ⟨times, rfl⟩, ⟨spaces, rfl⟩⟩

namespace Traces

variable {retained} (realized : Traces retained)

/-- The complete original419 edge and shared-vertex preparation is retained unchanged as data. -/
@[expose] def original : Edges cached ordered zeroInside oneInside firstFactory lastFactory := realized.1.val

/-- The full original cache is the GIVEN preparation, without rebuilding any vertex or coarse advance. -/
theorem original_eq : realized.original = retained := realized.1.property

/-- Read the SAME complete table of unique realized temporal traces. -/
@[expose] def times : TimeTraces retained := realized.2.1.val

/-- The complete temporal table keeps its original one-pass materialization factory. -/
theorem times_eq : realized.times = timeTraces retained := realized.2.1.property

/-- Read the SAME complete table of unique realized spatial traces. -/
@[expose] def spaces : SpaceTraces retained := realized.2.2.val

/-- The complete spatial table keeps its original one-pass materialization factory. -/
theorem spaces_eq : realized.spaces = spaceTraces retained := realized.2.2.property

/-- Read the SAME realized temporal edge cache at its two original bounded occurrences. -/
@[expose] def time (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    Time.Trace retained.original ordered timeIndex spaceIndex (retained.time timeIndex spaceIndex) :=
  DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get retained.original.times realized.times timeIndex) spaceIndex

/-- Read the SAME realized spatial edge cache at its two original bounded occurrences. -/
@[expose] def space (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    Space.Trace retained.original ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex
      (retained.space timeIndex spaceIndex) :=
  DependentProduct.get retained.original.spaces
    (DependentProduct.get (left :: retained.original.times) realized.spaces timeIndex) spaceIndex

/-- Both adjacent cell consumers use the SAME retained whole temporal trace at equal bounded edge occurrences. -/
theorem time_index_heq {firstTime lastTime : Fin retained.original.times.length}
    {firstSpace lastSpace : Fin (left :: retained.original.spaces).length}
    (timeEq : firstTime = lastTime) (spaceEq : firstSpace = lastSpace) :
    HEq (realized.time firstTime firstSpace) (realized.time lastTime lastSpace) := by
  cases timeEq
  cases spaceEq
  rfl

/-- Both adjacent cell consumers use the SAME retained whole spatial trace at equal bounded edge occurrences. -/
theorem space_index_heq {firstTime lastTime : Fin (left :: retained.original.times).length}
    {firstSpace lastSpace : Fin retained.original.spaces.length}
    (timeEq : firstTime = lastTime) (spaceEq : firstSpace = lastSpace) :
    HEq (realized.space firstTime firstSpace) (realized.space lastTime lastSpace) := by
  cases timeEq
  cases spaceEq
  rfl

/-- Read four actual realized edges of a cell from the SAME unique tables, retaining all signed stationary handoffs.

This tuple is not a filled-cell witness: different incident coarse edges
may still have different retained readings at a common coarse Owner. No
reverse edge, root-route equality or primitive cancellation is inferred.
-/
@[expose] def cell (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin retained.original.spaces.length) :
    Time.Trace retained.original ordered timeIndex spaceIndex.castSucc (retained.time timeIndex spaceIndex.castSucc) ×
    Space.Trace retained.original ordered zeroInside oneInside firstFactory lastFactory timeIndex.succ spaceIndex
      (retained.space timeIndex.succ spaceIndex) ×
    Space.Trace retained.original ordered zeroInside oneInside firstFactory lastFactory timeIndex.castSucc spaceIndex
      (retained.space timeIndex.castSucc spaceIndex) ×
    Time.Trace retained.original ordered timeIndex spaceIndex.succ (retained.time timeIndex spaceIndex.succ) :=
  ⟨realized.time timeIndex spaceIndex.castSucc, realized.space timeIndex.succ spaceIndex,
    realized.space timeIndex.castSucc spaceIndex, realized.time timeIndex spaceIndex.succ⟩

end Traces

end Edges

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices

end
