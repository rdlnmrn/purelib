module

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Piece

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Quadrature
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Program
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Refinement
public import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Rational.Geometric.DyadicCount
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Interval.Width
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Actual later cofactor observations on the retained spatial dyadic layer

Each original node keeps its complete Piece, Model, source query and old
observation. One dependent vector stores an actual later Model on that same
certificate at the node's width-fourth request. Every later index includes
the old selected index, and no interior source is queried again.

The original layer's quartered residual request and squared-width equation
identify their common decay. The actual integral-sample differences acquire
a fixed fourth-power ceiling after their squared chart displacement is
applied. Original finite quadrance summation and dyadic count cancellation
then pay a computed finite-request contraction. This compares scalar chart
cells; it asserts no shared primitive endpoint telescoping or geometric
integral equality, and does not contract a fixed parameter-increment budget.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.RootContinuation

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}

namespace Piece

/-- The original whole-quarter constructor derives a positive width from its retained exact unit-span readback. -/
theorem ofSource_width_positive (data : Waist.Differential.Bounds.Data site parameter differential)
    (source : Transport.Reading actual 0 ⟨by decide +kernel, by decide +kernel⟩)
    (regular : parameter ≠ criticalValue site) (accuracy : AccuracyRequest) :
    0 < (ofSource data source regular accuracy).span.width := by
  rewrite [ofSource_span]
  change (0 : Fraction.Rational) < 1 - 0
  decide +kernel

end Piece

namespace Layer

open Purelib.Data.Rat.Fraction.Order

variable {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy} {depth : Nat}

/-- A retained node has positive actual width whenever its original starting span has positive width. -/
theorem width_positive (layer : Layer initial depth) (initialPositive : 0 < initial.span.width)
    (piece : Piece data actual layer.accuracy) (member : piece ∈ layer.pieces) : 0 < piece.span.width := by
  have squarePositive : 0 < piece.span.width ^ 2 := by
    rewrite [layer.widths piece member]
    exact Geometric.Basic.quarterRadius_pos (Arithmetic.pow_pos_direct initialPositive 2) depth
  have widthNonnegative := Interval.Bounds.width_nonneg piece.span
  refine ⟨widthNonnegative, ?_⟩
  intro reverse
  have zero : piece.span.width = 0 := Fraction.Order.Basic.le_antisymm _ _ reverse widthNonnegative
  exact squarePositive.ne' ((congrArg (fun value : Fraction.Rational => value ^ 2) zero).trans (by decide +kernel))

/-- The original node lookup retains its positive width without transporting its parent index or source cache. -/
theorem node_width_positive (layer : Layer initial depth) (initialPositive : 0 < initial.span.width)
    (index : Fin layer.pieces.length) : 0 < (layer.node index).span.width :=
  layer.width_positive initialPositive (layer.node index) (List.getElem_mem index.isLt)

/-- The original quartered request is exactly its initial request-per-squared-width ratio times a node's squared width.

The original layer's accuracy and width readbacks share the same quarter
power. A positive original span pays the one initial scalar division; no
per-node cutoff or additional quantitative bound is supplied.
-/
theorem accuracy_width_eq (layer : Layer initial depth) (initialPositive : 0 < initial.span.width)
    (piece : Piece data actual layer.accuracy) (member : piece ∈ layer.pieces) :
    layer.accuracy.tolerance =
      (initialAccuracy.tolerance / initial.span.width ^ 2) * piece.span.width ^ 2 := by
  rewrite [layer.accuracy_eq, layer.widths piece member,
    Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  have paid : (initialAccuracy.tolerance / initial.span.width ^ 2) * initial.span.width ^ 2 =
      initialAccuracy.tolerance :=
    Fraction.Field.div_mul_cancel_of_ne _ _ (Arithmetic.pow_pos_direct initialPositive 2).ne'
  calc
    _ = ((initialAccuracy.tolerance / initial.span.width ^ 2) * initial.span.width ^ 2) *
        (1 / 4 : Fraction.Rational) ^ depth := congrArg
      (fun value : Fraction.Rational => value * (1 / 4 : Fraction.Rational) ^ depth) paid.symm
    _ = _ := by ring1

/-- The original residual slope and initial request-per-squared-width ratio compute the fixed comparison ceiling. -/
def refinementCeiling {initialAccuracy : AccuracyRequest} (initial : Piece data actual initialAccuracy) :
    Fraction.Rational :=
  Bounds.residualSlope data * (initialAccuracy.tolerance / initial.span.width ^ 2 + 1)

/-- The computed fixed cell-comparison ceiling is nonnegative on the original retained regular fibre. -/
theorem refinementCeiling_nonnegative {initialAccuracy : AccuracyRequest}
    (initial : Piece data actual initialAccuracy) : 0 ≤ refinementCeiling initial :=
  Arithmetic.mul_nonneg_direct
    (Bounds.signed_slopes_nonnegative data initial.cell.regular).2
    (Arithmetic.add_le_add_direct
      (Fraction.Order.Field.div_nonneg_direct initialAccuracy.positive.le
        (Arithmetic.sq_nonneg_direct initial.span.width))
      (by decide +kernel : (0 : Fraction.Rational) ≤ 1))

/-- Any actual later request paid by the fourth width has the SAME original layer integral-error ceiling.

The supplied observation remains a complete Refined cache on the original
node. Its actual residual tolerance may be smaller than the width's fourth
power, and the old layer request remains explicitly paid by its width law.
-/
theorem refined_integral_error_le_of_request (layer : Layer initial depth) (initialPositive : 0 < initial.span.width)
    (piece : Piece data actual layer.accuracy) (member : piece ∈ layer.pieces)
    {request : AccuracyRequest} (refined : Cells.Model.Refined piece.cell request)
    (requestPaid : request.tolerance ≤ piece.span.width ^ 4) :
    Norm.Basic.normSq (refined.val.cell.integralSample - piece.cell.cell.integralSample) ≤
      refinementCeiling initial * piece.span.width ^ 4 := by
  have fourthBound : piece.span.width ^ 4 ≤ piece.span.width ^ 2 := by
    calc
      _ = piece.span.width ^ 2 * piece.span.width ^ 2 := by ring1
      _ ≤ piece.span.width ^ 2 * 1 := Arithmetic.mul_le_mul_of_nonneg_left_direct
        piece.width_sq_le_one (Arithmetic.sq_nonneg_direct piece.span.width)
      _ = _ := Fraction.Field.mul_one_direct _
  have accuracyBound : piece.span.width ^ 4 + layer.accuracy.tolerance ≤
      (initialAccuracy.tolerance / initial.span.width ^ 2 + 1) * piece.span.width ^ 2 :=
    (Arithmetic.add_le_add_direct fourthBound
      (layer.accuracy_width_eq initialPositive piece member).le).trans_eq (by ring1)
  have paid := refined.integral_error_le
  unfold Cells.Model.errorBound at paid
  have paidRequest := Arithmetic.add_le_add_direct requestPaid
    (Fraction.Order.Basic.le_refl layer.accuracy.tolerance)
  have coefficient := Arithmetic.mul_le_mul_of_nonneg_left_direct accuracyBound
    (Bounds.signed_slopes_nonnegative data initial.cell.regular).2
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct coefficient
    (Arithmetic.sq_nonneg_direct piece.span.width)
  have scalarIdentity : piece.span.width ^ 2 * (Bounds.residualSlope data *
      ((initialAccuracy.tolerance / initial.span.width ^ 2 + 1) * piece.span.width ^ 2)) =
      refinementCeiling initial * piece.span.width ^ 4 := by
    unfold refinementCeiling
    ring1
  exact paid.trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct paidRequest
        (Bounds.signed_slopes_nonnegative data initial.cell.regular).2)
      (Arithmetic.sq_nonneg_direct piece.span.width)).trans (scaled.trans_eq scalarIdentity))

/-- A node's actual new-versus-old integral samples obey the derived uniform spatial fourth-power ceiling. -/
theorem refined_integral_error_le (layer : Layer initial depth) (initialPositive : 0 < initial.span.width)
    (piece : Piece data actual layer.accuracy) (member : piece ∈ layer.pieces)
    (refined : Cells.Model.Refined piece.cell
      (piece.cell.fourthRequest (layer.width_positive initialPositive piece member))) :
    Norm.Basic.normSq (refined.val.cell.integralSample - piece.cell.cell.integralSample) ≤
      refinementCeiling initial * piece.span.width ^ 4 :=
  layer.refined_integral_error_le_of_request initialPositive piece member refined
    (piece.cell.fourthRequest_tolerance (layer.width_positive initialPositive piece member)).le

/-- One exact original node's later Model retains its original Model and independently paid width-fourth observation. -/
abbrev RefinedEntry (layer : Layer initial depth) (initialPositive : 0 < initial.span.width)
    (index : Fin layer.pieces.length) :=
  Cells.Model.Refined (layer.node index).cell
    ((layer.node index).cell.fourthRequest (layer.node_width_positive initialPositive index))

/-- A materialized dependent bank of later observations on the unchanged original layer and node-index spine. -/
abbrev RefinedSamples (layer : Layer initial depth) (initialPositive : 0 < initial.span.width) :=
  Data.Vector.DependentVector (fun index => RefinedEntry layer initialPositive index)

/-- Request each original node's later cofactor observation once and store its complete new Model at the same index. -/
def refineSamples (layer : Layer initial depth) (initialPositive : 0 < initial.span.width) :
    RefinedSamples layer initialPositive :=
  Data.Vector.DependentVector.ofFn (fun index =>
    (layer.node index).cell.refineFourth (layer.node_width_positive initialPositive index))

/-- The stored entry is the original fourth-power refinement factory on that identical node and source certificate. -/
theorem refineSamples_apply (layer : Layer initial depth) (initialPositive : 0 < initial.span.width)
    (index : Fin layer.pieces.length) :
    (layer.refineSamples initialPositive).get index =
      (layer.node index).cell.refineFourth (layer.node_width_positive initialPositive index) :=
  Data.Vector.DependentVector.ofFn_get _ index

/-- Actual later node caches at independently chosen fourth-paid requests obey the original finite contraction.

The original node list, dyadic count and width laws are unchanged. Each
complete later Model is read from the supplied dependent vector; no
observation or model factory is repeated in this finite comparison.
-/
theorem refinedIntegralDifferenceSum_le (layer : Layer initial depth) (initialPositive : 0 < initial.span.width)
    (requests : Fin layer.pieces.length → AccuracyRequest)
    (samples : Data.Vector.DependentVector (fun index => Cells.Model.Refined (layer.node index).cell (requests index)))
    (requestsPaid : ∀ index, (requests index).tolerance ≤ (layer.node index).span.width ^ 4) :
    Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun index =>
      (samples.get index).val.cell.integralSample - (layer.node index).cell.cell.integralSample)) ≤
      refinementCeiling initial * initial.span.width ^ 2 *
        Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth := by
  have bounded (index : Fin layer.pieces.length) :
      Norm.Basic.normSq ((samples.get index).val.cell.integralSample - (layer.node index).cell.cell.integralSample) ≤
        refinementCeiling initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2 := by
    have member : layer.node index ∈ layer.pieces := List.getElem_mem index.isLt
    have paid := layer.refined_integral_error_le_of_request initialPositive (layer.node index) member
      (samples.get index) (requestsPaid index)
    have fourth : (layer.node index).span.width ^ 4 =
        Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2 := by
      calc
        _ = ((layer.node index).span.width ^ 2) ^ 2 := by ring1
        _ = _ := congrArg (fun value : Fraction.Rational => value ^ 2) (layer.widths (layer.node index) member)
    exact paid.trans_eq (congrArg (fun value : Fraction.Rational => refinementCeiling initial * value) fourth)
  have sumBound := Norm.Sum.Indexed.normSq_sumFin_le
    (fun index => (samples.get index).val.cell.integralSample - (layer.node index).cell.cell.integralSample)
    (refinementCeiling initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2) bounded
  have countCast : (layer.pieces.length : Fraction.Rational) = ((2 ^ depth : Nat) : Fraction.Rational) :=
    congrArg (fun count : Nat => (count : Fraction.Rational)) layer.count
  have scalarCancellation : (layer.pieces.length : Fraction.Rational) ^ 2 *
      (refinementCeiling initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2) =
      refinementCeiling initial * initial.span.width ^ 2 *
        Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth := by
    rewrite [countCast]
    calc
      _ = (refinementCeiling initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth) *
          (((2 ^ depth : Nat) : Fraction.Rational) *
            (((2 ^ depth : Nat) : Fraction.Rational) *
              Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth)) := by ring1
      _ = (refinementCeiling initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth) *
          initial.span.width ^ 2 := congrArg
        (fun value : Fraction.Rational =>
          (refinementCeiling initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth) * value)
        (Geometric.DyadicCount.dyadic_count_cancel (initial.span.width ^ 2) depth)
      _ = _ := by ring1
  exact sumBound.trans_eq scalarCancellation

namespace RefinedSamples

/-- Read the exact new-minus-old integral-sample difference at one retained original parent index. -/
def integralDifference {layer : Layer initial depth} {initialPositive : 0 < initial.span.width}
    (samples : RefinedSamples layer initialPositive) (index : Fin layer.pieces.length) : Canonical :=
  (samples.get index).val.cell.integralSample - (layer.node index).cell.cell.integralSample

/-- Sum the actual stored cell comparisons in the original finite node order without another observation. -/
def integralDifferenceSum {layer : Layer initial depth} {initialPositive : 0 < initial.span.width}
    (samples : RefinedSamples layer initialPositive) : Canonical :=
  FiniteSum.Fin.sumFin (fun index => samples.integralDifference index)

/-- The actual stored integral-sample differences pay both original dyadic count factors.

Every entry bound derives from its original old request, width and actual
later observation. The original layer count cancels one quarter-radius
factor in the finite quadrance sum. This is a bound on these actual stored
comparisons, without an asserted geometric endpoint telescoping law.
-/
theorem integralDifferenceSum_le {layer : Layer initial depth} {initialPositive : 0 < initial.span.width}
    (samples : RefinedSamples layer initialPositive) :
    Norm.Basic.normSq samples.integralDifferenceSum ≤
      refinementCeiling initial * initial.span.width ^ 2 *
        Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth := by
  exact layer.refinedIntegralDifferenceSum_le initialPositive
    (fun index => (layer.node index).cell.fourthRequest (layer.node_width_positive initialPositive index)) samples
    (fun index => ((layer.node index).cell.fourthRequest_tolerance
      (layer.node_width_positive initialPositive index)).le)

end RefinedSamples

/-- The original cell-comparison ceiling and span compute the fixed scale of its dyadic contraction. -/
def refinementScale {initialAccuracy : AccuracyRequest} (initial : Piece data actual initialAccuracy) :
    Fraction.Rational := refinementCeiling initial * initial.span.width ^ 4

/-- The finite contraction scale is nonnegative using the same original Model regularity and span. -/
theorem refinementScale_nonnegative {initialAccuracy : AccuracyRequest}
    (initial : Piece data actual initialAccuracy) : 0 ≤ refinementScale initial :=
  Arithmetic.mul_nonneg_direct (refinementCeiling_nonnegative initial)
    ((Arithmetic.sq_nonneg_direct (initial.span.width * initial.span.width)).trans_eq (by ring1))

/-- Retain the original certified depth search for the computed spatial cell-comparison scale and positive request. -/
def refinementSelection {initialAccuracy : AccuracyRequest} (initial : Piece data actual initialAccuracy)
    (current : Nat) (request : AccuracyRequest) :
    Geometric.Search.Selection (refinementScale initial) current request.tolerance :=
  Geometric.Search.Selection.build (refinementScale initial) (refinementScale_nonnegative initial)
    current request.tolerance request.positive

/-- Actual stored comparisons at or after the certified search stage meet its original positive finite request. -/
theorem RefinedSamples.requested_error_lt {layer : Layer initial depth}
    {initialPositive : 0 < initial.span.width} (samples : RefinedSamples layer initialPositive)
    {current : Nat} (request : AccuracyRequest)
    (selection : Geometric.Search.Selection (refinementScale initial) current request.tolerance)
    (after : selection.stage ≤ depth) : Norm.Basic.normSq samples.integralDifferenceSum < request.tolerance := by
  have allowance := selection.later_accurate after
  have scalarIdentity : refinementCeiling initial * initial.span.width ^ 2 *
      Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth =
      Geometric.Basic.quarterRadius (refinementScale initial) depth := by
    rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    unfold refinementScale
    ring1
  exact samples.integralDifferenceSum_le.trans_lt (scalarIdentity.trans_lt allowance)

end Layer

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

end
