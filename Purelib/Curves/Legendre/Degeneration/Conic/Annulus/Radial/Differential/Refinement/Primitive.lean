module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Program
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
public import Purelib.Data.Rat.List.Maximum
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Polynomial.Gaussian.Path.Primitive.Dyadic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Taylor
import Purelib.Data.List.Map
import Purelib.Data.Rat.Interval.Bisection
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Tactic.Ring

/-! # Prescribed primitive increments on actual regular parallel refinements

Every midpoint split retains the same chart endpoints. Their arbitrary
prescribed primitive values telescope on the exact original numerical cells,
and this identity is preserved through every constructed dyadic layer.
The finite integral estimate reuses the existing primitive comparison and
its exact count cancellation. Original radial geometry pays finite spatial
primitive Taylor errors, retaining the actual sampled coefficient residual.
Sheet-compatible residual decay and arbitrary-accuracy integral agreement
remain separate constructions.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.Dyadic
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.List
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Riemann.RootContinuation

open Purelib.Algebra.Quadratic (Pair)
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate (DensePrimitive)
open Purelib.Polynomial.Bounds (Horner)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

namespace Split

/-- The two original midpoint children telescope any prescribed chart primitive to their parent's endpoints. -/
theorem primitive_incrementSum {span : Interval.Bounds} {inside : FixedRootBoxPath.Inside span.lower}
    {source : Transport.Reading actual span.lower inside} {parent : Cells.Model data source accuracy}
    {within : ∀ time, span.Contains time → FixedRootBoxPath.Inside time}
    (split : Split parent within) (primitive : Canonical → Canonical) :
    Primitive.incrementSum primitive split.children.cells =
      primitive parent.cell.finish - primitive parent.cell.start := by
  change primitive ⟨Interval.Bisection.midpoint span, 0⟩ - primitive ⟨span.lower, 0⟩ +
    (primitive ⟨span.upper, 0⟩ - primitive ⟨Interval.Bisection.midpoint span, 0⟩ + 0) =
      primitive ⟨span.upper, 0⟩ - primitive ⟨span.lower, 0⟩
  ring1

end Split

namespace Steps

/-- The exact completed ordered midpoint splits preserve every original prescribed primitive increment sum. -/
theorem primitive_incrementSum (primitive : Canonical → Canonical) :
    {parents : List (Piece data actual accuracy)} → (steps : Steps parents) →
      Primitive.incrementSum primitive (Piece.models steps.children) =
        Primitive.incrementSum primitive (Piece.models parents)
  | _, .nil => rfl
  | parent :: parents, .cons split tail => by
      change Primitive.incrementSum primitive
        (Piece.models (Piece.children parent split ++ tail.children)) =
          primitive parent.model.finish - primitive parent.model.start +
            Primitive.incrementSum primitive (Piece.models parents)
      rewrite [Piece.models, Map.map_append, Primitive.incrementSum_append]
      change Primitive.incrementSum primitive split.children.cells +
        Primitive.incrementSum primitive (Piece.models tail.children) = _
      rewrite [split.primitive_incrementSum primitive, tail.primitive_incrementSum primitive]
      rfl

end Steps

namespace Layer

/-- The next exact original cached layer preserves the prescribed primitive increment sum of its retained parent. -/
theorem next_primitive_incrementSum {initialAccuracy : AccuracyRequest}
    {initial : Piece data actual initialAccuracy} {depth : Nat} (layer : Layer initial depth)
    (steps : Steps layer.pieces) (primitive : Canonical → Canonical) :
    Primitive.incrementSum primitive (layer.next steps).model.cells =
      Primitive.incrementSum primitive layer.model.cells := by
  rewrite [(layer.next steps).model_cells, layer.model_cells]
  exact steps.primitive_incrementSum primitive

/-- Compute a finite bound for the actual sampled coefficient residuals of this identical retained layer.

Every residual consumes the original cell center and original curved source
time. The maximum uses the owned nonnegative finite-list fold and does not
prepare another geometric reading or sample a numerical process.
-/
@[expose] def primitiveResidual {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy}
    {depth : Nat} (layer : Layer initial depth) (polynomial : CoefficientPolynomial) : Fraction.Rational :=
  Data.Rat.List.Maximum.nonnegativeMaximum
    (layer.pieces.map fun piece => piece.cell.primitiveResidual polynomial)

/-- Every original scalar cell's actual coefficient residual is bounded by that same finite layer maximum. -/
theorem le_primitiveResidual {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy}
    {depth : Nat} (layer : Layer initial depth) (polynomial : CoefficientPolynomial)
    (piece : Piece data actual layer.accuracy) (member : piece ∈ layer.pieces) :
    piece.cell.primitiveResidual polynomial ≤ layer.primitiveResidual polynomial :=
  Data.Rat.List.Maximum.le_nonnegativeMaximum_of_mem (Map.mem_map.mpr ⟨piece, member, rfl⟩)

end Layer

namespace Piece

/-- Original ordered dyadic spans telescope prescribed chart values to the same initial endpoints.

The optional exact view defaults to the complete original factory layer.
A supplied retained layer instead needs only its actual ordered span
provenance. Readback identifies its same cached numerical cells with the
existing original dyadic increment list, whose original sum theorem pays
the endpoints without reconstructing scalar cells or a replacement path.
-/
theorem layerAt_primitive_incrementSum (initial : Piece data actual accuracy)
    (primitive : Canonical → Canonical) (depth : Nat)
    (layer : {retained : Layer initial depth // retained.pieces.map (fun piece => piece.span) =
        Interval.Bisection.parts depth initial.span} := ⟨initial.layerAt depth, initial.layerAt_spans depth⟩) :
    Primitive.incrementSum primitive layer.val.model.cells =
      primitive initial.model.finish - primitive initial.model.start := by
  have readback : ∀ pieces : List (Piece data actual layer.val.accuracy),
      Primitive.incrementSum primitive (Piece.models pieces) =
        gaussianSum ((pieces.map (fun piece => piece.span)).map
          (fun span => primitive ⟨span.upper, 0⟩ - primitive ⟨span.lower, 0⟩)) := by
    intro pieces
    induction pieces with
    | nil => rfl
    | cons piece pieces inductionHypothesis =>
        exact congrArg (fun total => primitive ⟨piece.span.upper, 0⟩ -
          primitive ⟨piece.span.lower, 0⟩ + total) inductionHypothesis
  have retained := congrArg (Primitive.incrementSum primitive) layer.val.model_cells
  have spans := congrArg (fun intervals : List Interval.Bounds =>
    gaussianSum (intervals.map (fun span => primitive ⟨span.upper, 0⟩ - primitive ⟨span.lower, 0⟩))) layer.property
  have increments := congrArg gaussianSum
    (DyadicPrimitivePaths.dyadicIncrements_eq_parts (fun time => primitive ⟨time, 0⟩) depth initial.span).symm
  exact ((retained.trans (readback layer.val.pieces)).trans spans).trans
    (increments.trans (DyadicPrimitivePaths.dyadicIncrements_sum
      (fun time => primitive ⟨time, 0⟩) depth initial.span.lower initial.span.upper))

/-- Paid original per-cell errors give a prescribed primitive endpoint estimate on the same finite parallel layer.

The exact original count and internally proved endpoint telescoping discharge
the corresponding hypotheses of the generic dyadic primitive comparison.
The supplied local payments still concern the original numerical cells and
the independently prescribed primitive readings at their chart endpoints.
-/
theorem primitive_integral_error_le (initial : Piece data actual accuracy)
    (primitive : Canonical → Canonical) (depth : Nat)
    (movement taylor coefficientError : Fraction.Rational)
    (bounded : ∀ cell ∈ (initial.layerAt depth).model.cells,
      Norm.Basic.normSq (primitive cell.finish - primitive cell.start - cell.integralSample) ≤
        taylor * Geometric.Basic.quarterRadius movement depth ^ 2 +
          coefficientError * Geometric.Basic.quarterRadius movement depth) :
    Norm.Basic.normSq (primitive initial.model.finish - primitive initial.model.start -
      (initial.layerAt depth).model.integralSample) ≤
        taylor * movement * Geometric.Basic.quarterRadius movement depth + coefficientError * movement := by
  have estimate := Primitive.Dyadic.dyadic_integral_error_le primitive (initial.layerAt depth).model
    (initial.layerAt_primitive_incrementSum primitive depth) depth (initial.layerAt depth).model_count
      movement taylor coefficientError (by
        intro cell member
        rewrite [← Norm.Basic.normSq_eq_canonical]
        exact bounded cell member)
  rewrite [Norm.Basic.normSq_eq_canonical]
  exact estimate

end Piece

namespace Layer

/-- A retained layer with actual dyadic spans bounds its scalar integral by a spatial primitive boundary and residuals.

The supplied domain contains the entire original initial interval; the
actual finite dyadic subintervals derive every endpoint domain internally.
Original radial tangent remainders pay every local geometric error. The
original dyadic widths, ordered telescoping and cell count pay the
finite sum. The supplied Horner cache and exact retained residual maximum
concern this same original layer; the default computes its finite fold.
No decay of the sampled coefficient residual is asserted.
-/
theorem spatialPrimitive_error_le {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy}
    {depth : Nat} (layer : Layer initial depth)
    (spans : layer.pieces.map (fun piece => piece.span) = Interval.Bisection.parts depth initial.span)
    {polynomial : CoefficientPolynomial} {box : Purelib.Geometry.Rational.Box}
    (primitive : DensePrimitive polynomial box) (bounds : Horner)
    (bounds_eq : bounds = Dense.Gaussian.Bounds.Box.denseHornerNormBounds polynomial box)
    (domain : ∀ time, initial.span.Contains time → box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter time) positive).base)
    (residual : {retained : Fraction.Rational // retained = layer.primitiveResidual polynomial} :=
      ⟨layer.primitiveResidual polynomial, rfl⟩) :
    Norm.Basic.normSq (primitive.value.eval
        (Radial.point site parameter 2 (Waist.direction quarter initial.span.upper) positive).base -
      primitive.value.eval (Radial.point site parameter 2 (Waist.direction quarter initial.span.lower) positive).base -
      layer.model.integralSample) ≤
        4 * (primitive.remainderBound * ((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) ^ 2 +
          bounds.value * ((25 / 4) * Norm.Basic.normSq (halfGap site parameter))) *
            initial.span.width ^ 2 * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth +
              2 * residual.val * initial.span.width ^ 2 := by
  let chartPrimitive (time : Canonical) := primitive.value.eval
    (Radial.point site parameter 2 (Waist.direction quarter time.re) positive).base
  have telescopes := initial.layerAt_primitive_incrementSum chartPrimitive depth ⟨layer, spans⟩
  have estimate := Primitive.Dyadic.dyadic_integral_error_le chartPrimitive layer.model telescopes depth
    layer.model_count (initial.span.width ^ 2)
    (4 * (primitive.remainderBound * ((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) ^ 2 +
      bounds.value * ((25 / 4) * Norm.Basic.normSq (halfGap site parameter))))
    (2 * residual.val) (by
      intro cell member
      rewrite [layer.model_cells] at member
      rcases Map.mem_map.mp member with ⟨piece, pieceMember, rfl⟩
      have partMember : piece.span ∈ Interval.Bisection.parts depth initial.span := by
        rewrite [← spans]
        exact Map.mem_map.mpr ⟨piece, pieceMember, rfl⟩
      have firstInside := domain piece.span.lower
        (Interval.Bisection.parts_subset depth initial.span partMember
          (show piece.span.Contains piece.span.lower from ⟨le_rfl, piece.span.valid⟩))
      have lastInside := domain piece.span.upper
        (Interval.Bisection.parts_subset depth initial.span partMember
          (show piece.span.Contains piece.span.upper from ⟨piece.span.valid, le_rfl⟩))
      have bound := piece.cell.primitive_boundary_error_le primitive bounds bounds_eq firstInside lastInside
      have fourthPower : (piece.span.upper - piece.span.lower) ^ 4 = (piece.span.width ^ 2) ^ 2 := by
        unfold Interval.Bounds.width
        ring1
      rewrite [fourthPower] at bound
      change Norm.Basic.normSq (chartPrimitive piece.model.finish - chartPrimitive piece.model.start -
        piece.model.integralSample) ≤ _ at bound
      have residualBound : piece.cell.primitiveResidual polynomial ≤ residual.val := by
        rewrite [residual.property]
        exact layer.le_primitiveResidual polynomial piece pieceMember
      have paid := Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct residualBound
          (by decide +kernel : (0 : Fraction.Rational) ≤ 2))
        (Arithmetic.sq_nonneg_direct piece.span.width)
      change 2 * piece.cell.primitiveResidual polynomial * (piece.span.upper - piece.span.lower) ^ 2 ≤ _ at paid
      have combined := bound.trans
        (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) paid)
      rewrite [layer.widths piece pieceMember] at combined
      rewrite [← Norm.Basic.normSq_eq_canonical]
      exact combined)
  rewrite [Norm.Basic.normSq_eq_canonical]
  exact estimate

end Layer

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
