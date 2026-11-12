module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Cell
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Refinement
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Sampling
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Refined primitive endpoints against the unchanged original chart cell

A later observation on the identical source certificate pays the actual
width-fourth request. The supplied upper observation has that same request.
The original primitive cell theorem compares those prescribed endpoints to
the refined cell, and the retained same-source coefficient comparison pays
the refined integral sample's difference from the original old cell.

Both old and refined Models, their distinct selected observations and their
same original source remain intact. The bound retains the old residual
payment multiplied by the actual squared chart width; no coarse observation
is relabelled as a fourth-power observation or as an arithmetic witness.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Cell

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {span : Interval.Bounds}
variable {firstInside : FixedRootBoxPath.Inside span.lower} {lastInside : FixedRootBoxPath.Inside span.upper}

/-- Refined prescribed primitive endpoints pay their finite error against the literal unchanged old cell integral.

The later source Model supplies its actual width-fourth residual observation.
The original primitive Taylor cell estimate and the same-source integral
comparison derive both terms internally. The old tolerance remains in the
second term with the exact original cell displacement factor.
-/
theorem refined_integral_error_le {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    {data : Waist.Differential.Bounds.Data site parameter specification.differential}
    {source : Transport.Reading actual span.lower firstInside} {accuracy : AccuracyRequest}
    (model : Differential.Cells.Model (span := span) data source accuracy) (widthPositive : 0 < span.width)
    (refined : Differential.Cells.Model.Refined model (model.fourthRequest widthPositive))
    (target : Transport.Reading actual span.upper lastInside)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation
      target.lift.unitRoot (model.fourthRequest widthPositive)) :
    Norm.Basic.normSq
      (Primitive.reading (site := site) primitive quarter span.upper targetSample.reading -
        Primitive.reading (site := site) primitive quarter span.lower refined.val.sample.reading -
          model.cell.integralSample) ≤
      4 * (Taylor.ceiling site parameter primitive model.regular +
        slopeResidualFactor site parameter primitive) * span.width ^ 4 +
      2 * span.width ^ 2 * Differential.Cells.Model.errorBound model (model.fourthRequest widthPositive) := by
  have localBound := integral_error_le specification refined.val target targetSample
    (model.fourthRequest_tolerance widthPositive)
  have integralBound := refined.integral_error_le
  have decomposition :
      Primitive.reading (site := site) primitive quarter span.upper targetSample.reading -
        Primitive.reading (site := site) primitive quarter span.lower refined.val.sample.reading -
          model.cell.integralSample =
      (Primitive.reading (site := site) primitive quarter span.upper targetSample.reading -
        Primitive.reading (site := site) primitive quarter span.lower refined.val.sample.reading -
          refined.val.cell.integralSample) +
      (refined.val.cell.integralSample - model.cell.integralSample) := by ring1
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct localBound integralBound)
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1))

/-- Original primitive and layer coefficient budgets compute a fixed fourth-power ceiling for unchanged old cells. -/
def layerCeiling {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    (_specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    {data : Waist.Differential.Bounds.Data site parameter _specification.differential}
    {initialAccuracy : AccuracyRequest} (initial : Differential.Refinement.Piece data actual initialAccuracy) :
    Fraction.Rational :=
  4 * (Taylor.ceiling site parameter primitive initial.cell.regular +
    slopeResidualFactor site parameter primitive) +
  2 * Differential.Refinement.Layer.refinementCeiling initial

/-- The fixed original primitive/layer ceiling is nonnegative using its retained regularity and original budgets. -/
theorem layerCeiling_nonnegative {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    {data : Waist.Differential.Bounds.Data site parameter specification.differential}
    {initialAccuracy : AccuracyRequest} (initial : Differential.Refinement.Piece data actual initialAccuracy) :
    0 ≤ layerCeiling specification initial :=
  Arithmetic.add_le_add_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (Taylor.ceiling_nonnegative site parameter primitive initial.cell.regular)
        (slopeResidualFactor_nonnegative site parameter primitive initial.cell.regular)))
    (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Differential.Refinement.Layer.refinementCeiling_nonnegative initial))

/-- Actual refined endpoint observations pay the uniform spatial fourth-power error against each retained old node cell.

The original layer derives the common old-versus-new coefficient ceiling
from its quartered request and actual width. The original primitive cell
estimate consumes this node's exact later observation and the retained upper
observation; neither old numerical cell nor selected root reading is replaced.
-/
theorem layer_integral_error_le {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    {data : Waist.Differential.Bounds.Data site parameter specification.differential}
    {initialAccuracy : AccuracyRequest} {initial : Differential.Refinement.Piece data actual initialAccuracy}
    {depth : Nat} (layer : Differential.Refinement.Layer initial depth) (initialPositive : 0 < initial.span.width)
    (piece : Differential.Refinement.Piece data actual layer.accuracy) (member : piece ∈ layer.pieces)
    (refined : Differential.Cells.Model.Refined piece.cell
      (piece.cell.fourthRequest (layer.width_positive initialPositive piece member)))
    {lastInside : FixedRootBoxPath.Inside piece.span.upper}
    (target : Transport.Reading actual piece.span.upper lastInside)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot
      (piece.cell.fourthRequest (layer.width_positive initialPositive piece member))) :
    Norm.Basic.normSq
      (Primitive.reading (site := site) primitive quarter piece.span.upper targetSample.reading -
        Primitive.reading (site := site) primitive quarter piece.span.lower refined.val.sample.reading -
          piece.cell.cell.integralSample) ≤
      layerCeiling specification initial * piece.span.width ^ 4 := by
  have localBound := integral_error_le specification refined.val target targetSample
    (piece.cell.fourthRequest_tolerance (layer.width_positive initialPositive piece member))
  have coefficientBound := layer.refined_integral_error_le initialPositive piece member refined
  have decomposition :
      Primitive.reading (site := site) primitive quarter piece.span.upper targetSample.reading -
        Primitive.reading (site := site) primitive quarter piece.span.lower refined.val.sample.reading -
          piece.cell.cell.integralSample =
      (Primitive.reading (site := site) primitive quarter piece.span.upper targetSample.reading -
        Primitive.reading (site := site) primitive quarter piece.span.lower refined.val.sample.reading -
          refined.val.cell.integralSample) +
      (refined.val.cell.integralSample - piece.cell.cell.integralSample) := by ring1
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct localBound coefficientBound)
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2)).trans_eq (by unfold layerCeiling; ring1))

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Cell

end
