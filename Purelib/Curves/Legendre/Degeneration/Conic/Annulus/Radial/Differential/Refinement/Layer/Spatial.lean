module

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Piece

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Partition
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Query
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Distance
import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Dyadic
import Purelib.Data.List.Membership
import Purelib.Tactic.Ring

/-! # Actual finer-layer source queries and internally paid sharp spatial geometry

The original scalar Layer supplies its exact pieces and cached source
Readings. Its original endpoint Chain and finite width equation pay actual
neighboring Geometries. Source queries are read from those SAME pieces;
only the sharp clearance and physical Route are constructed here.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Integration.Partition

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

namespace Piece

/-- The original piece's lower endpoint retains its actual original quarter-containment certificate. -/
@[expose] def lowerEndpoint (piece : Piece data actual accuracy) : Endpoint :=
  ⟨piece.span.lower, piece.within piece.span.lower ⟨Fraction.Order.Basic.le_refl _, piece.span.valid⟩⟩

/-- The original piece's upper endpoint retains the actual original closed-span containment certificate. -/
@[expose] def upperEndpoint (piece : Piece data actual accuracy) : Endpoint :=
  ⟨piece.span.upper, piece.within piece.span.upper ⟨piece.span.valid, Fraction.Order.Basic.le_refl _⟩⟩

/-- Package the SAME original source Reading and its factory receipt for the existing spatial Steps constructor. -/
@[expose] def sourceQuery (piece : Piece data actual accuracy) (queried : piece.Queried) :
    { retained : Spatial.Parallel.ReadingAt actual piece.lowerEndpoint //
      Spatial.Parallel.QueryCache actual piece.lowerEndpoint retained } :=
  ⟨piece.source, by
    unfold Spatial.Parallel.QueryCache
    exact queried.readback⟩

/-- The original Steps query view is the identical complete old source, without another requested-time producer. -/
theorem sourceQuery_value (piece : Piece data actual accuracy) (queried : piece.Queried) :
    (piece.sourceQuery queried).val = piece.source := rfl

end Piece

namespace Layer

variable {initial : Piece data actual accuracy} {depth : Nat} (layer : Layer initial depth)

/-- The exact original layer width equation pays every original piece at any chosen sufficient finite depth. -/
theorem width_le (minimum : Nat) (enough : minimum ≤ depth)
    (piece : Piece data actual layer.accuracy) (member : piece ∈ layer.pieces) :
    piece.span.width ^ 2 ≤ Geometric.Basic.quarterRadius 1 minimum := by
  rewrite [layer.widths piece member]
  exact (Geometric.Basic.quarterRadius_scale_mono initial.width_sq_le_one depth).trans
    (Geometric.Basic.quarterRadius_antitone (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1) enough)

variable {start finish : Fraction.Rational}
variable (chain : Interval.Chain start finish (Piece.chartIntervals layer.pieces))
variable (index : Nat) (bound : index < layer.pieces.length) (nextBound : index + 1 < layer.pieces.length)

include chain

/-- The SAME actual neighboring source times differ by the exact retained first span width. -/
theorem next_width :
    (layer.pieces[index + 1]'nextBound).span.lower - (layer.pieces[index]'bound).span.lower =
      (layer.pieces[index]'bound).span.width := by
  rewrite [← layer.seam chain index bound nextBound]
  rfl

/-- The original width and Chain derive the depth-seven sharp-box payment for these literal cached source queries. -/
theorem next_payment (enough : 7 ≤ depth) :
    ((layer.pieces[index + 1]'nextBound).span.lower - (layer.pieces[index]'bound).span.lower) ^ 2 ≤
      Geometric.Basic.quarterRadius 1 7 := by
  rewrite [layer.next_width chain index bound nextBound]
  exact layer.width_le 7 enough _ (List.getElem_mem bound)

/-- Construct the original sharp Geometry on the SAME two retained neighboring Layer source readings.

The original layer depth and endpoint Chain pay clearance internally. This
factory creates the actual sharp box/Route once and performs no time query,
cofactor observation, Source attachment or owner substitution.
-/
def nextGeometry (regular : parameter ≠ criticalValue site) (enough : 7 ≤ depth) :
    Spatial.Parallel.Geometry (layer.pieces[index]'bound).source
      (layer.pieces[index + 1]'nextBound).source regular (layer.next_payment chain index bound nextBound enough) :=
  Spatial.Parallel.Geometry.build _ _ regular (layer.next_payment chain index bound nextBound enough)

/-- The SAME actual new Geometry is precisely the original factory on the two unchanged old source caches. -/
theorem nextGeometry_eq (regular : parameter ≠ criticalValue site) (enough : 7 ≤ depth) :
    layer.nextGeometry chain index bound nextBound regular enough =
      Spatial.Parallel.Geometry.build (layer.pieces[index]'bound).source
        (layer.pieces[index + 1]'nextBound).source regular
        (layer.next_payment chain index bound nextBound enough) := by
  unfold nextGeometry
  rfl

/-- A depth chosen before this Layer pays actual whole-source distances on every edge of its new sharp Geometry. -/
theorem nextGeometry_pointBound (regular : parameter ≠ criticalValue site) (enough : 7 ≤ depth)
    (physical : AccuracyRequest)
    (sufficient : Spatial.Parallel.Geometry.widthMinimum site parameter physical ≤ depth) :
    Polynomial.Geometry.ClearPath.PointBound
      (Transport.Spatial.coordinate site parameter 2 quarter positive (layer.pieces[index]'bound).span.lower)
      physical.tolerance (layer.nextGeometry chain index bound nextBound regular enough).route.path := by
  apply Spatial.Parallel.Geometry.route_pointBound_of_depth _ physical
  have widths := layer.width_le _ sufficient (layer.pieces[index]'bound) (List.getElem_mem bound)
  have scalar :
      ((layer.pieces[index]'bound).span.lower - (layer.pieces[index + 1]'nextBound).span.lower) ^ 2 =
        ((layer.pieces[index + 1]'nextBound).span.lower - (layer.pieces[index]'bound).span.lower) ^ 2 := by ring1
  rewrite [scalar, layer.next_width chain index bound nextBound]
  exact widths

end Layer

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

end
