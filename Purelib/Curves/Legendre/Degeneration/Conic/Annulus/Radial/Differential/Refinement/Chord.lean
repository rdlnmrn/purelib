module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Spatial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Quadrature
public import Purelib.Polynomial.Geometry.ClearPath.Quadrature
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Tactic.Ring

/-! # Actual curved cell samples and their oriented spatial chord quadrature

Each old scalar cell retains its original cofactor observation. One cached
ordinary spatial scalar coefficient consumes that SAME old reading. The
original oriented tangent and its actual endpoint chord differ by the
original fourth-power remainder. The resulting finite-layer comparison has
an internally computed decaying bound and sufficient finite stage.

A retained original spatial Route has exactly the same constant-coefficient
edge quadrature. This scalar statement is separate from the actual local
Source polynomial integrals and from any chart-to-affine integral theorem.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential (Paths.polynomial parameter)}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

/-- The SAME original gap and independently derived spatial coefficient ceiling pay the tangent/chord error. -/
@[expose] def chordScale (data : Waist.Differential.Bounds.Data site parameter differential) : Fraction.Rational :=
  ((25 / 4) * data.gapNorm) * Primitive.Bounds.magnitude data

/-- Intrinsic regularity makes the retained scalar chord comparison scale nonnegative. -/
theorem chordScale_nonnegative (data : Waist.Differential.Bounds.Data site parameter differential)
    (regular : parameter ≠ criticalValue site) : 0 ≤ chordScale data :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 25 / 4) data.gapNorm_nonnegative)
    (Primitive.Bounds.magnitude_nonnegative data regular)

namespace Piece

/-- The actual oriented physical chord weight reads the SAME original chart span endpoints. -/
@[expose] def chordWeight (piece : Piece data actual accuracy) : Canonical :=
  (point site parameter 2 (Waist.direction quarter piece.span.upper) positive).base - piece.spatialPoint

/-- The actual tangent weight and physical chord weight pay the original fourth-power geometric remainder. -/
theorem weight_chord_error_le (piece : Piece data actual accuracy) :
    Norm.Basic.normSq (piece.weight - piece.chordWeight) ≤
      ((25 / 4) * data.gapNorm) * piece.span.width ^ 4 := by
  have paid := Tangent.base_remainder_normSq_le site parameter 2 quarter positive
    (of_decide_eq_true rfl) (Fraction.Order.Basic.le_refl 2) piece.span.lower piece.span.width
  have upper : piece.span.lower + piece.span.width = piece.span.upper := by
    change piece.span.lower + (piece.span.upper - piece.span.lower) = piece.span.upper
    ring1
  rewrite [upper, ← data.gapNorm_eq] at paid
  change Norm.Basic.normSq (piece.chordWeight - piece.weight) ≤ _ at paid
  rewrite [Norm.Bounds.normSq_sub_symm]
  exact paid

/-- Weight the SAME retained old scalar coefficient by the actual oriented physical endpoint displacement. -/
@[expose] def chordSample (piece : Piece data actual accuracy) (spatial : Cells.Model.Spatial piece.cell) : Canonical :=
  piece.chordWeight * spatial.value

/-- The old curved-cell sample and its actual spatial chord quadrature obey the internally paid fourth-power bound. -/
theorem chord_error_le (piece : Piece data actual accuracy) (spatial : Cells.Model.Spatial piece.cell) :
    Norm.Basic.normSq (piece.cell.cell.integralSample - piece.chordSample spatial) ≤
      chordScale data * piece.span.width ^ 4 := by
  rewrite [spatial.integralSample_eq]
  change Norm.Basic.normSq (piece.weight * spatial.value - piece.chordWeight * spatial.value) ≤ _
  rewrite [show piece.weight * spatial.value - piece.chordWeight * spatial.value =
    (piece.weight - piece.chordWeight) * spatial.value by ring1, Norm.Basic.normSq_mul]
  have paid := Fraction.Order.Arithmetic.mul_le_mul_direct piece.weight_chord_error_le spatial.normSq_le
    (Norm.Basic.normSq_nonneg spatial.value)
    ((Norm.Basic.normSq_nonneg (piece.weight - piece.chordWeight)).trans piece.weight_chord_error_le)
  exact paid.trans_eq (by unfold chordScale; ring1)

/-- The SAME original Route's ordered constant-coefficient edge samples equal this physical chord sample.

The whole retained Geometry and its original source/target Reading pair
remain inputs. Only the scalar edge weights telescope; no root reading,
source polynomial, primitive constant or path integral is identified here.
-/
theorem routeSample_eq (piece : Piece data actual accuracy) (spatial : Cells.Model.Spatial piece.cell)
    (target : Transport.Reading actual piece.span.upper
      (piece.within piece.span.upper ⟨piece.span.valid, Fraction.Order.Basic.le_refl _⟩))
    {payment : piece.span.width ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (geometry : Transport.Spatial.Parallel.Geometry piece.source target piece.cell.regular payment) :
    geometry.route.path.constantSample spatial.value = piece.chordSample spatial := by
  rewrite [geometry.route.path.constantSample_eq]
  rfl

/-- The particular retained Route's scalar quadrature pays the same old curved sample's computed geometric bound. -/
theorem routeSample_error_le (piece : Piece data actual accuracy) (spatial : Cells.Model.Spatial piece.cell)
    (target : Transport.Reading actual piece.span.upper
      (piece.within piece.span.upper ⟨piece.span.valid, Fraction.Order.Basic.le_refl _⟩))
    {payment : piece.span.width ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (geometry : Transport.Spatial.Parallel.Geometry piece.source target piece.cell.regular payment) :
    Norm.Basic.normSq (piece.cell.cell.integralSample - geometry.route.path.constantSample spatial.value) ≤
      chordScale data * piece.span.width ^ 4 := by
  rewrite [piece.routeSample_eq spatial target geometry]
  exact piece.chord_error_le spatial

end Piece

namespace Layer

variable {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy} {depth : Nat}

/-- One scalar cache per SAME retained original layer node; no source or observation is reconstructed. -/
abbrev SpatialSamples (layer : Layer initial depth) :=
  Data.Vector.DependentVector (fun index => Cells.Model.Spatial (layer.node index).cell)

/-- Compute and retain each original node's scalar spatial coefficient once from its SAME old cofactor sample. -/
def spatialSamples (layer : Layer initial depth) : SpatialSamples layer :=
  Data.Vector.DependentVector.ofFn (fun index => Cells.Model.Spatial.build (layer.node index).cell)

/-- The retained scalar at each original node is exactly the one completed scalar factory, not another observation. -/
theorem spatialSamples_apply (layer : Layer initial depth) (index : Fin layer.pieces.length) :
    layer.spatialSamples.get index = Cells.Model.Spatial.build (layer.node index).cell :=
  Data.Vector.DependentVector.ofFn_get _ index

namespace SpatialSamples

/-- Sum the actual spatial chord samples in the SAME original layer order using its retained scalar caches. -/
def sample {layer : Layer initial depth} (samples : SpatialSamples layer) : Canonical :=
  FiniteSum.Fin.sumFin (fun index => (layer.node index).chordSample (samples.get index))

/-- The original layer count cancels one fourth-power factor of every actual tangent/chord error. -/
theorem error_le {layer : Layer initial depth} (samples : SpatialSamples layer) :
    Norm.Basic.normSq (layer.model.integralSample - samples.sample) ≤
      Geometric.Basic.quarterRadius (chordScale data * initial.span.width ^ 4) depth := by
  have bounded (index : Fin layer.pieces.length) :
      Norm.Basic.normSq ((layer.node index).cell.cell.integralSample -
        (layer.node index).chordSample (samples.get index)) ≤
      chordScale data * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2 := by
    have member : layer.node index ∈ layer.pieces := List.getElem_mem index.isLt
    have fourth : (layer.node index).span.width ^ 4 =
        Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2 := by
      calc
        _ = ((layer.node index).span.width ^ 2) ^ 2 := by ring1
        _ = _ := congrArg (fun width : Fraction.Rational => width ^ 2) (layer.widths _ member)
    exact ((layer.node index).chord_error_le (samples.get index)).trans_eq
      (congrArg (fun width : Fraction.Rational => chordScale data * width) fourth)
  have summed := Norm.Sum.Indexed.normSq_sumFin_le
    (fun index => (layer.node index).cell.cell.integralSample -
      (layer.node index).chordSample (samples.get index))
    (chordScale data * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2) bounded
  have count : (layer.pieces.length : Fraction.Rational) = ((2 ^ depth : Nat) : Fraction.Rational) :=
    congrArg (fun size : Nat => (size : Fraction.Rational)) layer.count
  have cancellation : (layer.pieces.length : Fraction.Rational) ^ 2 *
      (chordScale data * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2) =
      Geometric.Basic.quarterRadius (chordScale data * initial.span.width ^ 4) depth := by
    rewrite [count]
    calc
      _ = (chordScale data * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth) *
          (((2 ^ depth : Nat) : Fraction.Rational) *
            (((2 ^ depth : Nat) : Fraction.Rational) *
              Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth)) := by ring1
      _ = (chordScale data * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth) *
          initial.span.width ^ 2 := congrArg
        (fun width : Fraction.Rational => (chordScale data *
          Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth) * width)
        (Geometric.DyadicCount.dyadic_count_cancel (initial.span.width ^ 2) depth)
      _ = _ := by
        rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
  unfold sample
  rewrite [layer.integralSample_eq_sumFin, ← FiniteSum.Fin.sumFin_sub]
  exact summed.trans_eq cancellation

end SpatialSamples

/-- The original computed scalar chord ceiling and initial chart width give the finite decaying request scale. -/
@[expose] def chordErrorScale (initial : Piece data actual initialAccuracy) : Fraction.Rational :=
  chordScale data * initial.span.width ^ 4

/-- The original regularity and chart span make the computed finite request scale nonnegative. -/
theorem chordErrorScale_nonnegative (initial : Piece data actual initialAccuracy) : 0 ≤ chordErrorScale initial :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (chordScale_nonnegative data initial.cell.regular)
    (Fraction.Order.Arithmetic.pow_nonneg_direct initial.span.width_nonneg 4)

/-- Compute a sufficient finite comparison stage from the actual original caches before constructing a new layer. -/
def chordSelection (initial : Piece data actual initialAccuracy) (current : Nat) (request : AccuracyRequest) :
    Geometric.Search.Selection (chordErrorScale initial) current request.tolerance :=
  Geometric.Search.Selection.build (chordErrorScale initial) (chordErrorScale_nonnegative initial)
    current request.tolerance request.positive

/-- Any actual later original layer and its SAME retained scalar caches meet the internally computed request. -/
theorem SpatialSamples.requested_error_lt {layer : Layer initial depth} (samples : SpatialSamples layer)
    {current : Nat} (request : AccuracyRequest)
    (selection : Geometric.Search.Selection (chordErrorScale initial) current request.tolerance)
    (after : selection.stage ≤ depth) :
    Norm.Basic.normSq (layer.model.integralSample - samples.sample) < request.tolerance :=
  samples.error_le.trans_lt (selection.later_accurate after)

end Layer

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
