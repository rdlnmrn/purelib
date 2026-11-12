module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Calculus.Jet.Quadratic.Weighted.Bounds
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Data.Vector.Basic
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Fixed physical nodes and weights of the original parallel refinement

Each retained original piece supplies its actual source spatial point and
oriented chart-width times the original base velocity. Finite vectors read
those same pieces without geometric preparation or root sampling. Their
weight quadrances have an internally derived quarter-radius bound, retaining
the original parameter and span throughout same-cycle parameter variation.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib
open Purelib.Algebra
open Purelib.Calculus.Jet
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Approximation
open Purelib.Approximation.Rational

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

namespace Piece

/-- The physical spatial node is the point of this same piece's original requested-time source. -/
@[expose] def spatialPoint (piece : Piece data actual accuracy) : Canonical :=
  (point site parameter 2 (Waist.direction quarter piece.span.lower) positive).base

/-- The oriented physical quadrature weight is the original chart width times its actual source base velocity. -/
@[expose] def weight (piece : Piece data actual accuracy) : Canonical :=
  Stereographic.Tangent.increment piece.span.width *
    Tangent.baseVelocity site parameter 2 quarter piece.span.lower

/-- The original radial velocity bound pays the same piece's physical weight quadrance. -/
theorem weight_normSq_le (piece : Piece data actual accuracy) :
    Norm.Basic.normSq piece.weight ≤
      ((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * piece.span.width ^ 2 := by
  have incrementNorm : Norm.Basic.normSq (Stereographic.Tangent.increment piece.span.width) =
      piece.span.width ^ 2 := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    change piece.span.width * piece.span.width + 0 * 0 = piece.span.width ^ 2
    ring1
  rewrite [weight, Norm.Basic.normSq_mul, incrementNorm]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Tangent.baseVelocity_normSq_le site parameter 2 quarter positive
      (by decide +kernel) (by decide +kernel) piece.span.lower)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq (by ring1)

end Piece

namespace Layer

variable {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy} {depth : Nat}

/-- Read the exact retained original piece at its original finite list index and bound. -/
@[expose] def node (layer : Layer initial depth) (index : Fin layer.pieces.length) :
    Piece data actual layer.accuracy := layer.pieces[index.val]'index.isLt

/-- The original cached path integral sample is the ordered finite sum of the identical retained node cells. -/
theorem integralSample_eq_sumFin (layer : Layer initial depth) :
    layer.model.integralSample =
      FiniteSum.Fin.sumFin (fun index : Fin layer.pieces.length =>
        (layer.node index).cell.cell.integralSample) := by
  have eta : layer.model = Path.Basic.PathModel.mk layer.model.cells := by
    cases layer.model
    rfl
  calc
    _ = (Path.Basic.PathModel.mk layer.model.cells).integralSample :=
      congrArg (fun model => model.integralSample) eta
    _ = (Path.Basic.PathModel.mk
        (Piece.models layer.pieces)).integralSample :=
      congrArg (fun cells => (Path.Basic.PathModel.mk cells).integralSample)
        layer.model_cells
    _ = _ := Path.Basic.PathModel.integralSample_map_eq_sumFin
      layer.pieces Piece.model

/-- Materialize the original layer's fixed physical spatial points without preparing any source again. -/
@[expose] def points (layer : Layer initial depth) : Data.Vector Canonical layer.pieces.length :=
  Data.Vector.Basic.vectorOfFn (fun index => (layer.node index).spatialPoint)

/-- Materialize the original oriented physical weights once for reuse in both source and target sample banks. -/
@[expose] def weights (layer : Layer initial depth) : Data.Vector Canonical layer.pieces.length :=
  Data.Vector.Basic.vectorOfFn (fun index => (layer.node index).weight)

/-- Every materialized physical point is the same retained original piece's spatial point. -/
theorem points_apply (layer : Layer initial depth) (index : Fin layer.pieces.length) :
    layer.points index = (layer.node index).spatialPoint :=
  Data.Vector.Basic.vectorOfFn_apply _ index

/-- Every actual parallel node lies in its original labelled spatial patch independently of refinement depth. -/
theorem points_inside (layer : Layer initial depth) (index : Fin layer.pieces.length) :
    (spatialBox site).Contains (layer.points index) := by
  rewrite [layer.points_apply]
  exact point_inside site parameter 2 (Waist.direction quarter (layer.node index).span.lower) positive
    actual.data.lower actual.data.upper actual.data.bound

/-- Every materialized weight is the same original piece's chart width times actual source velocity. -/
theorem weights_apply (layer : Layer initial depth) (index : Fin layer.pieces.length) :
    layer.weights index = (layer.node index).weight :=
  Data.Vector.Basic.vectorOfFn_apply _ index

/-- Every original physical weight has its internally paid dyadic bound, with one common parameter and initial span. -/
theorem weights_normSq_le (layer : Layer initial depth) (index : Fin layer.pieces.length) :
    Norm.Basic.normSq (layer.weights index) ≤
      Geometric.Basic.quarterRadius
        (((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * initial.span.width ^ 2) depth := by
  rewrite [layer.weights_apply]
  have bound := (layer.node index).weight_normSq_le
  have member : layer.node index ∈ layer.pieces := List.getElem_mem index.isLt
  rewrite [layer.widths (layer.node index) member, Geometric.Basic.quarterRadius_eq_mul_pow] at bound
  exact bound.trans_eq (by
    rewrite [Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1)

/-- A common original entry ceiling bounds weighted Taylor factors on the actual parallel nodes at every depth. -/
theorem weightedFactor_le {increment : Canonical} (layer : Layer initial depth)
    (entries : Data.Vector (Quadratic.Basic.Certificate increment) layer.pieces.length)
    (ceiling : Fraction.Rational) (nonnegative : 0 ≤ ceiling)
    (bounded : ∀ index, (entries index).factor ≤ ceiling) :
    Quadratic.Basic.Certificate.weightedFactor layer.weights entries ≤
      (((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * initial.span.width ^ 2) * ceiling :=
  Quadratic.Basic.Certificate.dyadic_weightedFactor_le layer.weights entries depth layer.count _ ceiling
    nonnegative (fun index => layer.weights_normSq_le index) bounded

/-- Actual parallel weights and uniform entry factors pay one common parameter-Taylor remainder independent of depth. -/
theorem weighted_remainder_le {increment : Canonical} (layer : Layer initial depth)
    (entries : Data.Vector (Quadratic.Basic.Certificate increment) layer.pieces.length)
    (ceiling : Fraction.Rational) (nonnegative : 0 ≤ ceiling)
    (bounded : ∀ index, (entries index).factor ≤ ceiling) :
    Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun index => layer.weights index * (entries index).remainder)) ≤
      ((((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * initial.span.width ^ 2) * ceiling) *
        Norm.Basic.normSq increment ^ 2 :=
  Quadratic.Basic.Certificate.dyadic_weighted_remainder_le layer.weights entries depth layer.count _ ceiling
    nonnegative (fun index => layer.weights_normSq_le index) bounded

end Layer

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
