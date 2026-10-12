module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Semiring.Normalization
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Approximation.Budget.SquaredVariationRadius
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInverseModelOverlap
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples
import Purelib.Riemann.Integration.UniformPreparedPrimitives
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring
public import Purelib.Riemann.Normalization.InverseRootComparison

open Purelib

open Purelib.Approximation.Budget

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Data.Rat.Bounds

open Purelib.Geometry

open Purelib.Geometry.Rational.Box.Square.Centered

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization.InverseRootPolynomial

public section

/-!
# Uniform reciprocal models from a retained source inverse polynomial

One source primitive patch already covers its entire prepared parent. Refine
its inverse polynomial twice and use its values at the finitely many cuts as
reciprocal seeds, with the exact coordinate factor. A common radius follows
from a fixed coefficient bound; it does not depend on a newly isolated owner
or on a cut's continuation clearance. The source occurrence is retained.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels

open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model Gaussian Coordinate Box)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial (eval_constant)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential}

set_option genInjectivity false in
/-- Everything used by every reciprocal cut is computed once per retained parent. The fixed source inverse polynomial is
shared by all those cuts.

The original source polynomial is refined twice and cached with its exact residual bound. Each reciprocal cut uses the
same positive radius, slope and inverse-value ceiling from that retained parent. -/
structure Data (patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent) (count : Nat) where
  /-- The original source parent lies on the retained ambient boundary. -/ boundary :
    PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)
  /-- The original source endpoint lies in the retained primitive neighborhood. -/ finishInside : (patch.neighborhood
    count).box.Contains (parent.edge.point 1)
  /-- The cached twice-refined original source inverse polynomial. -/ source : InverseRootPolynomial.Model
    curve.polynomial (patch.neighborhood count).base.box
  /-- The cached source model is exactly refinement two of the original neighborhood base. -/ source_eq : source =
    (patch.neighborhood count).base.refine 2
  /-- The retained source squared residual bound is at most one over 256. -/ source_small : source.bound ≤ 1 / 256
  /-- The cached common ceiling for the original source inverse polynomial values. -/ inverseUpper :
    InverseRootPolynomial.Coordinate
  /-- The cached inverse ceiling is the exact original neighborhood derivative-bound ceiling. -/ inverseUpper_eq :
    inverseUpper = (SeededPrimitiveBounds.derivativeBounds (patch.neighborhood count).base).inverseUpper
  /-- The retained inverse ceiling is strictly positive. -/ inverseUpper_positive : 0 < inverseUpper
  /-- The cached common squared-norm ceiling for all original reciprocal seeds. -/ seedUpper :
    InverseRootPolynomial.Coordinate
  /-- The seed ceiling is exactly the original ambient norm bound raised to genus plus one times the retained inverse
    ceiling. -/ seedUpper_eq : seedUpper = (Cuts.Ambient curve).normSqBound ^ (genus + 1) * inverseUpper
  /-- The retained reciprocal seed ceiling is nonnegative. -/ seedUpper_nonnegative : 0 ≤ seedUpper
  /-- The retained fixed rational square containing all reciprocal cut boxes. -/ ambient : InverseRootPolynomial.Box
  /-- The retained ambient square is exactly the symmetric square of radius two. -/ ambient_eq : ambient =
    Rational.Box.symmetric 2 (by decide)
  /-- The cached squared-norm Lipschitz bound of the original reciprocal polynomial. -/ slope :
    InverseRootPolynomial.Coordinate
  /-- The cached slope equals the original polynomial's exact bound on the retained ambient square. -/ slope_eq : slope
    = Dense.Gaussian.Bounds.Box.denseLipschitzBound (HyperellipticReciprocal.polynomial curve) ambient
  /-- The retained polynomial slope bound is strictly positive. -/ slope_positive : 0 < slope
  /-- The retained positive common radius for every original reciprocal cut. -/ radius :
    InverseRootPolynomial.Coordinate
  /-- The common radius is the finite squared-variation radius for the retained polynomial slope and seed ceiling. -/
    radius_eq : radius = SquaredVariationRadius.squaredVariationRadius (1 / 64) (slope * seedUpper ^ 2)
  /-- The retained common reciprocal cut radius is strictly positive. -/ radius_positive : 0 < radius

constructive_injectivity Data

namespace Data

variable {patch : PreparedPatch parent}

/-- Cache one refined source inverse polynomial and uniform reciprocal seed bounds for the original prepared parent.

The radius is computed from the original polynomial slope and seed ceiling and is shared by every retained source cut.
-/
@[expose] def build (patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent) (count : Nat) (boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve))
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1)) :
      Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count := by
  let source := (patch.neighborhood count).base.refine 2
  let inverseUpper := (SeededPrimitiveBounds.derivativeBounds (patch.neighborhood count).base).inverseUpper
  have inversePositive := (SeededPrimitiveBounds.derivativeBounds (patch.neighborhood count).base).inverseUpper_positive
  let seedUpper := (Cuts.Ambient curve).normSqBound ^ (genus + 1) * inverseUpper
  have seedNonnegative : 0 ≤ seedUpper := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Cuts.Ambient curve).normSqBound_nonneg _) inversePositive.le
  let ambient := Rational.Box.symmetric 2 (by decide)
  let slope := Dense.Gaussian.Bounds.Box.denseLipschitzBound (HyperellipticReciprocal.polynomial curve) ambient
  let radius := SquaredVariationRadius.squaredVariationRadius (1 / 64) (slope * seedUpper ^ 2)
  refine ⟨boundary, finishInside, source, rfl, ?_, inverseUpper, rfl, inversePositive,
    seedUpper, rfl, seedNonnegative, ambient, rfl, slope, rfl,
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos _ _, radius, rfl,
    SquaredVariationRadius.squaredVariationRadius_positive _ _⟩
  change ((patch.neighborhood count).base.model.refine 2).bound ≤ 1 / 256
  rw [Model.refine_bound, Geometric.Basic.quarterRadius_eq_mul_pow]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (patch.neighborhood count).base.model.bound_small (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ (1 / 4) ^ 2)).trans_eq (by decide +kernel)

/-- Every bounded source parameter lies in the retained source inverse-model box. -/
theorem source_inside (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count)
  {parameter : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (patch.neighborhood count).base.box.Contains (parent.edge.point parameter) :=
  (patch.neighborhood count).box_refines.contains
    (PreparedPrimitivePaths.point_inside_of_endpoints parent (patch.neighborhood count).box
      (patch.start_inside count) data.finishInside inside)

/-- The retained source inverse polynomial satisfies its cached squared-norm ceiling along the original parent. -/
theorem source_norm_le (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count)
  {parameter : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (data.source.value.eval (parent.edge.point parameter)) ≤ data.inverseUpper
      := by
  rw [data.inverseUpper_eq]
  have scalar := (SeededPrimitiveBounds.derivativeBounds (patch.neighborhood count).base).value_le data.source
    (data.source_inside inside)
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

/-- Read the shared source inverse polynomial at the original parameter and multiply by the exact reciprocal coordinate
power. -/
@[expose] def seed (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count) (parameter :
  InverseRootPolynomial.Coordinate) : Gaussian :=
  parent.edge.point parameter ^ (genus + 1) * data.source.value.eval (parent.edge.point parameter)

/-- Every retained source-parameter seed satisfies the cached common squared-norm ceiling. -/
theorem seed_norm_le (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count) {parameter
  : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (data.seed parameter) ≤ data.seedUpper := by
  rw [seed, Data.Gaussian.Norm.Basic.normSq_mul,
    Power.normSq_pow, data.seedUpper_eq]
  exact Fraction.Order.Arithmetic.mul_le_mul_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Rational.Box.normSq_le_normSqBound (data.boundary.point inside).1) _)
    (data.source_norm_le inside) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Cuts.Ambient curve).normSqBound_nonneg _)

/-- The reciprocal seed is tied to the actual source model by an exact equation, stronger than independently choosing a
small square residual.

The original parent point is nonzero. Its reciprocal coordinate powers cancel in the same Gaussian multiplication
operations, identifying the retained shared-source seed without a new root or sign choice. -/
theorem seed_transport (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count)
  {parameter : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    ReciprocalRootNames.factor genus (parent.edge.point parameter) * data.seed parameter =
      data.source.value.eval (parent.edge.point parameter) := by
  have nonzero := PreparedExteriorReciprocal.parent_point_nonzero data.boundary inside
  have cancel : (parent.edge.point parameter)⁻¹ ^ (genus + 1) * parent.edge.point parameter ^ (genus + 1) = 1 := by
    rw [← Algebra.Semiring.Normalization.product_pow, Data.Gaussian.Basic.mul_comm _ (parent.edge.point parameter),
      Algebra.Field.ExplicitField.mul_inv_cancel _ nonzero, one_pow]
  dsimp only [ReciprocalRootNames.factor, seed]
  rw [← Data.Gaussian.Basic.mul_assoc, cancel, Data.Gaussian.Basic.one_mul]

/-- The retained reciprocal seed has squared residual at most one over 64 at its original reciprocal center. -/
theorem seed_residual (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count)
  {parameter : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (1 - (HyperellipticReciprocal.polynomial curve).eval (parent.edge.point
      parameter)⁻¹ * data.seed parameter ^ 2) ≤ 1 / 64 := by
  have nonzero := PreparedExteriorReciprocal.parent_point_nonzero data.boundary inside
  have identity : 1 - (HyperellipticReciprocal.polynomial curve).eval (parent.edge.point parameter)⁻¹ * data.seed
    parameter ^ 2 =
      1 - curve.polynomial.eval (parent.edge.point parameter) * (data.source.value.eval (parent.edge.point parameter)) ^
        2 := by
    rw [← ReciprocalRootNames.factor_identity curve _ nonzero, ← data.seed_transport inside]
    ring1
  rw [identity, ← data.source.residual_eq, Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact ((data.source.residualBound _ (data.source_inside inside)).trans data.source_small).trans (by decide +kernel)

/-- The retained common reciprocal radius is at most one. -/
theorem radius_le_one (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count) :
  data.radius ≤ 1 := by
  rw [data.radius_eq]
  exact SquaredVariationRadius.squaredVariationRadius_le_one _ _

/-- The retained common-radius square centered at the original parameter's reciprocal point. -/
@[expose] def box (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count) (parameter :
  InverseRootPolynomial.Coordinate) : Box :=
  BoxTransport.centeredBox (parent.edge.point parameter)⁻¹ data.radius data.radius_positive.le

/-- Each original reciprocal center has real and imaginary coordinates between minus one and one. -/
private theorem center_bounds (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count)
  {parameter : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    -1 ≤ ((parent.edge.point parameter)⁻¹).re ∧ ((parent.edge.point parameter)⁻¹).re ≤ 1 ∧
      -1 ≤ ((parent.edge.point parameter)⁻¹).im ∧ ((parent.edge.point parameter)⁻¹).im ≤ 1 := by
  have bound : Data.Gaussian.Norm.Basic.normSq (parent.edge.point parameter)⁻¹ ≤ (1 :
    InverseRootPolynomial.Coordinate) ^ 2 := by
    rw [one_pow]
    exact Reciprocal.Bounds.disk_unit_bound
      (ReciprocalExteriorCollar.inverse_inDisk curve (data.boundary.point inside))
  have realBound : ((parent.edge.point parameter)⁻¹).re ^ 2 ≤ 1 ^ 2 :=
    (le_add_of_nonneg_right (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans bound
  have imaginaryBound : ((parent.edge.point parameter)⁻¹).im ^ 2 ≤ 1 ^ 2 :=
    (le_add_of_nonneg_left (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans bound
  have real := Square.signed_bounds_of_sq_le_sq (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1) realBound
  have imaginary := Square.signed_bounds_of_sq_le_sq (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
    imaginaryBound
  exact ⟨real.1, real.2, imaginary.1, imaginary.2⟩

/-- Every original cut's common-radius square lies in the retained ambient square. -/
theorem box_refines (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count) {parameter
  : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (data.box parameter).Refines data.ambient := by
  have center := data.center_bounds inside
  rw [data.ambient_eq]
  change -2 ≤ ((parent.edge.point parameter)⁻¹).re - data.radius ∧
    ((parent.edge.point parameter)⁻¹).re + data.radius ≤ 2 ∧
    -2 ≤ ((parent.edge.point parameter)⁻¹).im - data.radius ∧
    ((parent.edge.point parameter)⁻¹).im + data.radius ≤ 2
  exact ⟨(show (-2 : InverseRootPolynomial.Coordinate) = -1 - 1 by decide).trans_le
      (Fraction.Order.Arithmetic.sub_le_sub_direct center.1 data.radius_le_one),
    (add_le_add center.2.1 data.radius_le_one).trans_eq (by decide : (1 : InverseRootPolynomial.Coordinate) + 1 = 2),
    (show (-2 : InverseRootPolynomial.Coordinate) = -1 - 1 by decide).trans_le
      (Fraction.Order.Arithmetic.sub_le_sub_direct center.2.2.1 data.radius_le_one),
    (add_le_add center.2.2.2 data.radius_le_one).trans_eq (by decide : (1 : InverseRootPolynomial.Coordinate) + 1 = 2)⟩

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data in
/-- Throughout the original cut box, the retained shared-source seed has squared residual at most one over 16. -/
theorem model_residual (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count)
  {parameter : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    {point : InverseRootPolynomial.Gaussian} (pointInside : (data.box parameter).Contains point) :
    Data.Gaussian.Norm.Basic.normSq (1 - (HyperellipticReciprocal.polynomial curve).eval point * data.seed
      parameter ^ 2) ≤ 1 / 16 := by
  have centerInside : (data.box parameter).Contains (parent.edge.point parameter)⁻¹ :=
    PreparedObservationNeighborhoods.centeredBox_center _ _
  have variation := Dense.Gaussian.Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound
    (HyperellipticReciprocal.polynomial curve)
    ((data.box_refines inside).contains centerInside) ((data.box_refines inside).contains pointInside)
  rw [← data.slope_eq] at variation
  have distance := Rational.Box.normSq_sub_le_diagonalSq centerInside pointInside
  rw [box, BoxTransport.centeredBox_diagonalSq] at distance
  have scaled : Data.Gaussian.Norm.Basic.normSq (((HyperellipticReciprocal.polynomial curve).eval
    (parent.edge.point parameter)⁻¹ -
      (HyperellipticReciprocal.polynomial curve).eval point) * data.seed parameter ^ 2) ≤ 1 / 64 := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow]
    have budget := SquaredVariationRadius.squaredVariation_error_lt (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 1 / 64)
      (Fraction.Order.Arithmetic.mul_nonneg_direct data.slope_positive.le (Fraction.Order.Arithmetic.sq_nonneg_direct
        data.seedUpper))
      data.radius_positive.le data.radius_eq.le
    calc
      _ ≤ (data.slope * (8 * data.radius ^ 2)) * data.seedUpper ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_direct
          (variation.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance data.slope_positive.le))
          (Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _) (data.seed_norm_le
            inside) 2)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
          (Fraction.Order.Arithmetic.mul_nonneg_direct data.slope_positive.le
            (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
      _ = (data.slope * data.seedUpper ^ 2) * (8 * data.radius ^ 2) := by ring1
      _ ≤ _ := budget.le
  have identity : 1 - (HyperellipticReciprocal.polynomial curve).eval point * data.seed parameter ^ 2 =
      (1 - (HyperellipticReciprocal.polynomial curve).eval (parent.edge.point parameter)⁻¹ * data.seed parameter ^ 2) +
        ((HyperellipticReciprocal.polynomial curve).eval (parent.edge.point parameter)⁻¹ -
          (HyperellipticReciprocal.polynomial curve).eval point) * data.seed parameter ^ 2 := by ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add (data.seed_residual inside) scaled) (by
      decide)).trans_eq
      (by decide +kernel : (2 : InverseRootPolynomial.Coordinate) * (1 / 64 + 1 / 64) = 1 / 16))

/-- The same positive radius works at every source cut. Creating this model reads the cached source polynomial and
performs finite arithmetic only. -/
@[expose] def modelAt (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count)
  (parameter : InverseRootPolynomial.Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) (data.box parameter) :=
  Model.ofSeed _ _ (data.seed parameter) (fun point pointInside => by
    have scalar := data.model_residual inside pointInside
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar)

/-- The retained reciprocal model seed satisfies the exact coordinate transport identity with the original source
polynomial. -/
theorem modelAt_transport (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count)
  (parameter : InverseRootPolynomial.Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    ReciprocalRootNames.factor genus (parent.edge.point parameter) * (data.modelAt parameter inside).value.eval
      (parent.edge.point parameter)⁻¹ =
      data.source.value.eval (parent.edge.point parameter) := by
  change ReciprocalRootNames.factor genus (parent.edge.point parameter) *
    (DensePolynomial.constant (data.seed parameter)).eval (parent.edge.point parameter)⁻¹ = _
  rw [DensePolynomial.eval_constant]
  exact data.seed_transport inside

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data in
/-- An inverse-root Newton step evaluates to the original value times one plus half its retained residual.

The exact finite coefficient evaluations of the retained product, sum and scalar multiple identify the displayed factor.
The polynomial and its residual remain the original model caches. -/
private theorem step_eval {polynomial : InverseRootPolynomial.Polynomial} {box : InverseRootPolynomial.Box}
    (model : InverseRootPolynomial.Model polynomial box) (point : InverseRootPolynomial.Gaussian) :
    model.step.value.eval point = model.value.eval point *
      (1 + InverseRootPolynomial.half * model.residual.eval point) := by
  rewrite [Model.step, DensePolynomial.eval_mul,
    DensePolynomial.eval_add, DensePolynomial.eval_constant,
    DensePolynomial.eval_scale]
  rfl

/-- One synchronized Newton step preserves the exact original source-to-reciprocal coordinate transport identity. -/
private theorem step_transport {leftBox rightBox : InverseRootPolynomial.Box}
    (left : InverseRootPolynomial.Model curve.polynomial leftBox)
    (right : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) rightBox)
    (point : InverseRootPolynomial.Gaussian) (nonzero : point ≠ 0)
    (agreement : ReciprocalRootNames.factor genus point * right.value.eval point⁻¹ = left.value.eval point) :
    ReciprocalRootNames.factor genus point * right.step.value.eval point⁻¹ = left.step.value.eval point := by
  have residualEq : right.residual.eval point⁻¹ = left.residual.eval point := by
    rw [right.residual_eq, left.residual_eq, ← ReciprocalRootNames.factor_identity curve point nonzero,
      ← agreement]
    ring1
  rw [step_eval,
    step_eval, residualEq, ←
    Data.Gaussian.Basic.mul_assoc, agreement]

/-- Synchronized Newton refinements preserve the exact source sheet at the cut. There is no fresh root isolation or sign
decision at a later index. -/
theorem modelAt_refine_transport (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch
  count) (parameter : InverseRootPolynomial.Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) (index : Nat) :
    ReciprocalRootNames.factor genus (parent.edge.point parameter) *
        ((data.modelAt parameter inside).refine index).value.eval (parent.edge.point parameter)⁻¹ =
      (data.source.refine index).value.eval (parent.edge.point parameter) := by
  induction index with
  | zero => exact data.modelAt_transport parameter inside
  | succ index ih =>
      exact step_transport _ _ _
        (PreparedExteriorReciprocal.parent_point_nonzero data.boundary inside) ih

/-- Every later refinement of the retained source model satisfies the original cached inverse ceiling. -/
theorem source_refine_norm_le (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count)
  (index : Nat)
    {parameter : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq ((data.source.refine index).value.eval (parent.edge.point parameter)) ≤
      data.inverseUpper := by
  rw [data.inverseUpper_eq]
  have scalar := (SeededPrimitiveBounds.derivativeBounds (patch.neighborhood count).base).value_le (data.source.refine
    index) (data.source_inside inside)
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data in
/-- Refining by the sum of two finite indices equals the corresponding successive refinements. -/
private theorem refine_add {polynomial : InverseRootPolynomial.Polynomial} {box : InverseRootPolynomial.Box}
    (model : InverseRootPolynomial.Model polynomial box) (first last : Nat) :
    model.refine (first + last) = (model.refine first).refine last := by
  induction last with
  | zero => rfl
  | succ last ih => rw [Nat.add_succ, Model.refine, Model.refine, ih]

/-- The shared source is an actual later model of the retained operational primitive patch, not an independently chosen
square-root approximation. -/
theorem source_refine_eq (data : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count) (index
  : Nat) :
    data.source.refine index = (patch.neighborhood count).base.refine (2 + index) := by
  rw [data.source_eq]
  exact (refine_add (patch.neighborhood
    count).base.model 2 index).symm

end Data
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
