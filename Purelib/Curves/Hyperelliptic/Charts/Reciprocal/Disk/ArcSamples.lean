module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Derivative
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Data.Rat
open Purelib.Polynomial.Dense
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Readings

/-!
# Shared cap samples on retained reciprocal boundary cells

Each cell reuses the inverse polynomial already cached by its reciprocal
primitive. The global cap sample and regular bounds are supplied from their
banks. Actual inverse endpoint values are materialized once; coefficient
identities retain the reciprocal orientation and the source sheet.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (CellPrimitive SourcePrimitive)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

set_option genInjectivity false in
/-- Cached derivative-comparison bounds for one original reciprocal boundary cell and shared regular cap.

The source and disk error scales are retained before choosing a common polynomial stage. -/
structure Data (regular : RegularBounds.Data cap) (cell : UniformReciprocalCover.Cell data edge) where
  /-- The retained derivative comparison between the original cell model and shared regular cap bounds. -/ disk :
    ComparisonBounds.Data regular cell.model
  /-- The cached original source-to-reciprocal coefficient discrepancy scale. -/ sourceScale :
    InverseRootPolynomial.Coordinate
  /-- The source scale is the original common density times the source residual bound plus one sixteenth. -/
    sourceScale_eq : sourceScale = UniformReciprocalPrimitives.Data.density data * (data.source.bound + 1 / 16)
  /-- The cached combined source-to-cap primitive comparison scale. -/ scale : InverseRootPolynomial.Coordinate
  /-- The combined scale is four times the source and disk scales times the original parent displacement squared norm.
  -/
  scale_eq : scale = 4 * (sourceScale + disk.scale) * Data.Gaussian.Norm.Basic.normSq
    parent.model.displacement

constructive_injectivity Data

namespace Data

/-- Cache the original cell's disk comparison and combined source-to-cap derivative scale. -/
@[expose] def build (regular : RegularBounds.Data cap) (cell : UniformReciprocalCover.Cell data edge) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell :=
  let disk := ComparisonBounds.Data.build regular cell.model
  let sourceScale := UniformReciprocalPrimitives.Data.density data * (data.source.bound + 1 / 16)
  ⟨disk, sourceScale, rfl, 4 * (sourceScale + disk.scale) * Data.Gaussian.Norm.Basic.normSq
    parent.model.displacement, rfl⟩

/-- The cached source coefficient discrepancy scale is nonnegative. -/
theorem sourceScale_nonnegative (comparison : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell)
  : 0 ≤ comparison.sourceScale := by
  rw [comparison.sourceScale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (UniformReciprocalPrimitives.Data.density_positive data).le
    (add_nonneg data.source.bound_nonnegative (by decide))

/-- The combined original arc derivative scale is nonnegative. -/
theorem scale_nonnegative (comparison : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell) : 0 ≤
  comparison.scale := by
  rw [comparison.scale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg comparison.sourceScale_nonnegative comparison.disk.scale_nonnegative))
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)

end Data

variable {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {index : Nat}
  {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- The original reciprocal primitive paired with a shared cap pullback and cached inverse-endpoint values.

Exact cell and inverse-model identities ensure the pullback consumes the retained polynomial cache. -/
structure Sample (comparison : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell) (capSample :
  Primitives.Sample cap differential index box) where
  /-- The original reciprocal cell primitive cache at the shared polynomial stage. -/ retained :
    UniformReciprocalPrimitives.CellPrimitive data index edge
  /-- The retained primitive belongs to exactly the specified original reciprocal cell. -/ cell_eq : retained.cell =
    cell
  /-- The cap pullback sample consuming that same retained reciprocal inverse model. -/ pullback :
    PolynomialPullback.Sample comparison.disk.preparation capSample
  /-- The pullback reciprocal model is exactly the original primitive's cached inverse. -/ inverse_eq :
    pullback.reciprocal = retained.inverse
  /-- The cached pullback value at the original inverse starting endpoint. -/ firstValue :
    InverseRootPolynomial.Gaussian
  /-- The cached first value equals the pullback polynomial evaluated at the original inverse start. -/ firstValue_eq :
    firstValue = pullback.value.eval (parent.edge.point edge.left.parameter)⁻¹
  /-- The cached pullback value at the original inverse finishing endpoint. -/ lastValue :
    InverseRootPolynomial.Gaussian
  /-- The cached last value equals the pullback polynomial evaluated at the original inverse finish. -/ lastValue_eq :
    lastValue = pullback.value.eval (parent.edge.point edge.right.parameter)⁻¹
  /-- The cached original pullback endpoint difference. -/ increment : InverseRootPolynomial.Gaussian
  /-- The increment is exactly the retained last value minus the retained first value. -/ increment_eq : increment =
    lastValue - firstValue

constructive_injectivity Sample

namespace Sample

/-- Share the actual reciprocal primitive's refined inverse, and evaluate the new cap comparison at its actual inverse
endpoints only once. -/
@[expose] def ofPrimitive (comparison : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell)
  (capSample : Primitives.Sample cap differential index box)
    (retained : UniformReciprocalPrimitives.CellPrimitive data index edge) (cell_eq : retained.cell = cell) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample :=
  let pullback := PolynomialPullback.Sample.ofModel comparison.disk.preparation capSample retained.inverse
    (by rw [retained.inverse_eq, cell_eq])
  let firstValue := pullback.value.eval (parent.edge.point edge.left.parameter)⁻¹
  let lastValue := pullback.value.eval (parent.edge.point edge.right.parameter)⁻¹
  ⟨retained, cell_eq, pullback, rfl, firstValue, rfl, lastValue, rfl, lastValue - firstValue, rfl⟩

/-- The sign in the cap derivative is the same reciprocal minus sign used by the retained cell's original primitive
comparison. -/
theorem coefficient_eq (sample : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample)
  (point : InverseRootPolynomial.Gaussian) :
    sample.pullback.coefficient.eval point = -sample.retained.coefficient.eval point := by
  rw [sample.pullback.coefficient_eq, sample.inverse_eq, sample.retained.inverse_eq, sample.retained.coefficient_eq,
    PreparedPrimitiveSamples.differentialNumerator_eval]

/-- The original pullback derivative error satisfies its geometric disk bound along every contained point of the
retained arc. -/
theorem derivative_error (sample : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample)
  (parameter : InverseRootPolynomial.Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq ((Derivative.derivative sample.pullback.value).eval (parent.edge.point
      parameter)⁻¹ -
      sample.pullback.coefficient.eval (parent.edge.point parameter)⁻¹) ≤ Geometric.Basic.quarterRadius
        comparison.disk.scale index := by
  have within : 0 ≤ parameter ∧ parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩
  have boundary := data.boundary.point within
  have lower := (collar.point_clearance boundary (show 0 ≤ (0 : InverseRootPolynomial.Coordinate) ∧ (0 :
    InverseRootPolynomial.Coordinate) ≤ 1 from ⟨le_rfl, by decide⟩)).2
  rw [collar.point_eq, ReciprocalExteriorCollar.deform_zero] at lower
  exact comparison.disk.derivative_error_le sample.pullback (cell.contains parameter between)
    (ReciprocalExteriorCollar.inverse_inDisk curve boundary) lower

/-- The original source and reciprocal coefficient discrepancy satisfies its retained geometric scale along the same
arc. -/
theorem source_error (sample : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample)
  (source : UniformReciprocalPrimitives.SourcePrimitive data index) (parameter : InverseRootPolynomial.Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (source.coefficient.eval (parent.edge.point parameter) - (parent.edge.point
      parameter)⁻¹ ^ 2 *
      sample.retained.coefficient.eval (parent.edge.point parameter)⁻¹) ≤ Geometric.Basic.quarterRadius
        comparison.sourceScale index := by
  have estimate := sample.retained.coefficient_distance_le source parameter between
  rw [Model.refine_bound, Model.refine_bound,
    sample.cell_eq, cell.model_eq] at estimate
  change Data.Gaussian.Norm.Basic.normSq _ ≤ UniformReciprocalPrimitives.Data.density data *
    (Geometric.Basic.quarterRadius data.source.bound index + Geometric.Basic.quarterRadius (1 / 16) index) at estimate
  exact estimate.trans_eq (by
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow, comparison.sourceScale_eq, -eq_self, -iff_self];
      ring1)

end Sample
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
