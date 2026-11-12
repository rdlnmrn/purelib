module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Channels
public import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Curves.Legendre.Periods.Jets.Specification.Ordinary
import Purelib.Approximation.Gaussian.Name.Coherent.State.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Cast
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Curves.Hyperelliptic.Differentials.Value
import Purelib.Curves.Hyperelliptic.Sheets.Basic
import Purelib.Riemann.Integration.PreparedPrimitiveEquivalence
import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Value-zero source integrals compared to retained primitive polynomials

The source observation keeps its original denotation and reading state.
The same retained Point supplies the ordinary based coefficient at the
primitive's own selected index. Finite candidate bounds compare the actual
source polynomial with that original primitive derivative; the polynomial
primitive theorem then controls the original source integral sample.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.Query

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.State (CoefficientState)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.Value (differentialValue)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Riemann.Integration.PreparedPrimitiveEquivalence
  (basedRoot basedApart coefficient coefficient_possible_bound)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator differentialNumerator_eval)

variable {parameter : Canonical} {frame : Paths.Frame parameter}
    {start finish : LiftedPoint 2} {lifted : LiftedCell start finish}
    {cell : Cell (parameter := parameter) lifted}

/-- The two actual coefficient states compare the source polynomial with the same retained inverse-root polynomial.

The whole original query equation supplies the actual cached Point/root
readback. The primitive error uses that same Point at its retained index;
no source state is cast to another process and no point is acquired here.
-/
theorem valueZero_coefficient_difference_le (query : Query cell) (frame : Paths.Frame parameter)
    (basis : Differential 1) (zero : basis.exponent = 0) {index : Nat}
    (model : PrimitiveModel cell.patch index (differentialNumerator basis))
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1)
    (observed : CellModels.Observations frame lifted cell.models query.requests input)
    (factory_eq : observed = query.observe frame input lower upper) :
    Norm.Basic.normSq (Evaluation.eval cell.models.valueZero.model.polynomial ⟨input, 0⟩ -
      model.coefficient.eval (cell.models.coordinate.point input)) ≤
        8 * (cell.models.valueZero.model.localAllowance + quarterRadius cell.patch.inverseErrorScale index) := by
  let sample := observed.retained.sample
  let first := observed.valueZero.algebraic.interpretation.channel
  let last := coefficient (curve := Fibre.frameCurve frame) sample index basis
  have rootEq : observed.valueZero.algebraic.sheetValue.value.name = sample.certificate.value.name :=
    query.channel_root_name frame input lower upper observed factory_eq 0
  have rootEquivalent : NamedEquivalent observed.valueZero.algebraic.sheetValue.value.name
      (basedRoot (curve := Fibre.frameCurve frame) sample index).name := by
    rewrite [rootEq]
    exact sample.certificate.value.basedEquivalent (sample.readingState index)
  have normalized := Specification.valueZero_denotation_reciprocal parameter observed.valueZero.algebraic.point
    observed.valueZero.algebraic.sheetValue.value observed.valueZero.algebraic.sheetValue.squareIdentity
    observed.valueZero.algebraic.sheetValue.apart observed.valueZero.algebraic.interpretation
  have quotient := Division.Equivalence.coherentDiv_respects (Coherence.exact 1) (Coherence.exact 1)
    observed.valueZero.algebraic.sheetValue.value (basedRoot (curve := Fibre.frameCurve frame) sample index)
    observed.valueZero.algebraic.sheetValue.apart
    (basedApart (curve := Fibre.frameCurve frame) sample index) (NamedEquivalent.refl _) rootEquivalent
  have lastEq : last = CoherentNamed.div (Coherence.exact 1)
      (basedRoot (curve := Fibre.frameCurve frame) sample index)
      (basedApart (curve := Fibre.frameCurve frame) sample index) := by
    dsimp only [last, coefficient, differentialValue]
    rewrite [zero]
    rfl
  have equivalent : NamedEquivalent first.name last.name := by
    rewrite [lastEq]
    exact normalized.trans quotient
  have inside := cell.models.coordinate.point_inside cell.startInside cell.finishInside lower upper
  have lastBound : ∀ candidate, last.name.process.Possible last.name.state candidate →
      Norm.Basic.normSq (candidate - model.coefficient.eval (cell.models.coordinate.point input)) ≤
        quarterRadius cell.patch.inverseErrorScale index := by
    intro candidate possible
    have bounded := coefficient_possible_bound (curve := Fibre.frameCurve frame) sample inside index basis _ possible
    rewrite [differentialNumerator_eval, zero, pow_zero, Data.Gaussian.Basic.one_mul] at bounded
    rewrite [Data.Gaussian.Basic.Canonical.normSq_one, Data.Rat.Fraction.one_mul] at bounded
    rewrite [model.coefficient_eq, differentialNumerator_eval, zero, pow_zero, Data.Gaussian.Basic.one_mul,
      Norm.Bounds.normSq_sub_symm, Norm.Basic.normSq_eq_canonical]
    exact bounded
  have positive : 0 < cell.models.valueZero.model.localAllowance +
      quarterRadius cell.patch.inverseErrorScale index := by
    rewrite [cell.models.valueZero.allowance_eq]
    exact Arithmetic.add_pos_of_pos_of_nonneg_direct query.positive
      (quarterRadius_nonneg cell.patch.inverseErrorScale_positive.le index)
  exact CoefficientState.reference_difference_le
    ⟨first, observed.valueZero.algebraic.readingState⟩ ⟨last, last.name.state⟩
    (Evaluation.eval cell.models.valueZero.model.polynomial ⟨input, 0⟩)
    (model.coefficient.eval (cell.models.coordinate.point input))
    cell.models.valueZero.model.localAllowance (quarterRadius cell.patch.inverseErrorScale index)
    (fun _ possible => observed.valueZero.candidate_error_le possible) lastBound equivalent positive

/-- Compile the same retained primitive against the original value-zero source cell using its derived residual ceiling.

Only the finite derivative and residual coefficient tables are constructed.
The bound is derived from the actual source observation and primitive
index; no primitive-integral estimate is supplied by the caller.
-/
def valueZero_primitiveComparison (query : Query cell) (frame : Paths.Frame parameter)
    (basis : Differential 1) (zero : basis.exponent = 0) {index : Nat}
    (model : PrimitiveModel cell.patch index (differentialNumerator basis)) :
    Primitive.Comparison cell.models.valueZero.model :=
  Primitive.Comparison.ofSpatialBound cell.models.valueZero.model model.primitive.value
    (Norm.Basic.normSq cell.models.valueZero.model.displacement *
      (8 * (cell.models.valueZero.model.localAllowance + quarterRadius cell.patch.inverseErrorScale index))) (by
      intro input inside
      let observed := query.observe frame input inside.1 inside.2
      have coefficientBound := query.valueZero_coefficient_difference_le frame basis zero model
        input inside.1 inside.2 observed rfl
      have pointEq : Geometry.Rational.Affine.line cell.models.valueZero.model.start
          cell.models.valueZero.model.displacement input = cell.models.coordinate.point input := by
        change cell.models.valueZero.model.start + (⟨input, 0⟩ : Canonical) *
          (cell.models.valueZero.model.finish - cell.models.valueZero.model.start) = _
        rewrite [cell.models.valueZero.start_eq, cell.models.valueZero.finish_eq, cell.models.coordinate.point_eq]
        rfl
      have reverse := Norm.Bounds.normSq_sub_symm
        (model.coefficient.eval (cell.models.coordinate.point input))
        (Evaluation.eval cell.models.valueZero.model.polynomial ⟨input, 0⟩)
      rewrite [model.primitive.derivative_eq, pointEq, Norm.Basic.normSq_mul,
        Cast.Path.ofCoordinate, reverse]
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientBound (Norm.Basic.normSq_nonneg _))

/-- The comparison retains the exact original primitive compiled in the source cell's actual local coordinate. -/
private theorem packaged_valueZero_primitiveComparison_value (query : Query cell) (frame : Paths.Frame parameter)
    (basis : Differential 1) (zero : basis.exponent = 0) {index : Nat}
    (model : PrimitiveModel cell.patch index (differentialNumerator basis)) :
    (query.valueZero_primitiveComparison frame basis zero model).value =
      Primitive.spatialPrimitive cell.models.valueZero.model model.primitive.value := by
  unfold valueZero_primitiveComparison
  rfl

/-- The comparison retains the exact original primitive compiled in the source cell's actual local coordinate. -/
theorem valueZero_primitiveComparison_value (query : Query cell) (frame : Paths.Frame parameter)
    (basis : Differential 1) (zero : basis.exponent = 0) {index : Nat}
    (model : PrimitiveModel cell.patch index (differentialNumerator basis)) :
    (query.valueZero_primitiveComparison frame basis zero model).value =
      Primitive.spatialPrimitive cell.models.valueZero.model model.primitive.value :=
  packaged_valueZero_primitiveComparison_value query frame basis zero model

/-- The retained residual ceiling consumes the same original source allowance, displacement and primitive index. -/
private theorem packaged_valueZero_primitiveComparison_bound (query : Query cell) (frame : Paths.Frame parameter)
    (basis : Differential 1) (zero : basis.exponent = 0) {index : Nat}
    (model : PrimitiveModel cell.patch index (differentialNumerator basis)) :
    (query.valueZero_primitiveComparison frame basis zero model).bound =
      Norm.Basic.normSq cell.models.valueZero.model.displacement *
        (8 * (cell.models.valueZero.model.localAllowance + quarterRadius cell.patch.inverseErrorScale index)) := by
  unfold valueZero_primitiveComparison
  rfl

/-- The retained residual ceiling consumes the same original source allowance, displacement and primitive index. -/
theorem valueZero_primitiveComparison_bound (query : Query cell) (frame : Paths.Frame parameter)
    (basis : Differential 1) (zero : basis.exponent = 0) {index : Nat}
    (model : PrimitiveModel cell.patch index (differentialNumerator basis)) :
    (query.valueZero_primitiveComparison frame basis zero model).bound =
      Norm.Basic.normSq cell.models.valueZero.model.displacement *
        (8 * (cell.models.valueZero.model.localAllowance + quarterRadius cell.patch.inverseErrorScale index)) :=
  packaged_valueZero_primitiveComparison_bound query frame basis zero model

/-- The source value-zero integral differs from the same retained primitive increment by its derived ceiling. -/
theorem valueZero_primitive_error_le (query : Query cell) (frame : Paths.Frame parameter)
    (basis : Differential 1) (zero : basis.exponent = 0) {index : Nat}
    (model : PrimitiveModel cell.patch index (differentialNumerator basis)) :
    Norm.Basic.normSq (model.primitive.value.eval finish.coordinate - model.primitive.value.eval start.coordinate -
      cell.models.valueZero.model.integralSample) ≤
        16 * (cell.models.valueZero.model.localAllowance + quarterRadius cell.patch.inverseErrorScale index) *
          Norm.Basic.normSq cell.models.valueZero.model.displacement := by
  have bound := (query.valueZero_primitiveComparison frame basis zero model).integral_error_le
  rewrite [query.valueZero_primitiveComparison_bound frame basis zero model,
    query.valueZero_primitiveComparison_value frame basis zero model,
    Primitive.spatialPrimitive_start, Primitive.spatialPrimitive_finish,
    cell.models.valueZero.start_eq, cell.models.valueZero.finish_eq] at bound
  exact bound.trans_eq (by
    ring1)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.Query

end
