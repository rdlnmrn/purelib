module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Row
public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Substitution.Composition

/-! # Primitive-row values from the same retained six-channel query

The actual query's point, reciprocal factors, selected root and model-power
reading remain unchanged. One additional row numerator is evaluated once;
its primitive denotation and polynomial value consume that same cached
factor and original inverse or cubic model table.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Row

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

variable {parameter : Canonical} {count : Nat}
variable {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {cache : Cache patch}
variable {floor : Nat} {target allowance : Rational} {request : Request cache floor target}
variable {start finish : Canonical} {models : CellModels request start finish allowance}
variable {bounds : UniformBounds patch} {uniformFloor : Nat}
variable {requests : IntegrandRequests bounds uniformFloor (allowance / 4)} {fraction : Rational}
variable (row : Row) (readings : CellModels.Readings models requests fraction)

/-- One row factor, same-root denotation and original source-polynomial value on the actual query reading. -/
@[expose] def QueryValue :=
  Σ _factor : {scalar : Canonical // scalar = (row.numerator parameter).eval (models.coordinate.point fraction)},
  Σ denotation : PrimitiveDenotation readings.sample row.pairs (row.numerator parameter),
    PrimitiveValue readings.reading row.pairs (row.numerator parameter) denotation (row.spatial request.models)

namespace QueryValue

/-- Construct the selected primitive row without rerunning the source query, selecting a root or reevaluating its model.

The original query's retained parameter inverse or square supplies the
primitive multiplier. The source table's exact compilation law and cached
odd-power reading derive its scalar value; neither the large polynomial
nor another source preparation is evaluated.
-/
def build : QueryValue row readings :=
  let factor := (row.numerator parameter).eval (models.coordinate.point fraction)
  let multiplier : {scalar : Canonical // scalar = readings.bounds.parameterInverse ^ (row.pairs.val + 1)} :=
    match row with
    | .inl _ => ⟨readings.bounds.parameterInverse, (pow_one _).symm⟩
    | .inr _ => ⟨readings.inverseSquare, readings.inverseSquare_eq⟩
  let denotation := retainPrimitiveDenotation readings.sample readings.bounds row.pairs (row.numerator parameter)
    ⟨factor, rfl⟩ multiplier
  have compiled : (row.spatial request.models).eval (models.coordinate.point fraction) =
      (row.numerator parameter).eval (models.coordinate.point fraction) *
        (primitivePolynomial request.models.powers row.pairs).eval (models.coordinate.point fraction) := by
    rewrite [row.spatial_eq request.models, DensePolynomial.eval_mul]
    rfl
  let value := retainPrimitiveValue readings.reading row.pairs (row.numerator parameter) denotation
    (row.spatial request.models) compiled ⟨factor, rfl⟩
  ⟨⟨factor, rfl⟩, denotation, value⟩

variable {row readings}
variable (queried : QueryValue row readings)

/-- Read the same once-evaluated original row numerator factor. -/
abbrev factor := queried.1.val

/-- Read the primitive denotation at the actual retained source query's original sheet generator. -/
abbrev denotation := queried.2.1

/-- Read the actual source-model primitive value, same shared root reading and finite source residual. -/
abbrev value := queried.2.2

end QueryValue

/-- The original selected relation cell starts at the same source coordinate as its six retained differential models. -/
theorem cell_start (row : Row) (models : CellModels request start finish allowance) :
    (row.cell models).start = start := by
  cases row with
  | inl coordinate =>
      refine Fin.cases ?_ (fun _ => ?_) coordinate
      · change models.zero.start = start
        rewrite [models.zero_eq]
        rfl
      · change models.one.start = start
        rewrite [models.one_eq]
        rfl
  | inr _ =>
      change models.scalar.start = start
      rewrite [models.scalar_eq]
      rfl

/-- The selected relation cell finishes at the same target coordinate as its six differential models. -/
theorem cell_finish (row : Row) (models : CellModels request start finish allowance) :
    (row.cell models).finish = finish := by
  cases row with
  | inl coordinate =>
      refine Fin.cases ?_ (fun _ => ?_) coordinate
      · change models.zero.finish = finish
        rewrite [models.zero_eq]
        rfl
      · change models.one.finish = finish
        rewrite [models.one_eq]
        rfl
  | inr _ =>
      change models.scalar.finish = finish
      rewrite [models.scalar_eq]
      rfl

/-- The selected relation cell has the same original affine physical point at every retained rational fraction. -/
theorem cell_point (row : Row) (models : CellModels request start finish allowance) (input : Rational) :
    (row.cell models).point input = models.coordinate.point input := by
  unfold Integration.Polynomial.Gaussian.Cell.Basic.CellModel.point
    Integration.Polynomial.Gaussian.Cell.Basic.CellModel.displacement
  rewrite [row.cell_start models, row.cell_finish models, models.coordinate.point_eq]
  rfl

/-- The selected primitive compiles its same retained spatial source table on the original row cell. -/
theorem primitive_value_eq (row : Row) (primitives : PrimitiveModels models) :
    (row.primitive primitives).value =
      Integration.Polynomial.Gaussian.Cell.Primitive.spatialPrimitive
        (row.cell models) (row.spatial request.models) := by
  cases row with
  | inl coordinate => exact Fin.cases primitives.zero_value_eq (fun _ => primitives.one_value_eq) coordinate
  | inr _ => exact primitives.scalar_value_eq

/-- Every actual fraction of the original cached local primitive reads the same original spatial primitive table. -/
theorem primitive_eval (row : Row) (primitives : PrimitiveModels models) (input : Rational) :
    (row.primitive primitives).value.eval (Data.Gaussian.Cast.Path.ofCoordinate input) =
      (row.spatial request.models).eval (models.coordinate.point input) := by
  rewrite [row.primitive_value_eq primitives,
    Integration.Polynomial.Gaussian.Cell.Primitive.spatialPrimitive,
    Polynomial.Dense.Gaussian.Substitution.Composition.eval_compose,
    Integration.Polynomial.Gaussian.Cell.Primitive.coordinate_eval]
  change (row.spatial request.models).eval ((row.cell models).point input) = _
  exact congrArg (fun point : Canonical => (row.spatial request.models).eval point) (row.cell_point models input)

end Purelib.Curves.Legendre.Periods.Jets.Source.Row

end
