module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
public import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original-cell primitive comparisons from the shared Legendre source

The actual row-cell coefficients and cached spatial primitive coefficients
determine each local derivative residual. Original endpoint membership
keeps the affine segment inside its continued neighborhood. The same selected
source allowance and exact displacement norm then pay all three comparisons.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Geometry.Rational
open Purelib.Approximation.Rational

variable {parameter : Canonical} {count : Nat}
  {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {cache : Cache patch}
  {floor : Nat} {target : Rational} {request : Request cache floor target}
  {start finish : Canonical} {allowance : Rational}

set_option genInjectivity false in
/-- The original three relation-cell primitive caches with source-derived local bounds.

The input cell models remain indexed. The original selected source radius
and exact displacement norm determine one shared bound. Each comparison
contains the actual finite primitive, derivative and displaced integrand
residual; no integral equality or endpoint estimate is an input. -/
structure PrimitiveModels (models : CellModels request start finish allowance) where
  /-- The cached quadrance of the same original segment displacement. -/
  displacementNorm : Rational
  /-- The cached norm belongs to the original displayed endpoints. -/
  displacementNorm_eq : displacementNorm = Norm.Basic.normSq (finish - start)
  /-- The cached original selected source radius. -/
  radius : Rational
  /-- The radius is the allowance of the retained actual source selection. -/
  radius_eq : radius = Geometric.Basic.quarterRadius cache.scale request.selection.stage
  /-- The common original-cell derivative residual ceiling. -/
  bound : Rational
  /-- The common ceiling consumes the same retained displacement norm and selected source radius. -/
  bound_eq : bound = displacementNorm * radius
  /-- The original first relation-cell primitive and displaced residual caches. -/
  zero : Primitive.Comparison models.zero
  /-- The first primitive compiles the original selected source primitive at the exact original row cell. -/
  zero_value_eq : zero.value = Primitive.spatialPrimitive models.zero request.models.primitiveZero
  /-- The first comparison retains the shared original local ceiling. -/
  zero_bound_eq : zero.bound = bound
  /-- The original second relation-cell primitive and displaced residual caches. -/
  one : Primitive.Comparison models.one
  /-- The second primitive compiles the original selected source primitive at the exact original row cell. -/
  one_value_eq : one.value = Primitive.spatialPrimitive models.one request.models.primitiveOne
  /-- The second comparison retains the shared original local ceiling. -/
  one_bound_eq : one.bound = bound
  /-- The original scalar relation-cell primitive and displaced residual caches. -/
  scalar : Primitive.Comparison models.scalar
  /-- The scalar primitive compiles its original selected cubic primitive on that exact original row cell. -/
  scalar_value_eq : scalar.value = Primitive.spatialPrimitive models.scalar request.models.scalarPrimitive
  /-- The scalar comparison retains the shared original local ceiling. -/
  scalar_bound_eq : scalar.bound = bound

constructive_injectivity PrimitiveModels

namespace PrimitiveModels

/-- Multiplying the reversed actual derivative discrepancy pays its exact displacement quadrance. -/
private theorem displaced_error_le (displacement row derivative : Canonical) (radius : Rational)
    (bound : Norm.Basic.normSq (row - derivative) ≤ radius) :
    Norm.Basic.normSq (displacement * (derivative - row)) ≤ Norm.Basic.normSq displacement * radius := by
  have opposite : derivative - row = -(row - derivative) := by ring1
  rw [opposite, Norm.Basic.normSq_mul, Norm.Basic.normSq_neg]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bound (Norm.Basic.normSq_nonneg _)

/-- Transport an actual source row residual through the original cell's exact geometric displacement. -/
private theorem displaced_source_bound (box : Geometry.Rational.Box) (cell : Basic.CellModel)
    (source primitive : DensePolynomial Canonical) (radius displacementNorm : Rational)
    (startEqual : cell.start = start) (finishEqual : cell.finish = finish)
    (normEqual : displacementNorm = Norm.Basic.normSq (finish - start))
    (readback : ∀ input, Ascending.Gaussian.Evaluation.eval cell.polynomial input =
      source.eval (start + input * (finish - start)))
    (sourceBound : ∀ point, box.Contains point →
      Norm.Basic.normSq (source.eval point - (Dense.Derivative.derivative primitive).eval point) ≤ radius)
    (startInside : box.Contains start) (finishInside : box.Contains finish)
    (input : Rational) (inside : Primitive.unitInterval.Contains input) :
    Norm.Basic.normSq (cell.displacement *
      ((Dense.Gaussian.GCD.derivative primitive).eval (Affine.line cell.start cell.displacement input) -
        Ascending.Gaussian.Evaluation.eval cell.polynomial (Cast.Path.ofCoordinate input))) ≤
      displacementNorm * radius := by
  have displacementEqual : cell.displacement = finish - start := by
    unfold Basic.CellModel.displacement
    rw [startEqual, finishEqual]
  have spatialInside := Box.contains_line startInside finishInside inside
  have bound := sourceBound (Affine.line start (finish - start) input) spatialInside
  have scalar := displaced_error_le (finish - start)
    (source.eval (Affine.line start (finish - start) input))
    ((Dense.Derivative.derivative primitive).eval (Affine.line start (finish - start) input)) radius bound
  rw [startEqual, displacementEqual, readback, Dense.Gaussian.GCD.derivative]
  rewrite [normEqual]
  exact scalar

/-- Derive all three original-cell primitive comparisons from the selected source and endpoint geometry. -/
def build (models : CellModels request start finish allowance)
    (startInside : patch.box.Contains start) (finishInside : patch.box.Contains finish) : PrimitiveModels models := by
  let displacementNorm := Norm.Basic.normSq (finish - start)
  let radius := Geometric.Basic.quarterRadius cache.scale request.selection.stage
  let bound := displacementNorm * radius
  have zeroStart : models.zero.start = start := by rw [models.zero_eq]; rfl
  have zeroFinish : models.zero.finish = finish := by rw [models.zero_eq]; rfl
  have oneStart : models.one.start = start := by rw [models.one_eq]; rfl
  have oneFinish : models.one.finish = finish := by rw [models.one_eq]; rfl
  have scalarStart : models.scalar.start = start := by rw [models.scalar_eq]; rfl
  have scalarFinish : models.scalar.finish = finish := by rw [models.scalar_eq]; rfl
  let zero := Primitive.Comparison.ofSpatialBound models.zero request.models.primitiveZero bound
    (displaced_source_bound patch.box models.zero request.rows.zero request.models.primitiveZero radius displacementNorm
      zeroStart zeroFinish rfl models.zero_eval (fun _ inside => request.zero_error_le inside)
      startInside finishInside)
  let one := Primitive.Comparison.ofSpatialBound models.one request.models.primitiveOne bound
    (displaced_source_bound patch.box models.one request.rows.one request.models.primitiveOne radius displacementNorm
      oneStart oneFinish rfl models.one_eval (fun _ inside => request.one_error_le inside)
      startInside finishInside)
  let scalar := Primitive.Comparison.ofSpatialBound models.scalar request.models.scalarPrimitive bound
    (displaced_source_bound patch.box models.scalar request.rows.scalar request.models.scalarPrimitive radius
      displacementNorm
      scalarStart scalarFinish rfl models.scalar_eval (fun _ inside => request.scalar_error_le inside)
      startInside finishInside)
  exact ⟨displacementNorm, rfl, radius, rfl, bound, rfl, zero, rfl, rfl, one, rfl, rfl, scalar, rfl, rfl⟩

/-- The first retained local primitive starts at the original spatial primitive reading. -/
theorem zero_start {models : CellModels request start finish allowance} (primitives : PrimitiveModels models) :
    primitives.zero.value.eval 0 = request.models.primitiveZero.eval start := by
  rw [primitives.zero_value_eq, Primitive.spatialPrimitive_start, models.zero_eq]
  rfl

/-- The first retained local primitive finishes at the original spatial primitive reading. -/
theorem zero_finish {models : CellModels request start finish allowance} (primitives : PrimitiveModels models) :
    primitives.zero.value.eval 1 = request.models.primitiveZero.eval finish := by
  rw [primitives.zero_value_eq, Primitive.spatialPrimitive_finish, models.zero_eq]
  rfl

/-- The second retained local primitive starts at the original spatial primitive reading. -/
theorem one_start {models : CellModels request start finish allowance} (primitives : PrimitiveModels models) :
    primitives.one.value.eval 0 = request.models.primitiveOne.eval start := by
  rw [primitives.one_value_eq, Primitive.spatialPrimitive_start, models.one_eq]
  rfl

/-- The second retained local primitive finishes at the original spatial primitive reading. -/
theorem one_finish {models : CellModels request start finish allowance} (primitives : PrimitiveModels models) :
    primitives.one.value.eval 1 = request.models.primitiveOne.eval finish := by
  rw [primitives.one_value_eq, Primitive.spatialPrimitive_finish, models.one_eq]
  rfl

/-- The retained cubic scalar primitive starts at its original spatial primitive reading. -/
theorem scalar_start {models : CellModels request start finish allowance} (primitives : PrimitiveModels models) :
    primitives.scalar.value.eval 0 = request.models.scalarPrimitive.eval start := by
  rw [primitives.scalar_value_eq, Primitive.spatialPrimitive_start, models.scalar_eq]
  rfl

/-- The retained cubic scalar primitive finishes at its original spatial primitive reading. -/
theorem scalar_finish {models : CellModels request start finish allowance} (primitives : PrimitiveModels models) :
    primitives.scalar.value.eval 1 = request.models.scalarPrimitive.eval finish := by
  rw [primitives.scalar_value_eq, Primitive.spatialPrimitive_finish, models.scalar_eq]
  rfl

/-- The first original row integral is controlled by the increment of its actual cached spatial primitive. -/
theorem zero_integral_error_le {models : CellModels request start finish allowance}
    (primitives : PrimitiveModels models) :
    Norm.Basic.normSq (request.models.primitiveZero.eval finish - request.models.primitiveZero.eval start -
      models.zero.integralSample) ≤ 2 * primitives.bound := by
  have estimate := primitives.zero.integral_error_le
  rw [primitives.zero_start, primitives.zero_finish, primitives.zero_bound_eq] at estimate
  exact estimate

/-- The second original row integral is controlled by the increment of its actual cached spatial primitive. -/
theorem one_integral_error_le {models : CellModels request start finish allowance}
    (primitives : PrimitiveModels models) :
    Norm.Basic.normSq (request.models.primitiveOne.eval finish - request.models.primitiveOne.eval start -
      models.one.integralSample) ≤ 2 * primitives.bound := by
  have estimate := primitives.one.integral_error_le
  rw [primitives.one_start, primitives.one_finish, primitives.one_bound_eq] at estimate
  exact estimate

/-- The original scalar row integral is controlled by the increment of its actual cached cubic primitive. -/
theorem scalar_integral_error_le {models : CellModels request start finish allowance}
    (primitives : PrimitiveModels models) :
    Norm.Basic.normSq (request.models.scalarPrimitive.eval finish - request.models.scalarPrimitive.eval start -
      models.scalar.integralSample) ≤ 2 * primitives.bound := by
  have estimate := primitives.scalar.integral_error_le
  rw [primitives.scalar_start, primitives.scalar_finish, primitives.scalar_bound_eq] at estimate
  exact estimate

/-- The actual displacement norm is nonnegative. -/
theorem displacementNorm_nonnegative {models : CellModels request start finish allowance}
    (primitives : PrimitiveModels models) : 0 ≤ primitives.displacementNorm := by
  rewrite [primitives.displacementNorm_eq]
  exact Norm.Basic.normSq_nonneg _

/-- The original finite source selection pays each local derivative residual using its actual displacement cost. -/
theorem bound_le_selected_target {models : CellModels request start finish allowance}
    (primitives : PrimitiveModels models) : primitives.bound ≤ primitives.displacementNorm * target := by
  rewrite [primitives.bound_eq, primitives.radius_eq]
  have paid := request.selection.accurate.le
  rewrite [request.selection.allowance_eq] at paid
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    paid primitives.displacementNorm_nonnegative

end PrimitiveModels

end Purelib.Curves.Legendre.Periods.Jets.Source

end
