module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
public import Purelib.Polynomial.Dense.Gaussian.Primitive.DerivativeBound
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Power

public import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Dense.Basic
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Cached local primitives for continued inverse-root models

Multiply one cached inverse-root polynomial by a displayed numerator, then
integrate its finite coefficients exactly.  The increment estimate charges
both the primitive's Taylor remainder and the actual operational root error.
This is a local increment theorem, not yet a prepared path-integral bridge or
a global surface-energy error rate.
-/

namespace Purelib.Riemann.Normalization.InverseRootPrimitive

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.SeededPrimitiveBounds (clearance derivativeBounds)
open Purelib.Riemann.Normalization.InverseModelDerivativeBounds (DerivativeBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate (DensePrimitive)

open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- A retained polynomial primitive for a numerator times an indexed original odd inverse-root power.

The original continued neighborhood, numerator, refinement index and pair
count determine the coefficient equation. The zero-pair default retains the
literal original numerator-times-inverse expression. Every primitive stays
certified on that same actual continued box.
-/
structure PrimitiveModel {polynomial : Polynomial} {count : Nat}
    (patch : ContinuedNeighborhood polynomial count) (index : Nat) (numerator : Polynomial)
    (pairs : optParam Nat 0) where
  /-- The retained product coefficient polynomial for this numerator and indexed inverse-root model. -/ coefficient :
    Polynomial
  /-- The coefficient reads the numerator and original indexed inverse power at every point.

  The default branch is the exact original zero-pair equation; higher
  branches keep their full odd denominator exponent.
  -/
  coefficient_eq : ∀ point, coefficient.eval point = match pairs with
    | 0 => numerator.eval point * (patch.base.refine index).value.eval point
    | remaining + 1 => numerator.eval point * (patch.base.refine index).value.eval point ^ (2 * (remaining + 1) + 1)
  /-- The original dense primitive certificate for the retained coefficient on the continued neighborhood's exact box.
  -/
  primitive : Primitive.Certificate.DensePrimitive coefficient patch.box

constructive_injectivity PrimitiveModel

namespace PrimitiveModel

variable {polynomial : Polynomial} {count : Nat} {patch : ContinuedNeighborhood polynomial count}
  {index : Nat} {numerator : Polynomial}

/-- Retain an actual compiled odd-power coefficient with its original dense polynomial primitive.

The exact supplied coefficient and pointwise compilation equation belong
to the same original neighborhood and model index. The existing polynomial
primitive constructor computes one antiderivative on that actual box; no
inverse model, odd power or source channel is rebuilt here.
-/
def ofCoefficient (patch : ContinuedNeighborhood polynomial count) (index : Nat) (numerator : Polynomial)
    (pairs : Nat) (coefficient : Polynomial)
    (compiled : ∀ point, coefficient.eval point = match pairs with
      | 0 => numerator.eval point * (patch.base.refine index).value.eval point
      | remaining + 1 => numerator.eval point *
          (patch.base.refine index).value.eval point ^ (2 * (remaining + 1) + 1)) :
    PrimitiveModel patch index numerator pairs :=
  ⟨coefficient, compiled,
    DensePrimitive.ofPolynomial coefficient patch.box⟩

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Readings in
/-- Build the primitive from retained derivative bounds and a model with the exact indexed refinement value.

The product coefficient is cached once, and the supplied uniform derivative bound certifies its primitive on the
original continued box through the retained base-box refinement. -/
def ofBounds (patch : ContinuedNeighborhood polynomial count) (index : Nat) (numerator : Polynomial)
    {rootBounds : DerivativeBounds (SeededPrimitiveBounds.clearance patch.base) patch.base.model}
    (bounds : PrimitiveDerivativeBounds rootBounds numerator)
    (model : Model polynomial patch.base.box) (same : model.value = (patch.base.refine index).value) :
    PrimitiveModel patch index numerator :=
  let coefficient := numerator * model.value
  { coefficient := coefficient
    coefficient_eq := fun point => by rw [Dense.Basic.DensePolynomial.eval_mul, same]
    primitive := Primitive.Certificate.DensePrimitive.ofDerivativeBound coefficient patch.box bounds.bound
      bounds.bound_nonnegative
      (fun point inside => by
        rw [Norm.Basic.normSq_eq_canonical]
        exact bounds.coefficient_derivative_le index coefficient
          (fun point => by rw [Dense.Basic.DensePolynomial.eval_mul, same]; rfl) (patch.box_refines.contains inside)) }

open Purelib.Riemann.Readings in
/-- Build the primitive of a supplied exact indexed refinement model using cached derivative bounds from the original
seeded neighborhood. -/
def ofModel (patch : ContinuedNeighborhood polynomial count) (index : Nat) (numerator : Polynomial)
    (model : Model polynomial patch.base.box) (same : model.value = (patch.base.refine index).value) :
    PrimitiveModel patch index numerator :=
  ofBounds patch index numerator (PrimitiveDerivativeBounds.build (SeededPrimitiveBounds.derivativeBounds patch.base)
    numerator) model same

/-- Build a primitive using the original neighborhood's exact inverse-root refinement at the supplied index. -/
def ofIndex (patch : ContinuedNeighborhood polynomial count) (index : Nat) (numerator : Polynomial) :
    PrimitiveModel patch index numerator := ofModel patch index numerator (patch.base.refine index) rfl

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Bound a retained primitive increment against numerator divided by the supplied root times the original endpoint
displacement.

The two endpoints belong to the retained box. The estimate combines the original primitive remainder with the supplied
squared inverse-root error at the start, preserving the numerator and root reading. -/
theorem increment_bound_of_inverse_error (model : PrimitiveModel patch index numerator)
    {start finish root : Gaussian} (startInside : patch.box.Contains start) (finishInside : patch.box.Contains finish)
    {error : Coordinate}
    (inverseError : normSq ((patch.base.refine index).value.eval start - inv root) <= error) :
    normSq (model.primitive.value.eval finish - model.primitive.value.eval start -
        (numerator.eval start / root) * (finish - start)) <=
      2 * (model.primitive.remainderBound * normSq (finish - start) ^ 2 +
        normSq (numerator.eval start) * error * normSq (finish - start)) := by
  have taylor := model.primitive.increment_bound startInside finishInside
  rw [model.coefficient_eq] at taylor
  simp only [Norm.Basic.normSq_eq_canonical] at taylor
  have identity : model.primitive.value.eval finish - model.primitive.value.eval start -
      (numerator.eval start / root) * (finish - start) =
        (model.primitive.value.eval finish - model.primitive.value.eval start -
          (numerator.eval start * (patch.base.refine index).value.eval start) * (finish - start)) +
          numerator.eval start * ((patch.base.refine index).value.eval start - inv root) * (finish - start) := by
    have inverse_eq : Data.Gaussian.Field.inv root = Basic.Canonical.inv root := by
      with_unfolding_all exact (Field.inv_eq root).symm
    rw [Field.ExplicitField.div_eq_mul_inv, Field.inv_eq, inverse_eq]
    ring1
  have rootTerm : normSq (numerator.eval start *
      ((patch.base.refine index).value.eval start - inv root) * (finish - start)) <=
        normSq (numerator.eval start) * error * normSq (finish - start) := by
    rw [Basic.Canonical.normSq_mul, Basic.Canonical.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inverseError (Basic.Canonical.normSq_nonneg _))
        (Basic.Canonical.normSq_nonneg _)
  rw [identity]
  have triangle := Norm.Bounds.normSq_add_le_two
    (model.primitive.value.eval finish - model.primitive.value.eval start -
      (numerator.eval start * (patch.base.refine index).value.eval start) * (finish - start))
    (numerator.eval start * ((patch.base.refine index).value.eval start - inv root) * (finish - start))
  simp only [Norm.Basic.normSq_eq_canonical] at triangle
  exact triangle.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add taylor rootTerm) (by decide))

open Purelib.Approximation.Rational in
/-- Bound the primitive increment using a root possible at the retained point certificate's scheduled reading state.

The original reading index supplies the geometric inverse-error bound, while the exact primitive remainder and numerator
reading control the endpoint increment. -/
theorem operational_increment_bound (model : PrimitiveModel patch index numerator)
    {start finish : Gaussian} (startInside : patch.box.Contains start) (finishInside : patch.box.Contains finish)
    (sample : ContinuedNeighborhood.Point patch start) {root : Gaussian}
    (possible : sample.certificate.value.name.process.Possible (sample.readingState index) root) :
    normSq (model.primitive.value.eval finish - model.primitive.value.eval start -
        (numerator.eval start / root) * (finish - start)) <=
      2 * (model.primitive.remainderBound * normSq (finish - start) ^ 2 +
        normSq (numerator.eval start) *
          Geometric.Basic.quarterRadius patch.inverseErrorScale index * normSq (finish - start)) :=
  model.increment_bound_of_inverse_error startInside finishInside
    (sample.reading_inverse_error startInside index possible)

end PrimitiveModel

end Purelib.Riemann.Normalization.InverseRootPrimitive

end

public section

namespace Purelib.Riemann.Normalization.InverseRootPrimitive.PrimitiveModel

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model Polynomial)
open Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial.Dense.Power (OddPowers)

variable {polynomial : Polynomial} {count : Nat}

/-- Construct an indexed odd-power primitive from the actual retained inverse model and its original power cache.

The zero-pair branch is the complete original derivative-bound ofModel
construction. Higher pairs retain their actual cached coefficient and use
the original ofCoefficient primitive constructor on the same continued box.
-/
@[expose] def ofPowers (patch : ContinuedNeighborhood polynomial count) (index : Nat) (numerator : Polynomial)
    (model : Model polynomial patch.base.box) (same : model.value = (patch.base.refine index).value)
    (powers : OddPowers model.value) (pairs : optParam Nat 0) :
    PrimitiveModel patch index numerator pairs :=
  match pairs with
  | 0 => ofModel patch index numerator model same
  | remaining + 1 => ofCoefficient patch index numerator (remaining + 1)
      (numerator * powers.odd (remaining + 1)) (fun point => by
        rewrite [DensePolynomial.eval_mul, powers.odd_eval]
        have actual := congrArg (fun value : Polynomial => value.eval point) same
        rewrite [actual]
        rfl)

/-- The zero-pair power-aware constructor is the complete original derivative-bound primitive factory. -/
theorem ofPowers_zero (patch : ContinuedNeighborhood polynomial count) (index : Nat) (numerator : Polynomial)
    (model : Model polynomial patch.base.box) (same : model.value = (patch.base.refine index).value)
    (powers : OddPowers model.value) :
    ofPowers patch index numerator model same powers = ofModel patch index numerator model same := (rfl)

end Purelib.Riemann.Normalization.InverseRootPrimitive.PrimitiveModel

end
