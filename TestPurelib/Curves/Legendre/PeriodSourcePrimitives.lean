module

import Purelib.Curves.Legendre.Periods.Jets.Source
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Norm.Basic

/-! # Primitive construction from the original six retained source coefficients

The producer computes one original request and consumes its six cached
coefficients. The default regression compares the complete former factory,
including its actual polynomial primitive and retained certificates.
-/

namespace TestPurelib.Curves.Legendre.PeriodSourcePrimitives

open Purelib
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization
open ContinuedInverseRoot (ContinuedNeighborhood)
open InverseRootPolynomial (Polynomial Model)
open InverseRootPrimitive (PrimitiveModel)
open InverseModelDerivativeBounds (DerivativeBounds)
open InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)

variable {parameter : Canonical} {count : Nat}
  {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}

/-- Compute one actual common source request and construct its six original indexed primitives.

The same request owns the model, shared powers, ordered coefficient table
and selected stage. No comparison, domain-success or coefficient-equality
hypothesis is supplied by the caller.
-/
def primitives (patch : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (current : Nat) (target : Rational) (positive : 0 < target) :
    (request : Source.Request (Source.Cache.ofPatch patch) current target) ×
      ((channel : Fin 6) → PrimitiveModel patch request.selection.stage
        ((Specification.Table.forms parameter channel).numerator.scale
          (Specification.Table.forms parameter channel).scale)
        (Specification.Table.forms parameter channel).denominatorPairs) :=
  let cache := Source.Cache.ofPatch patch
  let request := cache.request current target positive
  ⟨request, fun channel => request.primitive channel⟩

/-- The complete original common request is retained as the producer's actual first component. -/
example (current : Nat) (target : Rational) (positive : 0 < target) :
    (primitives patch current target positive).1 = (Source.Cache.ofPatch patch).request current target positive := rfl

/-- Every original ordered channel consumes precisely that retained request's actual coefficient cache. -/
example (current : Nat) (target : Rational) (positive : 0 < target) (channel : Fin 6) :
    ((primitives patch current target positive).2 channel).coefficient =
      (primitives patch current target positive).1.models.coefficient channel :=
  ((primitives patch current target positive).1).primitive_coefficient channel

open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Readings

/-- The complete original zero-pair factory before introducing the defaulted pair index. -/
private def formerOfBounds (patch : ContinuedNeighborhood polynomial count) (index : Nat) (numerator : Polynomial)
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

/-- The omitted pair index preserves the complete former polynomial, primitive and certificates for every input. -/
example {polynomial : Polynomial} {size : Nat}
    (patch : ContinuedNeighborhood polynomial size) (index : Nat) (numerator : Polynomial)
    {rootBounds : DerivativeBounds (SeededPrimitiveBounds.clearance patch.base) patch.base.model}
    (bounds : PrimitiveDerivativeBounds rootBounds numerator)
    (model : Model polynomial patch.base.box) (same : model.value = (patch.base.refine index).value) :
    PrimitiveModel.ofBounds patch index numerator bounds model same =
      formerOfBounds patch index numerator bounds model same := rfl

/-- The complete original supplied-model factory retains its actual cached derivative bounds and result. -/
example {polynomial : Polynomial} {size : Nat}
    (patch : ContinuedNeighborhood polynomial size) (index : Nat) (numerator : Polynomial)
    (model : Model polynomial patch.base.box) (same : model.value = (patch.base.refine index).value) :
    PrimitiveModel.ofModel patch index numerator model same =
      formerOfBounds patch index numerator
        (PrimitiveDerivativeBounds.build (SeededPrimitiveBounds.derivativeBounds patch.base) numerator)
        model same := rfl

/-- The complete original indexed factory retains the same actual source refinement and original primitive. -/
example {polynomial : Polynomial} {size : Nat}
    (patch : ContinuedNeighborhood polynomial size) (index : Nat) (numerator : Polynomial) :
    PrimitiveModel.ofIndex patch index numerator =
      formerOfBounds patch index numerator
        (PrimitiveDerivativeBounds.build (SeededPrimitiveBounds.derivativeBounds patch.base) numerator)
        (patch.base.refine index) rfl := rfl

/-- Supplying the zero-pair index retains the exact original three-field type, with no wrapper transport. -/
example {polynomial : Polynomial} {size : Nat} (patch : ContinuedNeighborhood polynomial size)
    (index : Nat) (numerator : Polynomial) :
    PrimitiveModel patch index numerator = PrimitiveModel patch index numerator 0 := rfl

end TestPurelib.Curves.Legendre.PeriodSourcePrimitives
