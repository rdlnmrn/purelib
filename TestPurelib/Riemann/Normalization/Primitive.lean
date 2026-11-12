module

import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Request
import Purelib.Polynomial.Dense.Power
import Purelib.Data.Gaussian.Norm.Basic

/-!
# Original continued-point primitive request construction

One source request selects its paid depth before materializing the retained
model and odd powers. The original point's actual requested root witness and
primitive denotation then produce the source residual comparison internally.
-/

namespace TestPurelib.Riemann.Normalization.Primitive

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

/-- An actual source request owns its selected model, shared root witness and original denotation comparison. -/
private theorem requestedPrimitive {polynomial : Coefficients} {count : Nat}
    {patch : ContinuedNeighborhood polynomial count} {point : Canonical}
    (sample : ContinuedNeighborhood.Point patch point) (inside : patch.box.Contains point)
    (pairs : Fin 3) (numerator : Coefficients) (original : PrimitiveDenotation sample pairs numerator)
    (floor : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    let bounds := sample.primitiveBounds
    let request := bounds.request pairs numerator floor target positive
    let model := patch.base.refine request.stage
    let powers := OddPowers.build model.value
    let root := selectPrimitiveRoot sample request.stage target positive
    let reading := root.readModel model rfl powers
    let source := numerator * primitivePolynomial powers pairs
    let value := retainPrimitiveValue reading pairs numerator original source
      (Polynomial.Dense.Basic.DensePolynomial.eval_mul _ _ _)
    Data.Gaussian.Norm.Basic.normSq value.residual < target := by
  dsimp only
  exact PrimitiveRequest.residual_lt _ _ inside (Nat.le_refl _)

example {polynomial : Coefficients} {count : Nat} {patch : ContinuedNeighborhood polynomial count}
    {point : Canonical} (sample : ContinuedNeighborhood.Point patch point) (inside : patch.box.Contains point)
    (pairs : Fin 3) (numerator : Coefficients) (original : PrimitiveDenotation sample pairs numerator)
    (floor : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    let request := sample.primitiveBounds.request pairs numerator floor target positive
    let model := patch.base.refine request.stage
    let powers := OddPowers.build model.value
    let root := selectPrimitiveRoot sample request.stage target positive
    let reading := root.readModel model rfl powers
    let value := retainPrimitiveValue reading pairs numerator original
      (numerator * primitivePolynomial powers pairs) (Polynomial.Dense.Basic.DensePolynomial.eval_mul _ _ _)
    Data.Gaussian.Norm.Basic.normSq value.residual < target :=
  requestedPrimitive sample inside pairs numerator original floor target positive

end TestPurelib.Riemann.Normalization.Primitive
