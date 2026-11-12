module

public import Purelib.Polynomial.Ascending.Gaussian.Dense.Antiderivative
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation

/-!
# Box control of retained finite antiderivatives

The original coefficient polynomial and retained antiderivative determine
the same original dense primitive certificate. Only its coefficient-computed
box remainder is added; the supplied antiderivative is not reconstructed.
-/

public section

namespace Purelib.Polynomial.Ascending.Gaussian.Antiderivative

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

/-- Regard the supplied original antiderivative as an original dense primitive on the supplied box.

The actual coefficient polynomial supplies the index; the actual retained
antiderivative supplies the value. The existing Horner Taylor fold computes
its remainder ceiling once in this certificate.
-/
@[expose] def inBox (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = antiderivative source }) (box : Box) :
    DensePrimitive (Dense.Evaluation.toDense source) box :=
  let original := derivativePrimitive (Dense.Evaluation.toDense retained.val) box
  have derivative (point : Basic.Canonical) :
      (Dense.Gaussian.GCD.derivative (Dense.Evaluation.toDense retained.val)).eval point =
        (Dense.Evaluation.toDense source).eval point := by
    rewrite [retained.property, Dense.Evaluation.toDense_eval]
    exact Dense.Antiderivative.toDense_antiderivative_derivative source point
  { value := original.value
    derivative_eq := derivative
    remainderBound := original.remainderBound
    remainderBound_nonnegative := original.remainderBound_nonnegative
    increment_bound := by
      intro start finish startInside finishInside
      have bounded := original.increment_bound startInside finishInside
      change Norm.Basic.normSq ((Dense.Evaluation.toDense retained.val).eval finish -
        (Dense.Evaluation.toDense retained.val).eval start -
        (Dense.Gaussian.GCD.derivative (Dense.Evaluation.toDense retained.val)).eval start *
          (finish - start)) ≤ _ at bounded
      rewrite [derivative] at bounded
      exact bounded }

/-- The original dense certificate retains the complete actual supplied antiderivative table. -/
theorem inBox_value (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = antiderivative source }) (box : Box) :
    (inBox source retained box).value = Dense.Evaluation.toDense retained.val := rfl

/-- The original boxed primitive and original coefficient ceiling, each tied to its complete actual construction.

Both caches retain the original coefficient polynomial, supplied
antiderivative and box as indices. The two-field dependent pair uses the
same original dense primitive and scalar subtype owners.
-/
abbrev BoxPreparation (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = antiderivative source }) (box : Box) :=
  (_primitive : { value : DensePrimitive (Dense.Evaluation.toDense source) box //
    value = inBox source retained box }) ×
    { value : Fraction.Rational //
      value = Dense.Gaussian.Bounds.Box.denseEvalNormBound (Dense.Evaluation.toDense source) box }

/-- Transport both actual boxed caches along an exact equality of their original boxes.

The supplied primitive and coefficient ceiling remain the same stored
values. Only their common box index and its defining certificates change.
-/
@[expose] def BoxPreparation.castBox {source : CoefficientPolynomial}
    {retained : { value : CoefficientPolynomial // value = antiderivative source }}
    {box target : Box} (preparation : BoxPreparation source retained box) (same : box = target) :
    BoxPreparation source retained target := same ▸ preparation

/-- Transport along the reflexive box equality preserves the complete supplied cache pair literally. -/
theorem BoxPreparation.castBox_refl {source : CoefficientPolynomial}
    {retained : { value : CoefficientPolynomial // value = antiderivative source }} {box : Box}
    (preparation : BoxPreparation source retained box) : preparation.castBox rfl = preparation := rfl

/-- Compute one original boxed primitive and one original coefficient ceiling from the retained input tables.

The supplied antiderivative is consumed directly. Its coefficient conversion
and remainder fold are retained by the primitive; the original numerator's
Horner value ceiling is computed once as the second cache.
-/
@[expose] def prepareInBox (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = antiderivative source }) (box : Box) :
    BoxPreparation source retained box :=
  let primitive := inBox source retained box
  let polynomial := Dense.Evaluation.toDense source
  let coefficientBound := Dense.Gaussian.Bounds.Box.denseEvalNormBound polynomial box
  ⟨⟨primitive, rfl⟩, ⟨coefficientBound, rfl⟩⟩

end Purelib.Polynomial.Ascending.Gaussian.Antiderivative
