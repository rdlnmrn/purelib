module
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
public import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite polynomial evaluation at one retained sample index

Horner arithmetic supplies geometric bounds and an operational certificate.
The executable sample reads its input once and evaluates the cached dense
polynomial directly, with a proof tying it to those same Horner bounds.
-/

namespace Purelib.Polynomial.Approximation.Evaluation

open _root_.Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)

/-- Evaluate a finite coefficient list by Horner operations on geometric Gaussian approximations.

The retained input is reused at each multiplication; the supplied initial approximation carries the accumulated error
and magnitude bounds. -/
public def loop (input : Geometric.GeometricApproximation) :
  Geometric.GeometricApproximation → List Gaussian.Basic.Canonical → Geometric.GeometricApproximation
  | initial, [] => initial
  | initial, coefficient :: remaining => loop input ((initial.mul input).add
    (.exact coefficient)) remaining

/-- At a fixed sample index, the geometric Horner loop is exactly the scalar fold over the retained input sample. -/
public theorem loop_sample (input :
  Geometric.GeometricApproximation) (index : Nat) :
    ∀ initial coefficients, (loop input initial coefficients).sample index =
      coefficients.foldl (fun value coefficient => value * input.sample index + coefficient) (initial.sample index)
  | _, [] => rfl
  | initial, coefficient :: remaining => loop_sample input index
    ((initial.mul input).add (.exact coefficient)) remaining

/-- Evaluate the dense polynomial at each retained input sample, with cached geometric Horner bounds.

The error scale and center bound are computed independently of future sample indices; each sample reads the input once
and uses the exact dense evaluation. -/
def evaluate (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (input :
  Geometric.GeometricApproximation) : GeometricApproximation :=
  let computed := loop input (.exact 0) polynomial.coeffs
  have samples (index : Nat) : computed.sample index = polynomial.eval (input.sample index) :=
    loop_sample input index _ _
  { sample := fun index => polynomial.eval (input.sample index)
    errorScale := computed.errorScale
    errorScale_nonneg := computed.errorScale_nonneg
    later_close := fun {first last} later => by rw [← samples last, ← samples first]; exact computed.later_close later
    centerBound := computed.centerBound
    centerBound_nonneg := computed.centerBound_nonneg
    sample_bounded := fun index => by rw [← samples index]; exact computed.sample_bounded index }

/-- A polynomial approximation sample is exactly the dense polynomial evaluated at the same input sample index. -/
theorem evaluate_sample (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (input :
  Geometric.GeometricApproximation) (index : Nat) :
    (evaluate polynomial input).sample index = polynomial.eval (input.sample index) := rfl
end Purelib.Polynomial.Approximation.Evaluation

end
