module

public import Purelib.RationalFunctions.Curve.Substitution
public import Purelib.Polynomial.Dense.Rational.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained denominator-cleared substitutions

The original cleared Horner fold and both coordinate coefficient tables are
computed once. Subsequent clearance and phase calculations consume those
retained tables rather than repeating substitution.
-/

namespace Purelib.RationalFunctions.Curve.Substitution

open Purelib.Data
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian
open Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

set_option genInjectivity false in
/-- One original cleared substitution with its cached real and imaginary tables.

The equalities bind every table to the exact retained Horner state, preserving
the original polynomial and rational curve as indices. -/
public structure Retained (polynomial : CoefficientPolynomial) (curve : RationalCurve) where
  /-- The once-computed original Horner substitution state. -/ state : ClearingState
  /-- The state is the original cleared substitution. -/ state_eq : state = clearingState polynomial curve
  /-- The retained real coordinate table. -/ real : CoordinatePolynomial
  /-- The real table projects this same state. -/ real_eq : real = Components.realPart state.value
  /-- The retained imaginary coordinate table. -/ imaginary : CoordinatePolynomial
  /-- The imaginary table projects this same state. -/ imaginary_eq : imaginary = Components.imagPart state.value

constructive_injectivity Retained

namespace Retained

/-- Compute the original Horner state once and retain both coordinate projections. -/
@[expose] public def prepare (polynomial : CoefficientPolynomial) (curve : RationalCurve) :
    Retained polynomial curve :=
  let state := clearingState polynomial curve
  { state, state_eq := rfl
    real := Components.realPart state.value, real_eq := rfl
    imaginary := Components.imagPart state.value, imaginary_eq := rfl }

variable {polynomial : CoefficientPolynomial} {curve : RationalCurve}

/-- The cached real table is the original cleared real polynomial. -/
public theorem real_readback (data : Retained polynomial curve) :
    data.real = clearedReal polynomial curve := by
  rw [data.real_eq, data.state_eq]
  rfl

/-- The cached imaginary table is the original cleared imaginary polynomial. -/
public theorem imaginary_readback (data : Retained polynomial curve) :
    data.imaginary = clearedImag polynomial curve := by
  rw [data.imaginary_eq, data.state_eq]
  rfl

/-- The cached coordinate tables evaluate to the same original retained clearing-state value. -/
public theorem coordinates (data : Retained polynomial curve) (parameter : Rat.Fraction.Rational) :
    (⟨data.real.eval parameter, data.imaginary.eval parameter⟩ : Gaussian.Basic.Canonical) =
      data.state.value.eval (Gaussian.Cast.Path.ofCoordinate parameter) := by
  apply Gaussian.Basic.ext
  · change data.real.eval parameter = _
    rw [data.real_eq, Components.eval_realPart]
  · change data.imaginary.eval parameter = _
    rw [data.imaginary_eq, Components.eval_imagPart]

/-- The same retained clearing-state value is the original cleared polynomial. -/
public theorem state_value (data : Retained polynomial curve) : data.state.value = clearedEval polynomial curve := by
  rw [data.state_eq]
  rfl

/-- Both cached coordinates vanish precisely when the original curve value vanishes.

The denominator must be nonzero at the same rational parameter. -/
public theorem zero_iff (data : Retained polynomial curve) (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    data.real.eval parameter = 0 ∧ data.imaginary.eval parameter = 0 ↔
      polynomial.eval (curve.point parameter) = 0 := by
  rw [data.real_readback, data.imaginary_readback]
  exact cleared_pair_zero_iff polynomial curve parameter denominatorNonzero

end Retained
end Purelib.RationalFunctions.Curve.Substitution
