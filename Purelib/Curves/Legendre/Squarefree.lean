module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Evaluation

public import Purelib.Curves.Legendre.Paths
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.GCD
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Legendre

open Purelib.Polynomial

open Purelib.Polynomial.Dense

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Squarefree

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

section
@[expose] public section

/-!
# Finite squarefreeness for the Legendre cubic

The explicit Bézout identity belongs to the family itself, independently of
any particular root frame.  Keeping it in this lightweight module lets
finite period clients construct a curve without initializing a complete
worked path example.
-/

section

namespace Purelib.Curves.Legendre.Squarefree

/-- Exact Gaussian rational parameters and evaluation points. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- Executable dense Gaussian polynomials for the Legendre family. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial

/-- Explicit parameterized left Bézout coefficient. -/
def bezoutLeft (lambda : Gaussian) :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[-6 * (lambda ^ 2 - lambda + 1),
    (lambda + 1) * (4 * lambda ^ 2 - 7 * lambda + 4)]⟩

/-- Explicit parameterized right Bézout coefficient. -/
def bezoutRight (lambda : Gaussian) :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[2 * (lambda ^ 2 - lambda + 1),
    -(lambda + 1) * (2 * lambda ^ 2 - 3 * lambda + 2),
    lambda * (lambda - 1) ^ 2]⟩

/-- The automatic derivative of the displayed Legendre cubic evaluates to its explicit quadratic. -/
theorem derivative_eval (lambda point : Gaussian) :
    (Purelib.Polynomial.Dense.Gaussian.GCD.derivative (Purelib.Curves.Legendre.Paths.polynomial lambda)).eval point =
      3 * point * point - 2 * (lambda + 1) * point + lambda := by
  unfold GCD.derivative
  rw [Derivative.eval_derivative]
  unfold Paths.polynomial
    Derivative.evalDerivativeCoeffs
    Derivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The displayed polynomial and derivative Bezout combination is the exact scalar parameter square times
parameter-minus-one square. -/
theorem bezout_identity (lambda point : Gaussian) :
    (bezoutLeft lambda).eval point * (Paths.polynomial lambda).eval point +
        (bezoutRight lambda).eval point *
          (GCD.derivative
            (Paths.polynomial lambda)).eval point = lambda ^ 2 * (lambda - 1) ^ 2 := by
  rw [Paths.polynomial_eval, derivative_eval]
  unfold bezoutLeft bezoutRight
    DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- A wholly finite squarefree certificate at every displayed nonsingular Legendre parameter. -/
def certificate (lambda : Gaussian)
    (unitNonzero : lambda ^ 2 * (lambda - 1) ^ 2 ≠ 0) :
    Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate (Paths.polynomial lambda) :=
  Evaluation.ofEvalBezoutUnit
    (Paths.polynomial lambda) (Paths.polynomial_isZero lambda)
    (lambda ^ 2 * (lambda - 1) ^ 2) unitNonzero
    (bezoutLeft lambda) (bezoutRight lambda)
      (bezout_identity lambda)

end Purelib.Curves.Legendre.Squarefree

end

end

section
@[expose] public section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

section

namespace Purelib.Curves.Legendre.Squarefree

/-- Explicit parameterized Bezout coefficients for a Legendre cubic. -/
def bezoutLeftAt (lambda : Data.Gaussian.Basic.Canonical) :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[-6 * (lambda ^ 2 - lambda + 1),
    (lambda + 1) * (4 * lambda ^ 2 - 7 * lambda + 4)]⟩

/-- The explicit parameterized right Bezout polynomial for the displayed Legendre cubic. -/
def bezoutRightAt (lambda : Data.Gaussian.Basic.Canonical) :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[2 * (lambda ^ 2 - lambda + 1),
    -(lambda + 1) * (2 * lambda ^ 2 - 3 * lambda + 2),
    lambda * (lambda - 1) ^ 2]⟩

end Purelib.Curves.Legendre.Squarefree

namespace Purelib.Examples.Riemann.ExplicitLegendreFrame

/-- The automatic derivative of the displayed Legendre cubic evaluates to its explicit quadratic. -/
theorem derivative_eval (lambda point :
  Data.Gaussian.Basic.Canonical) :
    (Purelib.Polynomial.Dense.Gaussian.GCD.derivative (Purelib.Curves.Legendre.Paths.polynomial lambda)).eval point =
      3 * point * point - 2 * (lambda + 1) * point + lambda := by
  unfold GCD.derivative
  rw [Derivative.eval_derivative]
  unfold Paths.polynomial
    Derivative.evalDerivativeCoeffs
    Derivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The displayed polynomial and derivative Bezout combination is the exact scalar parameter square times
parameter-minus-one square. -/
theorem bezout_identity (lambda point :
  Data.Gaussian.Basic.Canonical) :
    (Purelib.Curves.Legendre.Squarefree.bezoutLeftAt lambda).eval point * (Paths.polynomial lambda).eval point +
        (Purelib.Curves.Legendre.Squarefree.bezoutRightAt lambda).eval point *
          (GCD.derivative
            (Paths.polynomial lambda)).eval point = lambda ^ 2 * (lambda - 1) ^ 2 := by
  rw [Paths.polynomial_eval, derivative_eval]
  unfold Purelib.Curves.Legendre.Squarefree.bezoutLeftAt Purelib.Curves.Legendre.Squarefree.bezoutRightAt
    DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

end Purelib.Examples.Riemann.ExplicitLegendreFrame

namespace Purelib.Curves.Legendre.Squarefree

/-- Finite squarefreeness for every displayed Legendre parameter whose explicit discriminant-like unit is nonzero. -/
def squarefreeAt (lambda : Data.Gaussian.Basic.Canonical)
    (unitNonzero : lambda ^ 2 * (lambda - 1) ^ 2 ≠ 0) :
    Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate (Paths.polynomial lambda) :=
  Evaluation.ofEvalBezoutUnit
    (Paths.polynomial lambda) (Paths.polynomial_isZero lambda)
    (lambda ^ 2 * (lambda - 1) ^ 2) unitNonzero
    (bezoutLeftAt lambda) (bezoutRightAt lambda)
      (Purelib.Examples.Riemann.ExplicitLegendreFrame.bezout_identity lambda)

end Purelib.Curves.Legendre.Squarefree

end

end
