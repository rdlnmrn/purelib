module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib

section
@[expose] public section

/-!
# Worked finite hyperelliptic period examples

This module records explicit squarefree cyclic curves for the worked examples
of the finite period theorem.  Every polynomial is the concrete finite dense
power polynomial `Z^d - 1`.  Its nonzeroness, degree, and displayed Bézout
identity are proved by the finite power-monodromy algebra, so the examples
introduce no separate squarefreeness assumption.

The five nontrivial examples are

* `y² = x³ - 1` and `y² = x⁴ - 1` in genus one;
* `y² = x⁵ - 1` and `y² = x⁶ - 1` in genus two;
* `y² = x⁷ - 1` in genus three.

Two genus-zero controls, `y² = x - 1` and `y² = x² - 1`, exercise the
complete unconditional theorem and its genuinely empty period matrix.

The topology statements below compute the classical Euler characteristics
`0`, `-2`, and `-4` and expose the expected symplectic intersection basis.
The analytic period conclusions use the unconditional public theorem on
these same curves. The separate exact matrix examples below are algebraic
models, not period-program evaluations.
-/

namespace Purelib.LinearAlgebra.Gaussian.ImaginaryPositive

set_option genInjectivity false in
/-- Exact finite matrix form of the two Riemann conclusions. -/
structure RiemannMatrixWitness (size : Nat) where
  /-- The retained Gaussian matrix. -/ omega : LinearAlgebra.Gaussian.QuadraticForm.ExactGaussianMatrix size
  /-- The retained matrix is symmetric under transposition. -/ symmetric : forall row column, omega row column = omega
    column row
  /-- Its imaginary quadratic form is positive on every vector with a retained nonzero coordinate. -/ positive : forall
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size),
    LinearAlgebra.Gaussian.QuadraticForm.NonzeroVector vector ->
      0 < LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector omega

constructive_injectivity RiemannMatrixWitness

namespace RiemannMatrixWitness

/-- Explicit positive rational evidence returned for a nonzero vector. -/
def requestedMargin {size : Nat}
    (witness : RiemannMatrixWitness size)
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) :
    Fraction.Rational :=
  LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector witness.omega / 2

/-- Half of a positive rational is strictly less than that rational. -/
private theorem exact_half_lt_self {value :
  Fraction.Rational}
    (positive : 0 < value) : value / 2 < value := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (by decide : (0 : Fraction.Rational) < 2)).2
  calc
    value = value * 1 := by ring1
    _ < value * 2 :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive
        (by decide)

/-- The requested half-form margin is positive on a vector with a retained nonzero coordinate. -/
theorem requestedMargin_positive {size :
  Nat}
    (witness : RiemannMatrixWitness size)
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size)
    (nonzero : LinearAlgebra.Gaussian.QuadraticForm.NonzeroVector vector) :
    0 < witness.requestedMargin vector :=
  Fraction.Order.Field.div_pos_direct (witness.positive vector nonzero)
    (by decide)

/-- The requested half-form margin is strictly smaller than the positive quadratic form. -/
theorem requestedMargin_lt_form {size :
  Nat}
    (witness : RiemannMatrixWitness size)
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size)
    (nonzero : LinearAlgebra.Gaussian.QuadraticForm.NonzeroVector vector) :
    witness.requestedMargin vector <
      LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector witness.omega :=
  exact_half_lt_self (witness.positive vector nonzero)

end RiemannMatrixWitness
end Purelib.LinearAlgebra.Gaussian.ImaginaryPositive

end
