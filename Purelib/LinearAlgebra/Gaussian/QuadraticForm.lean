module

public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra

open Purelib

open Purelib.Data.Rat

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

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

namespace Purelib.LinearAlgebra.Gaussian.QuadraticForm

/-- A structural square matrix of exact Gaussian rational coefficients. -/
abbrev ExactGaussianMatrix (size : Nat) :=
  SquareMatrix Data.Gaussian.Basic.Canonical size
end Purelib.LinearAlgebra.Gaussian.QuadraticForm

end

section
@[expose] public section

/-!
# Finite Gaussian matrix quadratic form

The displayed rational vector has an explicit nonzero coordinate witness.
The imaginary quadratic form is the original finite double sum over the
retained Gaussian matrix.  No period or curve data enters this construction.
-/

namespace Purelib.LinearAlgebra.Gaussian.QuadraticForm

/-- A structural rational vector with retained finite dimension. -/
abbrev RationalVector (size : Nat) :=
  Data.Vector Fraction.Rational size
/-- A structural square matrix of Gaussian rational coefficients. -/
abbrev GaussianMatrix (size : Nat) :=
  SquareMatrix Data.Gaussian.Basic.Canonical size

set_option genInjectivity false in
/-- A displayed nonzero coordinate is the constructive witness that a finite
rational vector is nonzero. -/
structure NonzeroVector {size : Nat} (vector : RationalVector size) where
  /-- A retained bounded coordinate witnessing nonvanishing of the rational vector. -/ index : Fin size
  /-- The retained vector coefficient at the witness coordinate is nonzero. -/ coefficient_nonzero : vector index ≠ 0

constructive_injectivity NonzeroVector

/-- The rational imaginary quadratic form of a displayed finite matrix. -/
def imaginaryQuadraticForm {size : Nat} (vector : RationalVector size)
    (matrix : GaussianMatrix size) : Fraction.Rational :=
  FiniteSum.Fin.sumFin fun row =>
    FiniteSum.Fin.sumFin fun column =>
      vector row * (matrix row column).im * vector column

end Purelib.LinearAlgebra.Gaussian.QuadraticForm

end
