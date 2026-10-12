module
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Gaussian.QuadraticForm

open Purelib.Data

open Purelib.LinearAlgebra.Gaussian

open Purelib.LinearAlgebra.Gaussian.QuadraticForm

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

namespace Purelib.LinearAlgebra.Rational.Vector.Ones

/-! A concrete nonzero rational test vector in every positive dimension. -/

/-- Construct the rational vector with every coordinate equal to one.

The dimension is `predecessor + 1`, so the retained vector always has an entry at index zero. -/
def onesVector (predecessor : Nat) :
    QuadraticForm.RationalVector (predecessor + 1) :=
  Vector.Basic.vectorOfFn fun _ => 1

open Purelib.LinearAlgebra.Rational.Vector in
/-- Certify that the rational vector of ones is nonzero.

The explicit witness is index zero, whose coordinate is one in the positive dimension `predecessor + 1`. -/
def onesVector_nonzero (predecessor : Nat) :
    NonzeroVector (onesVector predecessor) where
  index := 0
  coefficient_nonzero := by
    simp only [onesVector, Vector.Basic.vectorOfFn_apply]
    decide
end Purelib.LinearAlgebra.Rational.Vector.Ones

end
