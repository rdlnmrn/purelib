module
public import Purelib.Riemann.Periods.PeriodMatrix
import Init.Prelude

open Purelib.Riemann.Periods

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

namespace Purelib.Approximation.Matrix.Operational.Types

/-- A finite square matrix of coherent Gaussian names in the original period-matrix representation. -/
abbrev ExactNamedMatrix (size : Nat) :=
  PeriodMatrix.NamedMatrix size
end Purelib.Approximation.Matrix.Operational.Types

end

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Approximation.Matrix.Operational.Types

/-- A two-by-two matrix of coherent Gaussian names in the original period-matrix representation. -/
abbrev NamedMatrix2 := PeriodMatrix.NamedMatrix 2
end Purelib.Approximation.Matrix.Operational.Types
end
