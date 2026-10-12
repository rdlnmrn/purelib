module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Matrix.Operational.Types
public import Purelib.LinearAlgebra.Gaussian.ImaginaryPositive
import Purelib.LinearAlgebra.Matrix.Basic
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Periods.PeriodMatrix

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Matrix.Operational

open Purelib.LinearAlgebra.Gaussian

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

namespace RiemannMatrixWitness

/-- Exact rational matrices are also productive CCL matrices. -/
def namedOmega {size : Nat} (witness :
  ImaginaryPositive.RiemannMatrixWitness size) :
    Types.ExactNamedMatrix size :=
  LinearAlgebra.Matrix.matrixOfFn fun row column =>
    Coherence.exact (witness.omega row column)

/-- Exact symmetry becomes operational equality of the corresponding CCL entry names. -/
def operationally_symmetric {size : Nat}
    (witness : ImaginaryPositive.RiemannMatrixWitness size) (row column : Fin size) :
    Gaussian.Equivalence.NamedEquivalent (witness.namedOmega row column).name
      (witness.namedOmega column row).name := by
  rw [namedOmega,
    LinearAlgebra.Matrix.matrixOfFn_apply,
    LinearAlgebra.Matrix.matrixOfFn_apply,
    witness.symmetric row column]
  exact NamedEquivalent.refl _
end RiemannMatrixWitness
end Purelib.LinearAlgebra.Gaussian.ImaginaryPositive

end
