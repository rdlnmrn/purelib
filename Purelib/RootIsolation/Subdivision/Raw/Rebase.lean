module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.State.Raw
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-! Restore the original Newton source selection from checked safe-subdivision
stages, then reuse that source in the unchanged local extraction construction.
The source ownership equation is exact, including its boundary bound. -/
namespace Purelib.RootIsolation.Subdivision.Raw.Rebase

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)

/-- Rebase a nonzero-winding state on its own box, retaining its polynomial, properness and boundary clearance. -/
def initial : State.Raw.RawWindingState p current.box :=
  ⟨current.box, Box.refines_refl current.box, current.proper,
    current.clearance, current.rawWinding_ne⟩
end Purelib.RootIsolation.Subdivision.Raw.Rebase

end
