module
public import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Approximation.Name
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Approximation.Gaussian

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace Purelib.RootIsolation.FTA.Squarefree.AdapterResult
section Result

/-- A higher-degree Paper-I root track, exposed directly as a progressive
squared-error arithmetic name without extracting a completed root. -/
def arithmeticNameAt {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (result : FTA.Squarefree.AdapterResult p)
    (index : Fin p.natDegree) :
    Name.Basic.Named :=
  Track.Approximation.Name.initialNamed (result.trackAt index)

/-- Start the CCL arithmetic cursor at an explicitly requested later RFAP
root box. -/
def refinedArithmeticNameAt
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      FTA.Squarefree.AdapterResult p)
    (index : Fin p.natDegree)
    (current : State.WindingOne.Basic.WindingOneState p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Name.Basic.Named :=
  Track.Approximation.Name.refinedNamed (result.trackAt index)
    current epsilon positive
end Result
end Purelib.RootIsolation.FTA.Squarefree.AdapterResult

end
