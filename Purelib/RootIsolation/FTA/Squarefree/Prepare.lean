module

import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.RootIsolation.Exact.Basic
public import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.RootIsolation.Exact.Ownership.Cardinality
public import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free box-only finite constructive FTA

This is the paper-facing numerical layer over the explicit constructive
fraction and Gaussian representations.  The squarefree certificate is finite
dense extended-Euclid data.  Both axis eliminants are computed internally by
the fraction-free separated Sylvester construction.
-/

namespace Purelib.RootIsolation.FTA.Squarefree.Input
section Input

/-- The exact finite degree bound of the two internally computed axis
eliminants. -/
def eliminationDegree {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (_input : Input p) : Nat :=
  Elimination.Axis.Separated.separatedEliminationDegree p

/-- Closed finite axis-elimination certificate computed from `p`'s displayed
coefficient list. -/
def elimination {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input
  : Input p) :
    Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p
      input.eliminationDegree :=
  Elimination.Axis.Separated.separatedAxisEliminationCertificate p
    input.nonzero input.degreePositive

/-- Exact degree-many isolation in the coefficient-computed large square. -/
def isolation {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input :
  Input p) :
    Exact.Basic.Output p
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) p.natDegree :=
  Exact.LargeSquare.isolateLargeSquare input.degreeAtLeastTwo
    input.squarefree input.elimination

/-- Degree-sharp bound for every finite pairwise-separated family of
winding-one tracks in the same large square. -/
theorem familyCardLe
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : Input p) {familyCount :
      Nat}
    (family : Fin familyCount → Track.Basic.WindingOneTrack p
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
    (pairwise : ∀ left right, left ≠ right →
      (family left).initial.box.Separated
        (family right).initial.box) :
    familyCount ≤ p.natDegree :=
  Exact.Ownership.Cardinality.family_card_le_natDegree
    input.degreeAtLeastTwo input.squarefree input.elimination family pairwise

end Input
end Purelib.RootIsolation.FTA.Squarefree.Input

end
