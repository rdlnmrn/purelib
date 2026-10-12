module
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
import Purelib.Polynomial.Elimination.Axis.Separated
public import Purelib.RootIsolation.Exact.LargeSquare

public import Purelib.Polynomial.Elimination.Axis.Replay
import Purelib.Polynomial.Elimination.Separated.Bezout.Replay
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.Exact.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
Restore the original axis certificate from checked separated-Sylvester data.
Both the scalar polynomials and the executable Bézout callbacks consume those
data. The degree bound is read from the restored polynomials as well.
These are the existing finite constructors, with their recursive inverse
inputs supplied by exact replay; no alternate eliminant is introduced.
-/

namespace Purelib.RootIsolation.Exact.Replay.Elimination

open Purelib.Polynomial.Elimination.SylvesterBezout
open Purelib.Polynomial.Dense.Basic.DensePolynomial

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}

/-- The cached degree and restored callbacks select the original ordered
isolation, including all track constructors and residual regions. -/
theorem isolation_eq (first :
  Elimination.Separated.Bezout.Replay.Saved p) (second : Elimination.Separated.Bezout.Replay.Saved
  (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p))
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree)
    (higher : 2 ≤ p.natDegree) (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) :
    Exact.LargeSquare.isolateLargeSquare higher squarefree (Elimination.Axis.Replay.certificate first second nonzero
      positive) =
      Exact.LargeSquare.isolateLargeSquare higher squarefree
        (Elimination.Axis.Separated.separatedAxisEliminationCertificate p nonzero positive) := by
  rcases first with ⟨first, firstEq⟩
  rcases second with ⟨second, secondEq⟩
  cases firstEq
  cases secondEq
  rfl

end Purelib.RootIsolation.Exact.Replay.Elimination

end
