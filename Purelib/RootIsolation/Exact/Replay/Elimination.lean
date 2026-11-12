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
Retain the original ordered isolation and its canonical refinement functions
while supplying scalar eliminants from checked inverse data. The certificate
readback includes its callbacks; transporting the certified degree index does
not change any retained isolation value.
-/

namespace Purelib.RootIsolation.Exact.Replay.Elimination

open Purelib.Polynomial.Elimination.SylvesterBezout
open Purelib.Polynomial.Dense.Basic.DensePolynomial

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}

/-- Reindexing an axis certificate by an exact bound equality preserves its complete isolation output. -/
private theorem isolate_castDegree
    {leftBound rightBound : Nat} (same : leftBound = rightBound)
    (higher : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p leftBound) :
    Exact.LargeSquare.isolateLargeSquare higher squarefree
      (show Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p rightBound from same ▸ elimination) =
      Exact.LargeSquare.isolateLargeSquare higher squarefree elimination := by
  cases same
  rfl

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
  exact (isolate_castDegree (Elimination.Axis.Replay.degree_eq first second) higher squarefree
    (Elimination.Axis.Replay.certificate first second nonzero positive)).symm.trans
      (congrArg (fun elimination => Exact.LargeSquare.isolateLargeSquare higher squarefree elimination)
        (Elimination.Axis.Replay.certificate_eq first second nonzero positive))

end Purelib.RootIsolation.Exact.Replay.Elimination

end
