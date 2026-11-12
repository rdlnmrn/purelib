module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Region.Sum
import Purelib.RootIsolation.Exact.Build
public import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.RootIsolation.Exact.State

public import Purelib.RootIsolation.Exact.LargeSquare.Region
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.Exact.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Exact isolation steps from checked extraction checkpoints

Rebuild the numerical fields of an isolation state and retain the original
track constructors.  Equality is to the canonical step, not to an arbitrary
equivalent root family.  Proof-only references to that step disappear from
the executable replay.  This imports only existing finite isolation modules.
-/

namespace Purelib.RootIsolation.Exact.LargeSquare.Replay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
variable (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
section Steps

variable (state : Exact.State.IsolationState p ambient)
  (nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
  (positive : 0 < Winding.Box.Region.Sum.totalRaw state.regions)
end Steps

section Runs

variable {state : Exact.State.IsolationState p ambient}
end Runs

/-- Symmetric-square isolation is the complete original run on its same named clear region. -/
theorem symmetric_eq {radius : Data.Rat.Fraction.Rational}
    (radiusLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ radius)
    (request : Option Data.Rat.Fraction.Rational := none) :
    LargeSquare.isolateSymmetric degreeAtLeastTwo squarefree elimination radiusLe request =
      Build.isolateFromRegion degreeAtLeastTwo squarefree elimination
        (Region.symmetricRegion degreeAtLeastTwo radiusLe) p.natDegree
        (Region.symmetricRegion_winding degreeAtLeastTwo radiusLe) request := (rfl)

/-- The original large-square isolation is exactly isolation from its named coefficient-computed clear region. -/
theorem largeSquare_eq (request : Option Data.Rat.Fraction.Rational := none) :
    Exact.LargeSquare.isolateLargeSquare degreeAtLeastTwo squarefree elimination request =
      Exact.Build.isolateFromRegion degreeAtLeastTwo squarefree elimination
        (Exact.LargeSquare.Region.largeSquareRegion degreeAtLeastTwo) p.natDegree
          (Exact.LargeSquare.Region.largeSquareRegion_winding degreeAtLeastTwo) request := rfl

end Purelib.RootIsolation.Exact.LargeSquare.Replay

end
