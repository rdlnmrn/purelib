module

public import Purelib.Riemann.Paths.OwnerTracePath
public import Purelib.RootIsolation.SquareRoot.Owner.Transport
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Polynomial.Dense.Evaluation

/-! # Actual stationary joins through exact coordinate-index transport

Only the original left Owner's parameter index changes. The separate
signed name relation supplies the real OwnerJoin; exact physical endpoint
equality then places its stationary link at the two original coordinates.
Neither an Owner nor a primitive observation is replaced.
-/

public section

open Purelib
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Coefficients
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter)

namespace Purelib.Riemann.Paths.OwnerTraceReadings.OwnerJoin

/-- Acquire a real join after changing only the original left Owner's equal-coordinate parameter index. -/
def acquireAt {polynomial : Coefficients} {start finish : Canonical}
    {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
    (same : start = finish) (roots : NamedEquivalent (ownerName left) (ownerName right)) :
    OwnerJoin (castOwnerParameter (congrArg polynomial.eval same) left) right := by
  cases same
  exact acquire left right roots

end Purelib.Riemann.Paths.OwnerTraceReadings.OwnerJoin

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerLink

/-- Retain an actual stationary join as a link at both original physical coordinates and original Owner indices. -/
def ofJoinAt {polynomial : Coefficients} {start finish : Canonical}
    {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
    (same : start = finish)
    (join : OwnerJoin (castOwnerParameter (congrArg polynomial.eval same) left) right) :
    OwnerLink polynomial start finish left right := by
  cases same
  exact stationary polynomial start join

end Purelib.Riemann.Paths.OwnerTracePath.OwnerLink

end
