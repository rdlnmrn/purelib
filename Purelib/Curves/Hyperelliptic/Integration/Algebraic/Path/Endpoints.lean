module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path

/-! # Exact endpoint transports for retained odd-power path certificates -/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets.UniformPathCertificates

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

variable {genus : Nat} {curve : HyperellipticCurve genus}
variable {differential : OddPowerDifferential curve.polynomial} {cells : List CellModel}

/-- Reindex the original odd-power path certificates at an exactly equal starting lifted point. -/
def castStart {first next last : LiftedPoint 2} {path : LiftedPath 2 first last}
    (equal : first = next) (certificates : UniformPathCertificates curve differential cells path) :
    UniformPathCertificates curve differential cells (path.castStart equal) := by
  cases equal
  exact certificates

/-- Reindex the original odd-power path certificates at an exactly equal finishing lifted point. -/
def castFinish {first last next : LiftedPoint 2} {path : LiftedPath 2 first last}
    (equal : last = next) (certificates : UniformPathCertificates curve differential cells path) :
    UniformPathCertificates curve differential cells (path.castFinish equal) := by
  cases equal
  exact certificates

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets.UniformPathCertificates

end
