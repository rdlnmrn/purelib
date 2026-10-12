module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
public import Purelib.Integration.Path.Lifted.Model
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Init.Prelude
import Purelib.Data.Gaussian.Basic

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation

open Purelib.Geometry.Path.Gaussian

open Purelib.Geometry.Path.Gaussian.Lifted.Basic

open Purelib.Integration.Polynomial.Gaussian

section
@[expose] public section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Diagnostics.Basis

set_option genInjectivity false in
/-- Cell-for-cell sampled algebraic diagnostics against a finite sheet-aware path. Period programs use
`UniformPathCertificates` below. -/
inductive PathCertificates {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential genus) :
    List Cell.Basic.CellModel -> {start finish : Lifted.Basic.LiftedPoint 2} ->
      Lifted.Basic.LiftedPath 2 start finish -> Type 2
  /-- The empty integration-cell list follows the empty lifted path with no algebraic observations. -/ | nil (point :
    Lifted.Basic.LiftedPoint 2) : PathCertificates
    curve differential [] (.nil point)
  /-- Retain endpoint identities and algebraic observations for the exact head cell, followed by the matching original
    lifted tail. -/ | cons {start middle finish : Lifted.Basic.LiftedPoint 2}
      {cell : Cell.Basic.CellModel} {cells : List Cell.Basic.CellModel}
      {liftedCell : Lifted.Basic.LiftedCell start middle}
      {remaining : Lifted.Basic.LiftedPath 2 middle finish}
      (start_eq : cell.start = start.coordinate)
      (finish_eq : cell.finish = middle.coordinate)
      (observations : Basis.ObservationCertificates curve differential liftedCell cell
        cell.observations)
      (tail : PathCertificates curve differential
        cells remaining) :
      PathCertificates curve differential (cell ::
        cells)
        (.cons liftedCell remaining)

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Diagnostics.Basis.PathCertificates

namespace PathCertificates

/-- Forget only the algebraic equations, retaining the proof that the same integration cells follow the same lifted
path. -/
theorem toFollowedBy {genus
  : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Differentials.Basic.Differential genus}
    {cells : List Cell.Basic.CellModel} {start finish : Lifted.Basic.LiftedPoint 2}
    {path : Lifted.Basic.LiftedPath 2 start finish}
    (certificates : Curves.Hyperelliptic.Integration.Algebraic.Diagnostics.Basis.PathCertificates curve differential
      cells path) :
    LiftedPath.FollowedBy cells path :=
  match certificates with
  | .nil point => .nil point
  | .cons start_eq finish_eq _ tail =>
      .cons start_eq finish_eq
        (toFollowedBy tail)

end PathCertificates

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Diagnostics.Basis

end
