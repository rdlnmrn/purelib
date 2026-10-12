module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
public import Purelib.Integration.Path.Lifted.Model
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Init.Prelude
import Purelib.Data.Gaussian.Basic

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform

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

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Basis

set_option genInjectivity false in
/-- Cell-for-cell uniform algebraic certification of an integration model. Unlike `PathCertificates`, this relation
rules out the one-point and empty-list loopholes on every nonstationary segment. -/
inductive UniformPathCertificates {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential genus) :
    List Cell.Basic.CellModel -> {start finish : Lifted.Basic.LiftedPoint 2} ->
      Lifted.Basic.LiftedPath 2 start finish -> Type 2
  /-- The empty integration-cell list uniformly certifies the constant empty lifted path. -/ | nil (point :
    Lifted.Basic.LiftedPoint 2) :
      UniformPathCertificates curve differential [] (.nil
        point)
  /-- Attach the valid original head-cell certificate and endpoint identities to the matching certified lifted tail. -/
    | cons {start middle finish : Lifted.Basic.LiftedPoint 2}
      {cell : Cell.Basic.CellModel} {cells : List Cell.Basic.CellModel}
      {liftedCell : Lifted.Basic.LiftedCell start middle}
      {remaining : Lifted.Basic.LiftedPath 2 middle finish}
      (start_eq : cell.start = start.coordinate)
      (finish_eq : cell.finish = middle.coordinate)
      (valid : Basis.ValidCellCertificate curve differential liftedCell cell)
      (tail : UniformPathCertificates curve differential
        cells remaining) :
      UniformPathCertificates curve differential (cell ::
        cells)
        (.cons liftedCell remaining)

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates

namespace UniformPathCertificates

/-- Transport uniform certificates across an equality of starting lifted points. -/
def castStart {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Differentials.Basic.Differential genus}
    {cells : List Cell.Basic.CellModel} {left right finish : Lifted.Basic.LiftedPoint 2}
    {path : Lifted.Basic.LiftedPath 2 left finish} (equal : left = right)
    (certificates : Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
      cells path) :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential cells
      (path.castStart equal) := by
  subst right
  exact certificates

/-- Transport uniform certificates across an equality of finishing lifted points. -/
def castFinish {genus :
  Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Differentials.Basic.Differential genus}
    {cells : List Cell.Basic.CellModel} {start left right : Lifted.Basic.LiftedPoint 2}
    {path : Lifted.Basic.LiftedPath 2 start left} (equal : left = right)
    (certificates : Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
      cells path) :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential cells
      (path.castFinish equal) := by
  subst right
  exact certificates

/-- Concatenate two uniformly certified finite algebraic paths meeting at the same lifted point. Recursion follows the
executable lifted path; the indexed certificate argument supplies the matching cell certificate at each step. -/
def append {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Differentials.Basic.Differential genus}
    {firstCells secondCells : List Cell.Basic.CellModel}
    {start middle finish : Lifted.Basic.LiftedPoint 2}
    {second : Lifted.Basic.LiftedPath 2 middle finish} :
    (first : Lifted.Basic.LiftedPath 2 start middle) ->
      Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential firstCells first
        ->
        Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential secondCells
          second ->
          Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
            (firstCells ++ secondCells) (first.append second)
  | .nil _, .nil _, secondCertificates => secondCertificates
  | .cons _ remaining, .cons start_eq finish_eq valid tail,
      secondCertificates =>
      .cons start_eq finish_eq valid
        (append remaining tail
          secondCertificates)

/-- Forget the algebraic observation guarantees while retaining exact cell-by-cell alignment with the original lifted
path. -/
theorem toFollowedBy {genus
  : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Differentials.Basic.Differential genus}
    {cells : List Cell.Basic.CellModel} {start finish : Lifted.Basic.LiftedPoint 2}
    {path : Lifted.Basic.LiftedPath 2 start finish}
    (certificates :
      Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential cells path) :
    LiftedPath.FollowedBy cells path :=
  match certificates with
  | .nil point => .nil point
  | .cons start_eq finish_eq _ tail =>
      .cons start_eq finish_eq
        (toFollowedBy tail)

end UniformPathCertificates

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Basis

end

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets

set_option genInjectivity false in
/-- Cell-for-cell uniform certification against one displayed lifted path. -/
inductive UniformPathCertificates {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : OddPower.Basic.OddPowerDifferential) :
    List Cell.Basic.CellModel -> {start finish : Lifted.Basic.LiftedPoint 2} ->
      Lifted.Basic.LiftedPath 2 start finish -> Type 2
  /-- The empty integration-cell list uniformly certifies the constant empty lifted path. -/ | nil (point :
    Lifted.Basic.LiftedPoint 2) :
      UniformPathCertificates curve differential [] (.nil
        point)
  /-- Attach the valid original head-cell certificate and endpoint identities to the matching certified lifted tail. -/
    | cons {start middle finish : Lifted.Basic.LiftedPoint 2}
      {cell : Cell.Basic.CellModel} {cells : List Cell.Basic.CellModel}
      {liftedCell : Lifted.Basic.LiftedCell start middle}
      {remaining : Lifted.Basic.LiftedPath 2 middle finish}
      (start_eq : cell.start = start.coordinate)
      (finish_eq : cell.finish = middle.coordinate)
      (valid : Jets.ValidCellCertificate curve differential liftedCell cell)
      (tail : UniformPathCertificates curve differential
        cells remaining) :
      UniformPathCertificates curve differential (cell ::
        cells)
        (.cons liftedCell remaining)

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets.UniformPathCertificates

namespace UniformPathCertificates

/-- Forget the algebraic observation guarantees while retaining exact cell-by-cell alignment with the original lifted
path. -/
theorem toFollowedBy {genus
  : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : OddPower.Basic.OddPowerDifferential}
    {cells : List Cell.Basic.CellModel} {start finish : Lifted.Basic.LiftedPoint 2}
    {path : Lifted.Basic.LiftedPath 2 start finish}
    (certificates : Curves.Hyperelliptic.Integration.Algebraic.Path.Jets.UniformPathCertificates curve differential
      cells path) :
    LiftedPath.FollowedBy cells path :=
  match certificates with
  | .nil point => .nil point
  | .cons start_eq finish_eq _ tail =>
      .cons start_eq finish_eq
        (toFollowedBy tail)

end UniformPathCertificates

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets

end
