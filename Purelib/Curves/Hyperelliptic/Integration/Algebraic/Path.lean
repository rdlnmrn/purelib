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
    (curve : Basic.HyperellipticCurve genus) (differential : Basic.Differential genus) :
    List Cell.Basic.CellModel -> {start finish : LiftedPoint 2} ->
      LiftedPath 2 start finish -> Type 2
  /-- The empty integration-cell list uniformly certifies the constant empty lifted path. -/ | nil (point :
    LiftedPoint 2) :
      UniformPathCertificates curve differential [] (.nil
        point)
  /-- Attach the valid original head-cell certificate and endpoint identities to the matching certified lifted tail. -/
    | cons {start middle finish : LiftedPoint 2}
      {cell : Cell.Basic.CellModel} {cells : List Cell.Basic.CellModel}
      {liftedCell : LiftedCell start middle}
      {remaining : LiftedPath 2 middle finish}
      (start_eq : cell.start = start.coordinate)
      (finish_eq : cell.finish = middle.coordinate)
      (valid : Basis.ValidCellCertificate curve differential liftedCell cell)
      (tail : UniformPathCertificates curve differential
        cells remaining) :
      UniformPathCertificates curve differential (cell ::
        cells)
        (.cons liftedCell remaining)

constructive_injectivity Basis.UniformPathCertificates

namespace UniformPathCertificates

/-- Transport uniform certificates across an equality of starting lifted points. -/
def castStart {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {differential : Basic.Differential genus}
    {cells : List Cell.Basic.CellModel} {left right finish : LiftedPoint 2}
    {path : LiftedPath 2 left finish} (equal : left = right)
    (certificates : UniformPathCertificates curve differential
      cells path) :
    UniformPathCertificates curve differential cells
      (path.castStart equal) := by
  subst right
  exact certificates

/-- Transport uniform certificates across an equality of finishing lifted points. -/
def castFinish {genus :
  Nat}
    {curve : Basic.HyperellipticCurve genus} {differential : Basic.Differential genus}
    {cells : List Cell.Basic.CellModel} {start left right : LiftedPoint 2}
    {path : LiftedPath 2 start left} (equal : left = right)
    (certificates : UniformPathCertificates curve differential
      cells path) :
    UniformPathCertificates curve differential cells
      (path.castFinish equal) := by
  subst right
  exact certificates

/-- Concatenate two uniformly certified finite algebraic paths meeting at the same lifted point. Recursion follows the
executable lifted path; the indexed certificate argument supplies the matching cell certificate at each step. -/
def append {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {differential : Basic.Differential genus}
    {firstCells secondCells : List Cell.Basic.CellModel}
    {start middle finish : LiftedPoint 2}
    {second : LiftedPath 2 middle finish} :
    (first : LiftedPath 2 start middle) ->
      UniformPathCertificates curve differential firstCells first
        ->
        UniformPathCertificates curve differential secondCells
          second ->
          UniformPathCertificates curve differential
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
    {curve : Basic.HyperellipticCurve genus} {differential : Basic.Differential genus}
    {cells : List Cell.Basic.CellModel} {start finish : LiftedPoint 2}
    {path : LiftedPath 2 start finish}
    (certificates :
      UniformPathCertificates curve differential cells path) :
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
    (curve : Basic.HyperellipticCurve genus)
    (differential : OddPower.Basic.OddPowerDifferential curve.polynomial) :
    List Cell.Basic.CellModel -> {start finish : LiftedPoint 2} ->
      LiftedPath 2 start finish -> Type 2
  /-- The empty integration-cell list uniformly certifies the constant empty lifted path. -/ | nil (point :
    LiftedPoint 2) :
      UniformPathCertificates curve differential [] (.nil
        point)
  /-- Attach the valid original head-cell certificate and endpoint identities to the matching certified lifted tail. -/
    | cons {start middle finish : LiftedPoint 2}
      {cell : Cell.Basic.CellModel} {cells : List Cell.Basic.CellModel}
      {liftedCell : LiftedCell start middle}
      {remaining : LiftedPath 2 middle finish}
      (start_eq : cell.start = start.coordinate)
      (finish_eq : cell.finish = middle.coordinate)
      (valid : Jets.ValidCellCertificate curve differential liftedCell cell)
      (tail : UniformPathCertificates curve differential
        cells remaining) :
      UniformPathCertificates curve differential (cell ::
        cells)
        (.cons liftedCell remaining)

constructive_injectivity Jets.UniformPathCertificates

namespace UniformPathCertificates

/-- Concatenate the original odd-power uniform certificates in their retained lifted-cell order. -/
def append {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {differential : OddPower.Basic.OddPowerDifferential curve.polynomial}
    {firstCells secondCells : List Cell.Basic.CellModel} {start middle finish : LiftedPoint 2}
    {second : LiftedPath 2 middle finish} :
    (first : LiftedPath 2 start middle) → UniformPathCertificates curve differential firstCells first →
      UniformPathCertificates curve differential secondCells second →
        UniformPathCertificates curve differential (firstCells ++ secondCells) (first.append second)
  | .nil _, .nil _, secondCertificates => secondCertificates
  | .cons _ remaining, .cons start_eq finish_eq valid tail, secondCertificates =>
      .cons start_eq finish_eq valid (append remaining tail secondCertificates)

/-- The certified head-rotation result on an exactly closed original lifted path.

An empty path has no head to move. A nonempty path retains the original
closing equality and the cyclically ordered original cell certificates.
-/
def HeadRotation {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {differential : OddPower.Basic.OddPowerDifferential curve.polynomial}
    (cells : List Cell.Basic.CellModel) {start finish : LiftedPoint 2}
    (path : LiftedPath 2 start finish) : Type 2 :=
  match path with
  | .nil _ => PUnit
  | .cons (middle := middle) head tail =>
      (closed : finish = start) →
        UniformPathCertificates curve differential (Path.Basic.PathModel.mk cells).rotateHead.cells
          ((closed ▸ tail).append (.cons head (.nil middle)))

/-- Rotate the original uniform certificates using their actual stored cell and geometry owners. -/
def rotate {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {differential : OddPower.Basic.OddPowerDifferential curve.polynomial}
    {cells : List Cell.Basic.CellModel} {start finish : LiftedPoint 2} {path : LiftedPath 2 start finish}
    (certificates : UniformPathCertificates curve differential cells path) :
    HeadRotation (curve := curve) (differential := differential) cells path :=
  UniformPathCertificates.casesOn certificates
    (fun _ => PUnit.unit)
    (fun {actualStart actualMiddle actualFinish cell cells liftedCell remaining}
        start_eq finish_eq valid tail closed => by
      cases closed
      exact append remaining tail (.cons (start := actualStart) (middle := actualMiddle)
        (finish := actualMiddle) (liftedCell := liftedCell) (remaining := .nil actualMiddle)
        start_eq finish_eq valid (.nil actualMiddle)))

/-- Move the original certified head cell to the end of its closed lifted path.

The original valid head certificate and every retained tail certificate are
reused. No algebraic observation or numerical model is constructed again.
-/
def rotateHead {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {differential : OddPower.Basic.OddPowerDifferential curve.polynomial}
    {cells : List Cell.Basic.CellModel} {start middle : LiftedPoint 2}
    {head : LiftedCell start middle} {tail : LiftedPath 2 middle start}
    (certificates : UniformPathCertificates curve differential cells (.cons head tail)) :
    UniformPathCertificates curve differential (Path.Basic.PathModel.mk cells).rotateHead.cells
      (tail.append (.cons head (.nil middle))) := certificates.rotate rfl

/-- Forget the algebraic observation guarantees while retaining exact cell-by-cell alignment with the original lifted
path. -/
theorem toFollowedBy {genus
  : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : OddPower.Basic.OddPowerDifferential curve.polynomial}
    {cells : List Cell.Basic.CellModel} {start finish : LiftedPoint 2}
    {path : LiftedPath 2 start finish}
    (certificates : UniformPathCertificates curve differential
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
