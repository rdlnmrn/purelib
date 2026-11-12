module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
public import Purelib.Geometry.Path.Gaussian.Lifted.Endpoints
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Rat.Fraction.Basic

/-! # Endpoint-index transport of retained uniform cell certificates

Exact endpoint identities transport the original lifted-cell index while
preserving its entire observation callback and every retained query owner.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformCellCertificate

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Data.Rat.Fraction (Rational)

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : OddPowerDifferential curve.polynomial}
    {start finish first last : LiftedPoint 2} {lifted : LiftedCell start finish} {cell : CellModel}

/-- Transport only the original lifted-cell endpoint indices of a uniform certificate. -/
def castEndpoints (retained : UniformCellCertificate curve differential lifted cell)
    (firstEq : start = first) (lastEq : finish = last) :
    UniformCellCertificate curve differential (lifted.castEndpoints firstEq lastEq) cell := by
  cases firstEq
  cases lastEq
  exact retained

/-- Endpoint transport retains the complete original certificate and callback up to its dependent indices. -/
private theorem packaged_castEndpoints_heq (retained : UniformCellCertificate curve differential lifted cell)
    (firstEq : start = first) (lastEq : finish = last) :
    HEq (retained.castEndpoints firstEq lastEq) retained := by
  cases firstEq
  cases lastEq
  exact HEq.rfl

/-- Endpoint transport retains the complete original certificate and callback up to its dependent indices. -/
theorem castEndpoints_heq (retained : UniformCellCertificate curve differential lifted cell)
    (firstEq : start = first) (lastEq : finish = last) :
    HEq (retained.castEndpoints firstEq lastEq) retained :=
  packaged_castEndpoints_heq retained firstEq lastEq

/-- Every transported scalar query keeps its original full generator name. -/
private theorem packaged_castEndpoints_root_name
    (retained : UniformCellCertificate curve differential lifted cell)
    (firstEq : start = first) (lastEq : finish = last)
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1) :
    ((retained.castEndpoints firstEq lastEq).query input lower upper).algebraic.sheetValue.value.name =
      (retained.query input lower upper).algebraic.sheetValue.value.name := by
  cases firstEq
  cases lastEq
  rfl

/-- Every transported scalar query keeps its original full generator name. -/
theorem castEndpoints_root_name (retained : UniformCellCertificate curve differential lifted cell)
    (firstEq : start = first) (lastEq : finish = last)
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1) :
    ((retained.castEndpoints firstEq lastEq).query input lower upper).algebraic.sheetValue.value.name =
      (retained.query input lower upper).algebraic.sheetValue.value.name :=
  packaged_castEndpoints_root_name retained firstEq lastEq input lower upper

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformCellCertificate

end
