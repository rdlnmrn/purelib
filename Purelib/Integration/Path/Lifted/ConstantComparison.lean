module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
public import Purelib.Integration.Energy.AffineTriangle
import Purelib.Integration.Path.Lifted.Model
public import Purelib.Integration.Polynomial.ConstantComparison
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Constant
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Triangulated finite surface energy

This module supplies the two-dimensional algebraic bridge for the second
Riemann bilinear relation.  A finite sample consists of a genuine oriented
triangulation, primitive values at its vertices, an exact identification of
its outer boundary with the displayed A/B period commutators, and a checked
lower-energy inequality on every face.  Incidence cancellation and finite
summation then derive the global surface lower theorem consumed by
`PreparedEnergy`; it is not repeated as an assumption.
-/

namespace Purelib.Integration.Path.Lifted.ConstantComparison

open Purelib.Data.Gaussian in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Energy in
open Purelib.Integration.Polynomial in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read an original constant-cell lifted-path integral as its affine reference increment plus retained coefficient
errors.

The following witness connects the original model displacement to the same lifted endpoints, preserving the exact
ordered constant-cell error terms. -/
theorem constantFollowedPathIntegralSample_eq_affine_add_error
    {cells : List Basic.CellModel} {start finish : Lifted.Basic.LiftedPoint 2}
    {path : Lifted.Basic.LiftedPath 2 start finish}
    (constant :
      Basic.PathModel.ConstantCells cells)
    (follows : path.FollowedBy cells)
    (reference : Basic.Canonical) :
    (Basic.PathModel.mk cells).integralSample =
      AffineTriangle.affinePrimitiveIncrement reference start.coordinate finish.coordinate +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (ConstantComparison.constantReferenceErrorTerms constant reference) := by
  rw [ConstantComparison.constantPathIntegralSample_eq_reference_add_error constant reference,
    Lifted.Basic.LiftedPath.followedBy_displacementSum follows]
  unfold AffineTriangle.affinePrimitiveIncrement
  apply Basic.ext <;>
    simp only [Basic.add_re,
      Basic.add_im,
      Basic.sub_re,
      Basic.sub_im,
      Basic.mul_re,
      Basic.mul_im] <;> ring1

end Purelib.Integration.Path.Lifted.ConstantComparison

end
