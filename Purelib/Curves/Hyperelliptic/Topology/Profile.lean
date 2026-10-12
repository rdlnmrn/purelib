module
public import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Topology.BranchProfile
import Purelib.Topology.BranchedCover
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Topology

open Purelib.Topology

open Purelib.Topology.BranchedCover

section
public section

/-!
# Degree-selected finite topology of an original hyperelliptic curve

The retained odd or even degree witness selects the finite branch-at-infinity
profile and its arithmetic genus certificate. The resulting cell model keeps
the same original curve owner and computes its displayed Euler characteristic.
-/

namespace Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve

/-- The finite branch-at-infinity profile selected by the displayed degree certificate. -/
@[expose] def branchProfile {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    BranchedCover.BranchProfile :=
  match curve.degreeShape with
  | .odd _ => BranchProfile.oddDegreeProfile genus
  | .even _ => BranchProfile.evenDegreeProfile genus

/-- Retain the genus certificate selected by the curve polynomial degree shape.

The odd and even degree witnesses select their corresponding finite double-cover branch profiles without changing the
curve owner. -/
@[expose] def genusCertificate {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    BranchedCover.GenusCertificate curve.branchProfile := by
  cases curve with
  | mk polynomial nonzero squarefree degreeShape =>
      cases degreeShape with
      | odd degreeEqual =>
          exact BranchProfile.oddDegreeGenusCertificate genus
      | even degreeEqual =>
          exact BranchProfile.evenDegreeGenusCertificate genus

/-- The selected finite branch-profile certificate computes the original curve genus. -/
theorem computedGenus {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    curve.genusCertificate.genus = genus := by
  cases curve with
  | mk polynomial nonzero squarefree degreeShape =>
      cases degreeShape with
      | odd degreeEqual =>
          exact BranchProfile.oddDegree_computedGenus genus
      | even degreeEqual =>
          exact BranchProfile.evenDegree_computedGenus genus

/-- Construct the finite branched cell model from the curve degree-selected branch profile. -/
@[expose] def cellModel {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    BranchedCover.BranchedCellModel :=
  BranchedCover.branchedCover curve.branchProfile

/-- The curve cell model has Euler characteristic two minus twice its retained genus. -/
theorem cellModel_eulerCharacteristic {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    curve.cellModel.eulerCharacteristic = (2 : Int) - 2 * genus := by
  have genusIdentity :=
    GenusCertificate.eulerCharacteristic_eq_two_sub_twice_genus
      curve.genusCertificate
      (BranchedCover.spherePolygonCellulation curve.branchProfile.cycles.length)
  rw [curve.computedGenus] at genusIdentity
  exact genusIdentity

end Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve

end
