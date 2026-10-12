module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.RootContinuation.SquareRootOwnerReplay

@[expose] public section

/-!
Canonical bank seeds reconstructed from the two checked endpoint families.
These adapters preserve the complete original prepared cycles.  They cache
the endpoint isolations, not bank preparation or its selected depths.
-/

namespace Purelib.Riemann.Topology.PreparedCycleSeedReplay

open Purelib.Riemann.Topology.PreparedCycleModels
open Purelib.Riemann.RootContinuation.SquareRootOwnerFamily (IndependentFamily)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  (branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) (higher : 1 <
    curve.polynomial.natDegree)
  (left right : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (refinement : Nat)
  (leftFamily : IndependentFamily (curve.polynomial.eval (Purelib.Curves.Hyperelliptic.Branches.Cuts.refinedTrackAnchor
    branches higher left refinement)))
  (rightFamily : IndependentFamily (curve.polynomial.eval (Purelib.Curves.Hyperelliptic.Branches.Cuts.refinedTrackAnchor
    branches higher right refinement)))

/-- Construct the original boundary cycle from two retained endpoint-owner families.

The four canonical sheet owners seed the connector and boundary banks at the original branch indices and refinement. -/
def boundary : PreparedBoundaryDoublePath curve :=
  PreparedBoundaryDoublePath.ofConnectorAtWithOwners branches higher left right refinement
    (leftFamily.owner 0) (rightFamily.owner 0) (rightFamily.owner 1) (leftFamily.owner 1)

/-- The retained endpoint families reconstruct exactly the canonical prepared boundary cycle. -/
theorem boundary_eq : boundary branches higher left right refinement leftFamily rightFamily =
    PreparedBoundaryDoublePath.ofConnectorAt branches higher left right refinement := by
  unfold boundary
  rw [leftFamily.owner_eq_independent 0, rightFamily.owner_eq_independent 0,
    rightFamily.owner_eq_independent 1, leftFamily.owner_eq_independent 1]
  rfl

/-- Construct the original bridge from the retained forward and backward endpoint owners.

The same branch indices and refinement determine the connector, using sheet zero at the left endpoint and sheet one at
the right endpoint. -/
def bridge : PreparedDoublePath curve :=
  PreparedDoublePath.ofConnectorAtWithOwners branches higher left right refinement
    (leftFamily.owner 0) (rightFamily.owner 1)

/-- The retained endpoint families reconstruct exactly the canonical prepared bridge. -/
theorem bridge_eq : bridge branches higher left right refinement leftFamily rightFamily =
    PreparedDoublePath.ofConnectorAt branches higher left right refinement := by
  unfold bridge
  rw [leftFamily.owner_eq_independent 0, rightFamily.owner_eq_independent 1]
  rfl

end Purelib.Riemann.Topology.PreparedCycleSeedReplay
