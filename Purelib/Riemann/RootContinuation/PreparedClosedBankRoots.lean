module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Integration.PreparedSwitchedRefinements

public import Purelib.Riemann.Topology.PreparedBankRootChains
public import Purelib.Riemann.Integration.PreparedOwnerClosedSchedules
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Gaussian.Basic

@[expose] public section

/-!
# Root closure on the actual initial cycle-parent lists

The existing closed owner tour determines all root joins of the four banks
consumed by its period schedule.  The stationary sheet-label cells contribute
no parent and do not authorize a root change: actual handoffs are proved from
the retained sequential owners and the checked final monodromy return.
-/

namespace Purelib.Riemann.RootContinuation.PreparedClosedBankRoots

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Topology.PreparedBankRootChains (dyadicBankRootChain)
open Purelib.Riemann.Readings.PreparedBoundaryGluing (JoinedBoundaryDoublePath)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)
open Purelib.Riemann.Integration.PreparedSwitchedRefinements

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

namespace JoinedBoundaryDoublePath

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Topology in
/-- Join the retained boundary-bank root chains using their exact owner identities.

The original bank order and centered parent list are preserved. The endpoint root names remain those of the original
first and last owners. -/
def initialRootChain (tour : JoinedBoundaryDoublePath curve) (differential : Differentials.Basic.Differential genus) :
    RootChain (PreparedSwitchedRefinements.boundaryState curve differential tour.data).parents
      (ownerName tour.data.forwardOwner) (ownerName tour.finishOwner) := by
  let forward := dyadicBankRootChain curve differential 0 tour.data.forwardChecked
  let right := PreparedBankRootChains.RootChain.castNames
    (congrArg ownerName tour.rightOwner_eq) rfl (dyadicBankRootChain curve differential 0
      tour.data.rightBoundaryChecked)
  let backward := PreparedBankRootChains.RootChain.castNames
    (congrArg ownerName tour.backwardOwner_eq) rfl (dyadicBankRootChain curve differential 1 tour.data.backwardChecked)
  let left := PreparedBankRootChains.RootChain.castNames
    (congrArg ownerName tour.leftOwner_eq) (congrArg ownerName tour.finishOwner_eq.symm)
    (dyadicBankRootChain curve differential 1 tour.data.leftBoundaryChecked)
  exact PreparedBankRootChains.RootChain.castChildren
    (PreparedSwitchedRefinements.boundaryState_parents curve differential tour.data).symm
    (forward.append (right.append (backward.append left)))

end JoinedBoundaryDoublePath

namespace ClosedBoundaryDoublePath

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- Close the retained boundary-bank root chain using the supplied root-return equivalence.

The exact schedule parent list is unchanged; the final name is transported to the original initial root name. -/
def initialRootChain (tour : ClosedBoundaryDoublePath curve) (differential : Differentials.Basic.Differential genus) :
    RootChain (PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath.schedule tour
      differential).toDifferential.initial.parents
      (ownerName tour.joined.data.forwardOwner) (ownerName tour.joined.data.forwardOwner) :=
  PreparedBankRootChains.RootChain.changeFinish
    (PreparedClosedBankRoots.JoinedBoundaryDoublePath.initialRootChain tour.joined differential) tour.rootEquivalent

end ClosedBoundaryDoublePath

end Purelib.Riemann.RootContinuation.PreparedClosedBankRoots
