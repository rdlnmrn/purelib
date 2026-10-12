module
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.Readings.PreparedBoundaryClosure
public import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.List.Append

public section

/-!
# Existing period schedules seeded by operationally closed owner tours

The closed tour's four cached integration banks are passed directly to the
existing switched refinement program.  Its A-cycle specialization retains
the original standard A geometry, while constructing all owner handoffs and
the final root return from one initial sheet.

These are explicitly named owner-closed seeds.  No equivalence with the old
independently seeded period names is assumed, and no B-cycle or geometric
intersection theorem is asserted here.  The return witness below concerns
the retained initial banks; propagation through every later refinement is a
separate obligation.
-/

namespace Purelib.Riemann.Integration.PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath

open Purelib.Data.List

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (StandardSwitchedClosedSchedule)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)
open Purelib.Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath
open Purelib.Riemann.Topology.PreparedCycleModels (PreparedCycleData)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

section
open Purelib.Curves.Hyperelliptic
/-- Use the retained closed boundary tour as the finite-cut geometry for all standard-differential readings. -/
@[expose] def schedule (tour : ClosedBoundaryDoublePath curve) (source : Differentials.Basic.Differential genus) :
    StandardSwitchedClosedSchedule curve :=
  ⟨source, .finiteCut tour.joined.data⟩

/-- The resulting schedule retains exactly the original joined finite-cut data. -/
theorem schedule_prepared (tour : ClosedBoundaryDoublePath curve) (source : Differentials.Basic.Differential genus) :
    (schedule tour source).prepared = .finiteCut tour.joined.data := rfl

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- The schedule retains the four original banks' centered parents in boundary-tour order.

The original concatenation order and all four cached banks are retained; associativity only identifies the displayed
list bracketing. -/
theorem schedule_initial_parents (tour : ClosedBoundaryDoublePath curve) (source : Differentials.Basic.Differential
  genus) :
    (schedule tour source).toDifferential.initial.parents =
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
        curve source 0 tour.joined.data.forwardChecked).parents ++
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
        curve source 0 tour.joined.data.rightBoundaryChecked).parents ++
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
        curve source 1 tour.joined.data.backwardChecked).parents ++
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
        curve source 1 tour.joined.data.leftBoundaryChecked).parents := by
  change (PreparedSwitchedRefinements.boundaryState curve source tour.joined.data).parents = _
  simpa only [Append.append_assoc, -eq_self, -iff_self] using
    PreparedSwitchedRefinements.boundaryState_parents curve source tour.joined.data

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The total closed tour realizes the raw connector cycle with its original boundary owners.

The return-box and traced-fallback branches both preserve the exact connector and owner-boundary paths required by the
realization witness. -/
theorem total_realizesRaw {leftAmbient rightAmbient connectorAmbient : Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient) (owner : Owner (curve.polynomial.eval leftState.box.anchor)) :
    PreparedCycleData.RealizesRaw (.finiteCut (total leftState rightState connector within owner).joined.data)
      (BranchCutLifts.doubleLiftWithBoundaryOwners leftState rightState connector) := by
  unfold total
  dsimp only
  split
  · rename_i closed accepted
    rw [checkReturn_joined _ closed accepted]
    exact .finiteCut _ rfl rfl
  · exact .finiteCut _ rfl rfl

open Purelib.Curves.Hyperelliptic.Branches in
/-- The prepared branch-connector tour realizes the raw cycle at the same original branch indices and refinement stage.
-/
theorem ofConnectorAt_realizesRaw (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree) (left right : BranchIsolation.Data.Index branches)
    (refinement : Nat) :
    PreparedCycleData.RealizesRaw (.finiteCut (ofConnectorAt branches degreeGtOne left right refinement).joined.data)
      (BranchCutLifts.doubleLiftWithBoundaryOwners
        (Cuts.refinedState branches degreeGtOne left refinement)
        (Cuts.refinedState branches degreeGtOne right refinement)
        (Cuts.connectorAt branches degreeGtOne left right refinement)) :=
  total_realizesRaw _ _ _ _ _

end Purelib.Riemann.Integration.PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath

namespace Purelib.Riemann.Integration.PreparedOwnerClosedSchedules.PreparedRefinementPrograms

open Purelib.Data.List

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Topology.PreparedCycleModels
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (StandardSwitchedClosedSchedule)

section
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Riemann.Readings in
/-- Prepare the owner-closed A-cycle seed from the supplied branch-isolation data.

The original finite cycle index selects its two configured branch owners and their stage-zero connector; no replacement
branch family is introduced. -/
@[expose] def ownerClosedASeedOfData {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin genus) : ClosedBoundaryDoublePath curve :=
  PreparedBoundaryClosure.ClosedBoundaryDoublePath.ofConnectorAt (BranchConfiguration.configurationOfData curve
    branches).branches
    (BranchCutLifts.degreeGtOne_of_cycleIndex curve index)
    (BranchConfiguration.basisPairLeftIndexOfData curve branches index)
    (BranchConfiguration.basisPairRightIndexOfData curve branches index) 0

open Purelib.Riemann.Integration in
open Purelib.Riemann.Periods in
/-- Build the standard switched A schedule from the exact retained branch data and cycle index. -/
@[expose] def ownerClosedAScheduleOfData {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin genus) : StandardSwitchedClosedSchedule curve :=
  PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath.schedule (ownerClosedASeedOfData curve branches index)
    (PeriodMatrix.standardDifferential index)

open Purelib.Riemann.Integration in
/-- The retained A schedule explicitly realizes the same branch-data family's raw stage-zero A cycle. -/
theorem ownerClosedAScheduleOfData_realizesRaw_zero {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin genus) :
    PreparedCycleData.RealizesRaw (ownerClosedAScheduleOfData curve branches index).prepared
      (((BranchCutLifts.familyOfData curve branches).symplecticCycles.aCycle index).liftedPath 0) := by
  rw [BranchCutLifts.canonicalACycle_liftedPath_ofData]
  exact PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath.ofConnectorAt_realizesRaw
    (BranchConfiguration.configurationOfData curve branches).branches
    (BranchCutLifts.degreeGtOne_of_cycleIndex curve index)
    (BranchConfiguration.basisPairLeftIndexOfData curve branches index)
    (BranchConfiguration.basisPairRightIndexOfData curve branches index) 0

/-- Prepare the owner-closed A seed using the curve's canonical branch-isolation data. -/
@[expose] def ownerClosedASeed {genus : Nat} (curve : Basic.HyperellipticCurve genus) (index : Fin genus) :
    ClosedBoundaryDoublePath curve :=
  ownerClosedASeedOfData curve (BranchIsolation.data curve) index

/-- Build the owner-closed standard A schedule using the curve's canonical branch data. -/
@[expose] def ownerClosedASchedule {genus : Nat} (curve : Basic.HyperellipticCurve genus) (index : Fin genus) :
    StandardSwitchedClosedSchedule curve :=
  ownerClosedAScheduleOfData curve (BranchIsolation.data curve) index

/-- The canonical owner-closed A schedule realizes the same original stage-zero A cycle. -/
theorem ownerClosedASchedule_realizesRaw_zero {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (index : Fin genus) :
    PreparedCycleData.RealizesRaw (ownerClosedASchedule curve index).prepared
      (((BranchCutLifts.family curve).symplecticCycles.aCycle index).liftedPath 0) :=
  ownerClosedAScheduleOfData_realizesRaw_zero curve (BranchIsolation.data curve) index

end

end Purelib.Riemann.Integration.PreparedOwnerClosedSchedules.PreparedRefinementPrograms
