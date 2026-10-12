module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Branches.BranchCutRepresentatives
public import Purelib.Riemann.Integration.PreparedOwnerClosedSchedules
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Gaussian.Basic

public section

/-!
# Paired owner-closed A and reference-bridge tours

Both tours start with the same retained owner.  The bridge includes the two
actual branch-boundary loops, unlike the older connector-only B path.  The
constructors prove root return and exact raw geometry, not a geometric
intersection or cut-surface theorem.
-/

namespace Purelib.Riemann.Integration.PreparedOwnerClosedBridges

open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)
open Purelib.Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath (total total_initialName total_base)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Topology.PreparedCycleModels (PreparedCycleData)

set_option genInjectivity false in
/-- An A tour and reference-bridge tour with the same retained root name and basepoint.

Both closed boundary tours keep their original owners and certificates; exact equalities identify their initial names
and base coordinates. -/
structure OwnerClosedCyclePair {genus : Nat} (curve : Basic.HyperellipticCurve genus) where
  /-- The retained closed A boundary tour. -/ aTour : ClosedBoundaryDoublePath curve
  /-- The retained closed reference-bridge boundary tour. -/ bTour : ClosedBoundaryDoublePath curve
  /-- The root name shared by the two original initial owners. -/ root : Name.Basic.Named
  /-- The A tour's original initial root name equals the retained shared name. -/ aRoot_eq : ownerName
    aTour.joined.data.forwardOwner = root
  /-- The B tour's original initial root name equals the retained shared name. -/ bRoot_eq : ownerName
    bTour.joined.data.forwardOwner = root
  /-- Both original tours start at the same retained base coordinate. -/ base_eq :
    aTour.joined.data.leftState.box.anchor = bTour.joined.data.leftState.box.anchor

constructive_injectivity OwnerClosedCyclePair

namespace OwnerClosedCyclePair

open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Readings
open Purelib.RootIsolation
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Riemann.Topology
open Purelib.Riemann.Integration
open Purelib.Geometry.Path.Gaussian

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

/-- Prepare both owner-closed tours from the supplied connectors and shared initial root owner.

The A connector reaches the right branch state and the B connector reaches the reference state. Their exact common left
state supplies the basepoint and root-name identities. -/
@[expose] def ofGeometry {leftAmbient rightAmbient referenceAmbient aAmbient bAmbient : Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (referenceState : State.WindingOne.Basic.WindingOneState curve.polynomial referenceAmbient)
    (aConnector : Polynomial.Geometry.ClearPath curve.polynomial aAmbient leftState.box.anchor rightState.box.anchor)
    (aWithin : aConnector.WithinAmbient)
    (bConnector : Polynomial.Geometry.ClearPath curve.polynomial bAmbient leftState.box.anchor
      referenceState.box.anchor)
    (bWithin : bConnector.WithinAmbient)
    (owner : Owner (curve.polynomial.eval leftState.box.anchor)) : OwnerClosedCyclePair curve where
  aTour := PreparedBoundaryClosure.ClosedBoundaryDoublePath.total leftState rightState aConnector aWithin owner
  bTour := PreparedBoundaryClosure.ClosedBoundaryDoublePath.total leftState referenceState bConnector bWithin owner
  root := ownerName owner
  aRoot_eq := PreparedBoundaryClosure.ClosedBoundaryDoublePath.total_initialName leftState rightState aConnector aWithin
    owner
  bRoot_eq := PreparedBoundaryClosure.ClosedBoundaryDoublePath.total_initialName leftState referenceState bConnector
    bWithin owner
  base_eq := (PreparedBoundaryClosure.ClosedBoundaryDoublePath.total_base (curve := curve) leftState rightState
    aConnector aWithin owner).trans
    (PreparedBoundaryClosure.ClosedBoundaryDoublePath.total_base (curve := curve) leftState referenceState bConnector
      bWithin owner).symm

/-- Prepare the paired tours from the original branch-isolation data and finite cycle index.

The configured basis pair and final reference cut retain their stage-zero states and connectors; one independent initial
owner is shared by both tours. -/
@[expose] def ofData (curve : Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve) (index : Fin
  genus) :
    OwnerClosedCyclePair curve :=
  let configured := (BranchConfiguration.configurationOfData curve branches).branches
  let higher := BranchCutLifts.degreeGtOne_of_cycleIndex curve index
  let left := BranchConfiguration.basisPairLeftIndexOfData curve branches index
  let right := BranchConfiguration.basisPairRightIndexOfData curve branches index
  let reference := BranchCutRepresentatives.BranchConfiguration.pairLeftIndexOfData curve branches (Fin.last genus)
  let leftState := Cuts.refinedState configured higher left 0
  let rightState := Cuts.refinedState configured higher right 0
  let referenceState := Cuts.refinedState configured higher reference 0
  let aConnector := Cuts.connectorAt configured higher left right 0
  let bConnector := Cuts.connectorAt configured higher left reference 0
  let owner := SquareRootContinuationChain.Owner.independent
    (Cuts.connectorAt_start_eval_ne_zero configured higher left right 0) 0
  ofGeometry leftState rightState referenceState aConnector
    (Cuts.connectorAt_withinAmbient configured higher left right 0)
    bConnector (Cuts.connectorAt_withinAmbient configured higher left reference 0) owner

/-- The A tour is exactly the existing owner-closed seed from the same branch data and index. -/
theorem ofData_aTour (curve : Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve) (index : Fin
  genus) :
    (ofData curve branches index).aTour = PreparedOwnerClosedSchedules.PreparedRefinementPrograms.ownerClosedASeedOfData
      curve branches index := rfl

/-- The raw lifted reference-bridge cycle at the supplied branch-data refinement stage. -/
@[expose] def rawBridgeOfData (curve : Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve) (index :
  Fin genus)
    (refinement : Nat) : Lifted.Closed.ClosedLiftedPath 2 :=
  let configured := (BranchConfiguration.configurationOfData curve branches).branches
  let higher := BranchCutLifts.degreeGtOne_of_cycleIndex curve index
  let cuts := Cuts.systemOfData curve branches
  let left := BranchCutLifts.Geometry.representative (cuts.cutAt (BranchCutLifts.basisCutIndex index))
  let reference := BranchCutLifts.Geometry.representative (cuts.cutAt (BranchCutLifts.referenceCutIndex genus))
  BranchCutLifts.doubleLiftWithBoundaryOwners
    (Cuts.refinedState configured higher left refinement) (Cuts.refinedState configured higher reference refinement)
    (Cuts.connectorAt configured higher left reference refinement)

/-- The retained B tour explicitly realizes the original reference-bridge cycle at stage zero. -/
theorem ofData_bTour_realizesRaw (curve : Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (index : Fin genus) :
    PreparedCycleData.RealizesRaw (.finiteCut (ofData curve branches index).bTour.joined.data)
      (rawBridgeOfData curve branches index 0) := by
  dsimp only [rawBridgeOfData]
  rw [BranchCutRepresentatives.BranchCutLifts.standardCutRepresentative,
    BranchCutRepresentatives.BranchCutLifts.standardCutRepresentative]
  simp only [BranchCutLifts.basisCutIndex, BranchCutLifts.referenceCutIndex]
  exact PreparedOwnerClosedSchedules.ClosedBoundaryDoublePath.total_realizesRaw _ _ _ _ _

/-- Prepare the paired owner-closed tours from the curve's canonical branch-isolation data. -/
@[expose] def ofCurve (curve : Basic.HyperellipticCurve genus) (index : Fin genus) : OwnerClosedCyclePair curve :=
  ofData curve (BranchIsolation.data curve) index

end OwnerClosedCyclePair

end Purelib.Riemann.Integration.PreparedOwnerClosedBridges
