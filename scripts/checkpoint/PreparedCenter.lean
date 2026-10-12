module

meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.System.FilePath

import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import scripts.checkpoint.RootRefinement
import scripts.checkpoint.RootState
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay
import Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSelectionReplay.Trace
public import Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSourceRefinementReplay.Restoration
public import Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSourceRefinementReplay.Selection
public import Purelib.Curves.Hyperelliptic.Integration.Preparation.Roots.PreparedRootSafeReplay.Restoration
public import Purelib.Curves.Hyperelliptic.Integration.Preparation.Roots.PreparedRootSafeReplay.Selection
public import Purelib.Curves.Hyperelliptic.Integration.Surface.PreparedCycleReplay.Readiness
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Riemann.Transport.PreparedSourceRefinementReplay

import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
import Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedTrackReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
public import scripts.checkpoint.Center
public import scripts.checkpoint.PreparedBank
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Transport.PreparedDirectRefinementReplay
import Purelib.Riemann.Transport.PreparedDeferredRecipeReplay
import Purelib.Riemann.Transport.PreparedUniformRefinementReplay
import Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy
public import Purelib.Riemann.RootContinuation.PreparedRootSafeReplay
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.CheckedDirectGeometry
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.PreparedCycleReplay
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Transport.CheckedDirectGeometryReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedOwnerTransportReplay
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import scripts.checkpoint.Integration

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib.Approximation

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Path.Gaussian

open Purelib.RootIsolation

open Purelib.Polynomial

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.Topology

open Purelib.Riemann.Paths

open Purelib.Riemann.Transport

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.SquareRoot.Replay

open Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedMeshReplay (finish)

section
open Purelib.Data (Json)
open scoped Purelib.Data.String
open Purelib.Data.Json (toJson)

public section

/-!
Disk-backed centring of the original prepared bank spines.  Each callback
receives the complete original-source equation, not just matching numbers.
The explicit stored-spine eliminators retain the owners already computed by
preparation instead of rebuilding their canonical indices during execution.
-/

namespace PreparedCenterCheckpoint

variable {Result : Type}

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open PreparedDirectDyadicRefinements (CenteredPathChain)
open QuadraticTrackReplay (Ready)
open PreparedCycleReplay
open IntegrationCheckpoint

variable {genus : Nat} (curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus) (source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus)

/-- Restore the centered data of the original stored subdivision spine.

Visit its retained edges directly, check each center and pass the exact canonical-data equation to the continuation
without rebuilding the subdivision. -/
@[expose] def withSubdivision {ambient : Rational.Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) (index : Nat)
    {left : PreparedSheetContinuation.Endpoint}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (spine : PreparedSheetContinuation.Subdivision segment within left owner) :
    Ready owner →
    ((value : CenteredPathChain.PreparedSegmentCenteredData curve source sheet
        (segment.pointAt left.parameter) (segment.pointAt spine.endpoint.parameter)) →
      value = CenteredPathChain.dataOfCanonicalSubdivision curve source segment within sheet spine → m Result) →
    m Result :=
  PreparedSheetContinuation.Subdivision.casesOn
    (motive := fun left owner spine => Ready owner →
      ((value : CenteredPathChain.PreparedSegmentCenteredData curve source sheet
          (segment.pointAt left.parameter) (segment.pointAt spine.endpoint.parameter)) →
        value = CenteredPathChain.dataOfCanonicalSubdivision curve source segment within sheet spine → m Result) →
      m Result) spine
    (fun _ _ _ use => use { parents := [], chain := .nil _ } rfl)
    (fun current owner request cached ordered small remaining ready use => do
      let edge := PreparedSubdivisionModelCore.edgeOfStep curve source segment within
        current owner request cached ordered small sheet
      let edgeReady := QuadraticTrackReplay.baseQuery edge
        (QuadraticTrackReplay.cached segment current owner request ready cached)
      let restored ← CenterCheckpoint.run edge edgeReady (pure .checkedFirstOnly) control ((Purelib.System.FilePath.join
        directory (System.FilePath.mk (s!"edge-{index}"))))
      match restored with
      | .error failure =>
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("stopped-center.json"))))
            (index, failure.report edge)
          throw (IO.userError s!"center replay stopped at edge {index}; typed failure and trace retained")
      | .ok center =>
          withSubdivision segment within sheet control directory (index + 1) remaining
            (QuadraticTrackReplay.advance segment current owner request ready within small)
            fun tail tailEqual => do
              let centered : PreparedSubdivisionModelCore.CenteredEdge curve source := ⟨edge, center.val⟩
              use { parents := centered :: tail.parents, chain := .cons centered tail.chain } (by
                rw [CenteredPathChain.dataOfCanonicalSubdivision_next, ← tailEqual]
                exact congrArg (fun value : PreparedConstantModels.PreparedEdge.CenterState edge =>
                  ({ parents := ⟨edge, value⟩ :: tail.parents
                     chain := .cons ⟨edge, value⟩ tail.chain } :
                    CenteredPathChain.PreparedSegmentCenteredData curve source sheet
                      (segment.pointAt current.parameter) (segment.pointAt remaining.endpoint.parameter)))
                  center.property))
termination_by structural spine

/-- Restore one complete segment's original centered data with its exact endpoint transports. -/
@[expose] def withSegment {ambient : Rational.Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedClearPathModels.CompleteSegment segment within owner)
    (ready : Ready owner) (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : (value : CenteredPathChain.PreparedSegmentCenteredData curve source sheet start finish) →
      value = CenteredPathChain.dataOfCompleteSegment curve source sheet prepared → m Result) : m Result :=
  withSubdivision curve source segment within sheet control directory 0 prepared.subdivision
    (PreparedTrackReplay.ownerAtStart segment owner ready) fun data equal =>
      let startEqual := congrArg
        (fun coordinate : Gaussian =>
          ({ coordinate := coordinate, sheet := sheet } : Lifted.Basic.LiftedPoint 2)) prepared.start_eq
      let finishEqual := congrArg
        (fun coordinate : Gaussian =>
          ({ coordinate := coordinate, sheet := sheet } : Lifted.Basic.LiftedPoint 2)) prepared.finish_eq
      use { parents := data.parents, chain := (data.chain.castStart startEqual).castFinish finishEqual }
        (by cases equal; rfl)

/-- Restore the original centered path by traversing its retained prepared segments.

Pass the exact terminal-owner readiness into the tail and preserve the canonical parent list and chain equation. -/
@[expose] def withPath {ambient : Rational.Box} (sheet : Fin 2)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) (index : Nat)
    {start finish : Gaussian} {path : Purelib.Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (prepared : PreparedClearPathModels.PreparedPath path owner) : Ready owner →
    ((value : CenteredPathChain.PreparedPathCenteredData curve source sheet start finish) →
      value = CenteredPathChain.ofPreparedPath curve source sheet prepared → m Result) → m Result :=
  PreparedClearPathModels.PreparedPath.casesOn
    (motive := fun {start finish} _ owner prepared => Ready owner →
      ((value : CenteredPathChain.PreparedPathCenteredData curve source sheet start finish) →
        value = CenteredPathChain.ofPreparedPath curve source sheet prepared → m Result) → m Result) prepared
    (fun _ _ _ use => use { parents := [], chain := .nil _ } rfl)
    (fun _ _ _ _ head tail ready use =>
      withSegment curve source sheet head ready control ((Purelib.System.FilePath.join directory (System.FilePath.mk
        (s!"segment-{index}")))) fun first firstEqual =>
        withPath sheet control directory (index + 1) tail
          (PreparedTrackReplay.finishOwner head ready) fun rest restEqual =>
            use { parents := first.parents ++ rest.parents, chain := first.chain.append rest.chain }
              (by rw [CenteredPathChain.ofPreparedPath, ← firstEqual, ← restEqual]))
termination_by structural prepared

/-- Restore the centered state of the original cached dyadic bank with its parent-propriety certificate. -/
@[expose] def withBank {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {ambient : Rational.Box} {start finish : Gaussian}
    {path : Purelib.Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth diameter positive path owner)
    (ready : Ready owner) (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : (value : CenteredPathChain.CheckedDyadicCenteredState curve source sheet start finish) →
      value = CenteredPathChain.ofDyadicBank curve source sheet (.certified
        (SquareRoot.Preparation.Bank.Cache.DyadicBank.cache bank)) → m Result) : m Result :=
  let cached := (SquareRoot.Preparation.Bank.Cache.DyadicBank.cache bank)
  withPath curve source sheet control directory 0 cached.prepared ready fun data equal =>
    let value : CenteredPathChain.CheckedDyadicCenteredState curve source sheet start finish :=
      { parents := data.parents
        proper := by
          rw [equal]
          exact CenteredPathChain.ofPreparedPath_allParentsProper_of_allEdgesProper curve source sheet
            cached.prepared cached.prepared_allEdgesProper
        chain := data.chain }
    use value (centeredState_eq_of_parents_eq _ _ (congrArg (fun data => data.parents) equal))

/-- Restore every original bridge or finite-cut cycle part in its retained sheet order. -/
@[expose] def withParts (data : PreparedCycleModels.PreparedCycleData curve) (ready :
  Integration.Surface.PreparedCycleReplay.Readiness.CycleReady curve data)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : (parts : CycleParts curve source) → parts = CycleParts.canonical curve source data → m Result) :
    m Result :=
  match data with
  | .bridge data =>
      withBank curve source 0 data.forwardChecked ready.1 control ((Purelib.System.FilePath.join directory
        (System.FilePath.mk ("forward")))) fun forward forwardEq =>
        withBank curve source 1 data.backwardChecked ready.2 control ((Purelib.System.FilePath.join directory
          (System.FilePath.mk ("backward")))) fun backward backwardEq =>
          use (.bridge data.start data.finish forward backward)
            (by rw [forwardEq, backwardEq]; rfl)
  | .finiteCut data =>
      withBank curve source 0 data.forwardChecked ready.1 control ((Purelib.System.FilePath.join directory
        (System.FilePath.mk ("forward")))) fun forward forwardEq =>
        withBank curve source 0 data.rightBoundaryChecked ready.2.1 control ((Purelib.System.FilePath.join directory
          (System.FilePath.mk ("right")))) fun right rightEq =>
          withBank curve source 1 data.backwardChecked ready.2.2.1 control ((Purelib.System.FilePath.join directory
            (System.FilePath.mk ("backward")))) fun backward backwardEq =>
            withBank curve source 1 data.leftBoundaryChecked ready.2.2.2 control ((Purelib.System.FilePath.join
              directory (System.FilePath.mk ("left")))) fun left leftEq =>
              use (.finiteCut data.leftState.box.anchor data.rightState.box.anchor forward right backward left)
                (by rw [forwardEq, rightEq, backwardEq, leftEq]; rfl)

/-- Reconstruct the original complete compact cycle from persisted samples. The compact allowance is cheap source
geometry, evaluated once and checked against any saved copy; it is not inferred from an observation receipt. -/
@[expose] def withCycle (data : PreparedCycleModels.PreparedCycleData curve) (ready :
  Integration.Surface.PreparedCycleReplay.Readiness.CycleReady curve data)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : CachedCycle curve source data → m Result) : m Result :=
  withParts curve source data ready control directory fun parts equal => do
    let allowance := PreparedSwitchedRefinements.cycleSourceAggregateBound source data
    let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("source-allowance.json")))
    if ← path.pathExists then
      let saved : FractionData ← loadJson path
      let decoded ← checked "source allowance" (decodeFraction saved)
      unless decoded == allowance do
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-allowance.json")))) (saved,
          fractionData allowance)
        throw (IO.userError "saved source allowance differs; exact operands retained")
    else
      if control.savedOnly then throw (IO.userError "missing source allowance; generation forbidden")
      saveJson path (fractionData allowance)
    use
      { parts := parts
        parts_eq := (congrArg CycleParts.state equal).trans (CycleParts.canonical_state curve source data)
        sourceAllowance := allowance
        sourceAllowance_eq := rfl }

end PreparedCenterCheckpoint

namespace PreparedRefinementCheckpoint

variable {Result : Type}

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open PreparedSubdivisionModelCore (CenteredEdge)
open PreparedDirectDyadicRefinements (CheckedDirectMeshes)
open PreparedDyadicRefinements (AllParentsProper)
open PreparedSheetContinuation (Coordinate)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- Replay direct geometry for each original centered parent in order.

Retain the accepted prefix when a later transport is unresolved, and distinguish certified geometry misses from pending
replay. -/
@[expose] def withMeshes (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    (control : RootRefinementCheckpoint.Control) :
    (parents : List (CenteredEdge curve source)) → (proper : AllParentsProper parents) →
    (index : Nat) → (directory : System.FilePath) →
    (Except (Integration.Preparation.Replay.PreparedMeshReplay.Pending depth diameter positive parents proper)
      (Integration.Preparation.Replay.PreparedMeshReplay.Checked depth diameter positive parents proper) → m Result) →
    m Result
  | [], _, _, _, use => use (.ok ⟨.ok .nil, rfl⟩)
  | parent :: remaining, proper, index, directory, use => do
      let inputs := SquareRoot.Replay.PreparedSourceReplay.Inputs.capture parent.edge.segment diameter
      match ← DirectMeshCheckpoint.run parent.edge proper.1 diameter positive inputs control depth
          parent.edge.left parent.edge.request.endpoint le_rfl le_rfl proper.1 ((Purelib.System.FilePath.join directory
            (System.FilePath.mk (s!"parent-{index}")))) with
      | .error pending => use (.error (.head pending))
      | .ok checked =>
          let finished := CheckedDirectGeometryReplay.finish parent.edge proper.1 diameter positive depth
            parent.edge.left parent.edge.request.endpoint le_rfl le_rfl proper.1 checked
          match found : finished.val with
          | .error failure =>
              use (.ok (Integration.Preparation.Replay.PreparedMeshReplay.failedHead depth diameter positive proper
                failure (finished.property.trans found)))
          | .ok accepted =>
              withMeshes depth diameter positive control remaining proper.2 (index + 1) directory fun result =>
                match result with
                | .error pending => use (.error (.tail accepted (finished.property.trans found) pending))
                | .ok tail => use (.ok (Integration.Preparation.Replay.PreparedMeshReplay.acceptedHead depth diameter
                  positive proper accepted
                    (finished.property.trans found) tail))

open PreparedDirectDyadicRefinements (CheckedSelection MeshAllowanceChecks)

/-- Replay the bounded first-success mesh and allowance search.

Geometry misses increase depth; allowance misses increase depth and root precision; unresolved transport retains the
exact pending search state. -/
@[expose] def withSearch (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (control :
      RootRefinementCheckpoint.Control)
    (directory : System.FilePath) : (fuel depth bits : Nat) →
    (Except (Integration.Preparation.Replay.PreparedSelectionReplay.Trace.PendingSearch parents proper targets target
      fuel depth bits)
      (Integration.Preparation.Replay.PreparedSelectionReplay.Trace.Search parents proper targets target fuel depth
        bits) → m Result) → m Result
  | 0, _, _, use => use (.ok .exhausted)
  | fuel + 1, depth, bits, use =>
      withMeshes depth (Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits)
        (Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt_positive bits) control parents proper 0
        ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"depth-{depth}-bits-{bits}")))) fun result =>
        match result with
        | .error pending => use (.error (.current pending))
        | .ok checked =>
            let finished := finish depth (Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt bits)
              (Integration.Preparation.Replay.PreparedSelectionReplay.Trace.diameterAt_positive bits) parents proper
              checked
            match observed : finished.val with
            | .error failure =>
                withSearch parents proper targets target control directory fuel (depth + 1) bits fun result =>
                  match result with
                  | .error pending => use (.error (.geometry failure pending))
                  | .ok next => use (.ok (.geometry failure next))
            | .ok meshes =>
                match allowanceEq : MeshAllowanceChecks.attempt meshes target targets with
                | .error failure =>
                    withSearch parents proper targets target control directory fuel (depth + 1) (bits + 1) fun result =>
                      match result with
                      | .error pending => use (.error (.allowance meshes (finished.property.trans observed) failure
                        pending))
                      | .ok next => use (.ok (.allowance meshes (finished.property.trans observed) failure next))
                | .ok allowances => use (.ok (.accepted meshes (finished.property.trans observed) allowances
                  allowanceEq))
open PreparedDirectRefinementReplay
open PreparedSheetContinuation (Endpoint)

/-- Select the replay certificate determined by the retained first-success history.

An accepted search or uniform fallback retains equality with the original
selection. Each finite miss preserves its attempted data in the corresponding
replay inconclusivity certificate. -/
@[expose] def withSelected (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : Except (Integration.Preparation.Roots.PreparedRootSafeReplay.Selection.PendingSelection parents proper
      targets target)
      {selected : CheckedSelection parents targets target // selected =
        (PreparedRootSafeAccuracy.RootSafeAccuracy.select parents proper targets target positive).selected} →
      m Result) : m Result :=
  withSearch parents proper targets target control ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("search")))) 8
    (PreparedDirectDyadicRefinements.commonAccuracyDepth target parents)
    (PreparedDirectDyadicRefinements.proposedRootBits parents.length
      (PreparedDirectDyadicRefinements.familyForecast parents targets) target) fun result =>
    match result with
    | .error pending => use (.error (.search pending))
    | .ok trace =>
        match found : trace.value with
        | some selected => use (.ok ⟨selected,
          Integration.Preparation.Roots.PreparedRootSafeReplay.Selection.selected_eq parents proper targets target
          positive trace selected found⟩)
        | none =>
            let plan := PreparedUniformRefinementReplay.Plan.build parents targets target positive
            withMeshes plan.depth plan.diameter plan.positive control parents proper 0 ((Purelib.System.FilePath.join
              directory (System.FilePath.mk ("uniform")))) fun result =>
              match result with
              | .error pending => use (.error (.uniformPreparation trace found plan pending))
              | .ok checked =>
                  let finished := finish plan.depth plan.diameter plan.positive parents proper checked
                  match finished.val with
                  | .error failure => use (.error (.uniformGeometry trace found plan failure))
                  | .ok meshes => use (.ok ⟨PreparedUniformRefinementReplay.selected parents proper targets target
                    positive plan meshes,
                      (PreparedUniformRefinementReplay.selected_eq parents proper targets target positive plan
                        meshes).trans
                        (Integration.Preparation.Roots.PreparedRootSafeReplay.Selection.fallback_eq parents proper
                          targets target positive trace found).symm⟩)

set_option genInjectivity false in
/-- The unresolved leaf of a retained direct mesh with its accepted left-prefix centers. -/
inductive PendingCenters {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} {parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential}
    {diameter : Coordinate} : {depth : Nat} → {left right : Endpoint} →
    CheckedDirectGeometry.Mesh parent diameter depth left right → Type
  /-- The exact leaf center check is invalid or inconclusive. -/ | leaf {left right : Endpoint}
      {leaf : CheckedDirectGeometry.Leaf parent left right diameter}
      {proper : left.parameter < right.parameter}
      (failure : CenterCheckpoint.RunFailure leaf.edge) : PendingCenters (.leaf leaf proper)
  /-- Center restoration stopped in the left child mesh. -/ | first {depth : Nat} {left right : Endpoint}
      {head : CheckedDirectGeometry.Mesh parent diameter depth left (CheckedDirectGeometry.midpoint left right)}
      {tail : CheckedDirectGeometry.Mesh parent diameter depth (CheckedDirectGeometry.midpoint left right) right}
      (pending : PendingCenters head) : PendingCenters (.split head tail)
  /-- The left child centers are retained while the right child remains unresolved. -/ | second {depth : Nat} {left
    right : Endpoint}
      {head : CheckedDirectGeometry.Mesh parent diameter depth left (CheckedDirectGeometry.midpoint left right)}
      {tail : CheckedDirectGeometry.Mesh parent diameter depth (CheckedDirectGeometry.midpoint left right) right}
      (accepted : Centers head) (pending : PendingCenters tail) : PendingCenters (.split head tail)

constructive_injectivity PendingCenters

/-- Serialize the missing original-owner construction equation or retained transport failure. -/
@[expose] public def historyIssueReport : PreparedDeferredRecipeReplay.Issue → Json
  | .inherited (parameter := parameter) owner => Json.mkObj
      [("kind", toJson "original owner has no retained constructor equation in this finite attempt"),
       ("parameter", toJson (IntegrationCheckpoint.gaussianData parameter)),
       ("state", toJson (RootStateCheckpoint.capture owner.track.initial)),
       ("classificationBudget", toJson (0 : Nat))]
  | .transport _ _ _ failure => PreparedBankCheckpoint.transportReport failure

/-- Resolve the retained original history only when a checked Newton attempt misses. Stationary queries can use an
earlier moving query's source equation. -/
@[expose] public def leafFallbackPlan {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} {parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential}
    {diameter : Coordinate} {left right : Endpoint}
    (history : PreparedDeferredRecipeReplay.History parent.cached.preparedOwner)
    (leaf : CheckedDirectGeometry.Leaf parent left right diameter) (directory : System.FilePath) :
    m (SquareRoot.Replay.QuadraticFallbackReplay.Plan (leaf.edge.directQueryOwner 0 leaf.edge.baseInside).track) := do
  match (PreparedDeferredRecipeReplay.leafHistory history leaf).get with
  | .error issue =>
      IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("fallback-provenance-inconclusive.json")))) (historyIssueReport issue)
      return .checkedFirstOnly
  | .ok checked =>
      return SquareRoot.Replay.QuadraticFallbackReplay.Plan.ofDeferred _
        (QuadraticSampleReplay.matches_baseQuery leaf.edge .deferred checked.down)

/-- Restore all centers of the original selected mesh using its exact retained owner history.

The deferred fallback is resolved only when needed, and an unresolved leaf retains previously accepted child centers. -/
@[expose] def runCenters {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} {parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential}
    {diameter : Coordinate} (ready : QuadraticTrackReplay.Ready parent.cached.preparedOwner)
    (history : PreparedDeferredRecipeReplay.History parent.cached.preparedOwner)
    (control : RootRefinementCheckpoint.Control) :
    {depth : Nat} → {left right : Endpoint} →
    (mesh : CheckedDirectGeometry.Mesh parent diameter depth left right) →
    (directory : System.FilePath) → m (Except (PendingCenters mesh) (Centers mesh))
  | _, _, _, .leaf leaf proper, directory => do
      match ← CenterCheckpoint.run leaf.edge
          (QuadraticTrackReplay.baseQuery leaf.edge (leafReady ready leaf))
          (leafFallbackPlan history leaf directory) control directory with
      | .error failure => return .error (.leaf failure)
      | .ok center => return .ok (.leaf leaf proper center.val center.property)
  | _, _, _, .split head tail, directory => do
      match ← runCenters ready history control head ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("left")))) with
      | .error pending => return .error (.first pending)
      | .ok first =>
          match ← runCenters ready history control tail ((Purelib.System.FilePath.join directory (System.FilePath.mk
            ("right")))) with
          | .error pending => return .error (.second first pending)
          | .ok last => return .ok (.split first last)

set_option genInjectivity false in
/-- An unresolved center bank indexed by its original selected meshes and accepted parent prefix. -/
inductive PendingBankCenters {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus} {diameter : Coordinate} {depth : Nat} :
    {parents : List (CenteredEdge curve source)} → CheckedDirectMeshes depth diameter parents → Type 2
  /-- The first parent mesh still has unresolved centers. -/ | head {parent : CenteredEdge curve source} {remaining :
    List (CenteredEdge curve source)}
      {mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth parent.edge.left parent.edge.request.endpoint}
      {meshes : CheckedDirectMeshes depth diameter remaining}
      (pending : PendingCenters mesh) : PendingBankCenters (.cons mesh meshes)
  /-- The first parent's centers are retained and the remaining bank is unresolved. -/ | tail {parent : CenteredEdge
    curve source} {remaining : List (CenteredEdge curve source)}
      {mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth parent.edge.left parent.edge.request.endpoint}
      {meshes : CheckedDirectMeshes depth diameter remaining}
      (accepted : Centers mesh) (pending : PendingBankCenters meshes) : PendingBankCenters (.cons mesh meshes)

constructive_injectivity PendingBankCenters

/-- Restore selected mesh centers in parent order using their original readiness and history witnesses. -/
@[expose] def withBankCenters {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus} {diameter : Coordinate} {depth : Nat}
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    {parents : List (CenteredEdge curve source)} →
    (meshes : CheckedDirectMeshes depth diameter parents) → AllReady parents →
    PreparedDeferredRecipeReplay.Histories parents → Nat →
    (Except (PendingBankCenters meshes) (BankCenters meshes) → m Result) → m Result
  | [], .nil, _, _, _, use => use (.ok .nil)
  | _ :: _, .cons mesh meshes, ready, histories, index, use => do
      match ← runCenters ready.1 histories.1 control mesh ((Purelib.System.FilePath.join directory (System.FilePath.mk
        (s!"parent-{index}")))) with
      | .error pending => use (.error (.head pending))
      | .ok first =>
          withBankCenters control directory meshes ready.2 histories.2 (index + 1) fun result =>
            match result with
            | .error pending => use (.error (.tail first pending))
            | .ok remaining => use (.ok (.cons first remaining))

set_option genInjectivity false in
/-- An unresolved root-closed refinement with its original selection or selected-mesh center obligation. -/
inductive PendingStep {root : Gaussian.Name.Basic.Named}
    (current : PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState curve source root)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target) : Type 2
  /-- The original root-closed mesh selection remains unresolved. -/ | selection (pending :
    Integration.Preparation.Roots.PreparedRootSafeReplay.Selection.PendingSelection current.state.parents
    current.state.proper targets target)
  /-- The original selection is retained, but its checked center bank is incomplete. -/ | centers (selected :
    CheckedSelection current.state.parents targets target)
      (equal : selected = (PreparedRootSafeAccuracy.RootSafeAccuracy.select
        current.state.parents current.state.proper targets target positive).selected)
      (pending : PendingBankCenters selected.meshes)

constructive_injectivity PendingStep

/-- Restore one original root-closed refinement with selection, center and readiness equations.

Retain construction histories for the resulting parent blocks; return typed pending evidence if selection or centering
cannot be completed. -/
@[expose] def withStep {root : Gaussian.Name.Basic.Named}
    (current : PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState curve source root)
    (ready : AllReady current.state.parents)
    (histories : PreparedDeferredRecipeReplay.Histories current.state.parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : Except (PendingStep current targets target positive)
      (Integration.Preparation.Roots.PreparedRootSafeReplay.Restoration.RestoredStep current targets target positive) →
        m Result) : m Result :=
  withSelected current.state.parents current.state.proper targets target positive control directory fun result =>
    match result with
    | .error pending => use (.error (.selection pending))
    | .ok selected =>
        withBankCenters control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("centers"))))
          selected.val.meshes ready histories 0 fun result =>
          match result with
          | .error pending => use (.error (.centers selected.val selected.property pending))
          | .ok centers => use (.ok
              ⟨PreparedRootSafeReplay.step current targets target positive selected.val selected.property centers,
               PreparedRootSafeReplay.step_eq current targets target positive selected.val selected.property centers,
               PreparedRootSafeReplay.step_ready current ready targets target positive selected.val selected.property
                 centers,
               by
                 rw [PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState.Step.parents_eq]
                 exact PreparedDeferredRecipeReplay.Histories.blocks selected.val.meshes centers histories⟩)

/-- Serialize an unresolved direct mesh, retaining its transport failure and accepted left-child prefix. -/
@[expose] public def meshPendingReport {parent : PreparedSubdivisionModelCore.PreparedEdge curve source}
    {proper : parent.left.parameter < parent.request.endpoint.parameter}
    {diameter : Coordinate} {positive : 0 < diameter} :
    {depth : Nat} → {left right : Endpoint} → {lower upper localProper : _} →
    CheckedDirectGeometryReplay.Pending parent proper diameter positive depth left right lower upper localProper → Json
  | _, _, _, _, _, _, .transport failure _ => PreparedBankCheckpoint.transportReport failure
  | _, _, _, _, _, _, .first pending => Json.mkObj
      [("unresolvedChild", toJson "left"), ("pending", meshPendingReport pending)]
  | _, _, _, _, _, _, .second _ _ pending => Json.mkObj
      [("acceptedLeftChild", toJson true), ("unresolvedChild", toJson "right"),
       ("pending", meshPendingReport pending)]

/-- Serialize an unresolved parent mesh bank with its accepted parent prefix. -/
@[expose] public def pendingReport {depth : Nat} {diameter : Coordinate} {positive : 0 < diameter} :
    {parents : List (CenteredEdge curve source)} → {proper : AllParentsProper parents} →
    Integration.Preparation.Replay.PreparedMeshReplay.Pending depth diameter positive parents proper → Json
  | _, _, .head pending => Json.mkObj
      [("unresolvedParent", toJson (0 : Nat)), ("pending", meshPendingReport pending)]
  | _, _, .tail _ _ pending => Json.mkObj
      [("acceptedHeadParent", toJson true), ("remaining", pendingReport pending)]

/-- Serialize the exact depth, diameter and completed prefix of a certified finite mesh miss. -/
@[expose] public def geometryReport {depth : Nat} {diameter : Coordinate} {positive : 0 < diameter}
    {parents : List (CenteredEdge curve source)} {proper : AllParentsProper parents}
    (failure : CheckedDirectMeshes.Inconclusive depth diameter positive parents proper) : Json :=
  Json.mkObj
    [("kind", toJson "certified finite mesh miss"),
     ("depth", toJson failure.attemptedDepth),
     ("diameter", toJson (IntegrationCheckpoint.fractionData failure.requestedDiameter)),
     ("parentCount", toJson failure.parentCount),
     ("completedParents", toJson failure.completedParents),
     ("leafEvidence", toJson "exact checked node requests and mesh-outcome.json under this attempt")]

/-- Serialize the first excessive differential allowance and its accepted and unattempted differential lists. -/
@[expose] public def allowanceFailureReport {depth : Nat} {diameter : Coordinate}
    {parents : List (CenteredEdge curve source)} {meshes : CheckedDirectMeshes depth diameter parents}
    {target : Coordinate} : {targets : List (Differentials.Basic.Differential genus)} →
    MeshAllowanceChecks.Failure meshes target targets → Json
  | _, .excessive differential remaining value _ _ => Json.mkObj
      [("failedDifferential", toJson differential.index.val),
       ("computedAllowance", toJson (IntegrationCheckpoint.fractionData value)),
       ("target", toJson (IntegrationCheckpoint.fractionData target)),
       ("violated", toJson "twice the computed allowance must be at most target"),
       ("unattemptedDifferentials", toJson (remaining.map fun item => item.index.val))]
  | _, .later differential value _ _ failure => Json.mkObj
      [("acceptedDifferential", toJson differential.index.val),
       ("computedAllowance", toJson (IntegrationCheckpoint.fractionData value)),
       ("remaining", allowanceFailureReport failure)]

/-- Serialize the original finite selection trace, including certified misses and its first accepted result or exhausted
budget. -/
@[expose] public def searchReport {parents : List (CenteredEdge curve source)} {proper : AllParentsProper parents}
    {targets : List (Differentials.Basic.Differential genus)} {target : Coordinate} :
    {fuel depth bits : Nat} → Integration.Preparation.Replay.PreparedSelectionReplay.Trace.Search parents proper targets
      target fuel depth bits → Json
  | _, depth, bits, .exhausted => Json.mkObj
      [("reason", toJson "finite search exhausted"), ("remainingBudget", toJson (0 : Nat)),
       ("nextDepth", toJson depth), ("nextRootBits", toJson bits)]
  | _, _, _, .geometry failure next => Json.mkObj
      [("geometryMiss", geometryReport failure), ("next", searchReport next)]
  | _, depth, bits, .allowance _ _ failure next => Json.mkObj
      [("depth", toJson depth), ("rootBits", toJson bits),
       ("allowanceMiss", allowanceFailureReport failure.failure), ("next", searchReport next)]
  | fuel + 1, depth, bits, .accepted _ _ _ _ => Json.mkObj
      [("reason", toJson "accepted original first success"), ("remainingBudget", toJson (fuel + 1)),
       ("depth", toJson depth), ("rootBits", toJson bits)]

/-- Serialize the retained search prefix and current unresolved source transport without treating it as a mesh
rejection. -/
@[expose] public def pendingSearchReport {parents : List (CenteredEdge curve source)} {proper : AllParentsProper
  parents}
    {targets : List (Differentials.Basic.Differential genus)} {target : Coordinate}
    {fuel depth bits : Nat}
    (trace : Integration.Preparation.Replay.PreparedSelectionReplay.Trace.PendingSearch parents proper targets target
      fuel depth bits) : Json :=
  match trace with
  | .current pending => Json.mkObj
      [("reason", toJson "source transport replay is inconclusive; this is not a rejected mesh"),
       ("remainingBudget", toJson fuel), ("depth", toJson depth), ("rootBits", toJson bits),
       ("pending", pendingReport pending)]
  | .geometry failure next => Json.mkObj
      [("geometryMiss", geometryReport failure), ("next", pendingSearchReport next)]
  | .allowance _ _ failure next => Json.mkObj
      [("depth", toJson depth), ("rootBits", toJson bits),
       ("allowanceMiss", allowanceFailureReport failure.failure), ("next", pendingSearchReport next)]

/-- Serialize the bounded search or uniform fallback obligation for the original root-closed selector. -/
@[expose] public def pendingSelectionReport {parents : List (CenteredEdge curve source)} {proper : AllParentsProper
  parents}
    {targets : List (Differentials.Basic.Differential genus)} {target : Coordinate} :
    Integration.Preparation.Roots.PreparedRootSafeReplay.Selection.PendingSelection parents proper targets target → Json
  | .search pending => pendingSearchReport pending
  | .uniformPreparation trace _ plan pending => Json.mkObj
      [("reason", toJson "bounded attempt to restore the original uniform fallback is inconclusive"),
       ("search", searchReport trace), ("uniformDepth", toJson plan.depth),
       ("uniformDiameter", toJson (IntegrationCheckpoint.fractionData plan.diameter)),
       ("pending", pendingReport pending)]
  | .uniformGeometry trace _ plan failure => Json.mkObj
      [("reason", toJson "bounded uniform replay attempt missed; the total fallback is not disproved"),
       ("search", searchReport trace), ("uniformDepth", toJson plan.depth),
       ("uniformDiameter", toJson (IntegrationCheckpoint.fractionData plan.diameter)),
       ("finiteMiss", geometryReport failure)]

/-- Serialize an unresolved center leaf with its retained accepted left-child prefix. -/
@[expose] public def pendingCentersReport {parent : PreparedSubdivisionModelCore.PreparedEdge curve source}
    {diameter : Coordinate} : {depth : Nat} → {left right : Endpoint} →
    {mesh : CheckedDirectGeometry.Mesh parent diameter depth left right} → PendingCenters mesh → Json
  | _, _, _, _, .leaf (leaf := leaf) failure => failure.report leaf.edge
  | _, _, _, _, .first pending => Json.mkObj
      [("unresolvedChild", toJson "left"), ("pending", pendingCentersReport pending)]
  | _, _, _, _, .second _ pending => Json.mkObj
      [("acceptedLeftChild", toJson true), ("unresolvedChild", toJson "right"),
       ("pending", pendingCentersReport pending)]

/-- Serialize an unresolved center bank with its retained accepted parent prefix. -/
@[expose] public def pendingBankCentersReport {diameter : Coordinate} {depth : Nat} :
    {parents : List (CenteredEdge curve source)} → {meshes : CheckedDirectMeshes depth diameter parents} →
    PendingBankCenters meshes → Json
  | _, _, .head pending => Json.mkObj
      [("unresolvedParent", toJson (0 : Nat)), ("pending", pendingCentersReport pending)]
  | _, _, .tail _ pending => Json.mkObj
      [("acceptedHeadParent", toJson true), ("remaining", pendingBankCentersReport pending)]

/-- Serialize the original root-closed selection or its remaining center obligation. -/
@[expose] def PendingStep.report {root : Gaussian.Name.Basic.Named}
    {current : PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState curve source root}
    {targets : List (Differentials.Basic.Differential genus)} {target : Coordinate} {positive : 0 < target} :
    PendingStep current targets target positive → Json
  | .selection pending => pendingSelectionReport pending
  | .centers selected _ pending => Json.mkObj
      [("reason", toJson "selected original geometry retained; coefficient centres unresolved"),
       ("selectedDepth", toJson selected.depth),
       ("selectedDiameter", toJson (IntegrationCheckpoint.fractionData selected.rootDiameter)),
       ("pending", pendingBankCentersReport pending)]

/-! The generated fixtures use the source-only selector, whose original
finite search begins at depth zero. Its choice law differs from the
root-closed selector while sharing the same checkpointed mesh attempts. -/
namespace Source

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (proposedRootBits familyForecast checkedDirectSelection
  uniformSelection accurateDirectRefinement)

/-- Select the replay certificate determined by the retained first-success history.

An accepted search or uniform fallback retains equality with the original
selection. Each finite miss preserves its attempted data in the corresponding
replay inconclusivity certificate. -/
@[expose] def withSelected (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : Except (Integration.Preparation.Replay.PreparedSourceRefinementReplay.Selection.PendingSelection parents
      proper targets target)
      {selected : CheckedSelection parents targets target // selected =
        checkedDirectSelection parents proper targets target positive} →
      m Result) : m Result :=
  withSearch parents proper targets target control ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("search")))) 8
    0
    (PreparedDirectDyadicRefinements.proposedRootBits parents.length
      (PreparedDirectDyadicRefinements.familyForecast parents targets) target) fun result =>
    match result with
    | .error pending => use (.error (.search pending))
    | .ok trace =>
        match found : trace.value with
        | some selected => use (.ok ⟨selected,
          Integration.Preparation.Replay.PreparedSourceRefinementReplay.Selection.selected_eq parents proper targets
          target positive trace selected found⟩)
        | none =>
            let plan := PreparedUniformRefinementReplay.Plan.build parents targets target positive
            withMeshes plan.depth plan.diameter plan.positive control parents proper 0 ((Purelib.System.FilePath.join
              directory (System.FilePath.mk ("uniform")))) fun result =>
              match result with
              | .error pending => use (.error (.uniformPreparation trace found plan pending))
              | .ok checked =>
                  let finished := finish plan.depth plan.diameter plan.positive parents proper checked
                  match finished.val with
                  | .error failure => use (.error (.uniformGeometry trace found plan failure))
                  | .ok meshes => use (.ok ⟨PreparedUniformRefinementReplay.selected parents proper targets target
                    positive plan meshes,
                      (PreparedUniformRefinementReplay.selected_eq parents proper targets target positive plan
                        meshes).trans
                        (Integration.Preparation.Replay.PreparedSourceRefinementReplay.Selection.fallback_eq parents
                          proper targets target positive trace found).symm⟩)

end Source

end PreparedRefinementCheckpoint

namespace Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSourceRefinementReplay.Selection

open PreparedSubdivisionModelCore (CenteredEdge)
open PreparedDyadicRefinements (AllParentsProper)
open PreparedSheetContinuation (Coordinate)
open PreparedRefinementCheckpoint (pendingSearchReport searchReport pendingReport
  geometryReport)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- Serialize the retained source-only selection history and its unresolved original fallback obligation. -/
@[expose] def PendingSelection.report
  {parents : List (CenteredEdge curve source)} {proper : AllParentsProper parents}
    {targets : List (Differentials.Basic.Differential genus)} {target : Coordinate} :
    Integration.Preparation.Replay.PreparedSourceRefinementReplay.Selection.PendingSelection parents proper targets
      target → Json
  | .search pending => pendingSearchReport pending
  | .uniformPreparation trace _ plan pending => Json.mkObj
      [("reason", toJson "bounded attempt to restore the original uniform fallback is inconclusive"),
       ("search", searchReport trace), ("uniformDepth", toJson plan.depth),
       ("uniformDiameter", toJson (IntegrationCheckpoint.fractionData plan.diameter)),
       ("pending", pendingReport pending)]
  | .uniformGeometry trace _ plan failure => Json.mkObj
      [("reason", toJson "bounded uniform replay attempt missed; the total fallback is not disproved"),
       ("search", searchReport trace), ("uniformDepth", toJson plan.depth),
       ("uniformDiameter", toJson (IntegrationCheckpoint.fractionData plan.diameter)),
       ("finiteMiss", geometryReport failure)]

end Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSourceRefinementReplay.Selection

namespace PreparedRefinementCheckpoint

variable {Result : Type}

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open PreparedSubdivisionModelCore (CenteredEdge)
open PreparedDirectDyadicRefinements (CheckedDirectMeshes)
open PreparedDyadicRefinements (AllParentsProper)
open PreparedSheetContinuation (Coordinate)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open PreparedDirectDyadicRefinements (CheckedSelection MeshAllowanceChecks)
open PreparedDirectRefinementReplay
open PreparedSheetContinuation (Endpoint)

namespace Source

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (proposedRootBits familyForecast checkedDirectSelection
  uniformSelection accurateDirectRefinement)

open Purelib.Riemann.Integration.PreparedSwitchedRefinements (DirectSwitchedState)

set_option genInjectivity false in
/-- An unresolved source-only refinement indexed by its original switched state and target. -/
inductive PendingStep (current : DirectSwitchedState curve source)
    (target : Coordinate) (positive : 0 < target) : Type 2
  /-- The original source-only selection beginning at depth zero remains unresolved. -/ | selection (pending :
    Integration.Preparation.Replay.PreparedSourceRefinementReplay.Selection.PendingSelection current.parents
    current.proper [source] target)
  /-- The exact source-only selection is retained, but its center bank is incomplete. -/ | centers (selected :
    CheckedSelection current.parents [source] target)
      (equal : selected = checkedDirectSelection current.parents current.proper [source] target positive)
      (pending : PendingBankCenters selected.meshes)

constructive_injectivity PendingStep

/-- Restore the original source-only refinement using its distinct first-success selection law.

Return the exact restored step, readiness and parent histories, or retain its unresolved selection or center evidence.
-/
@[expose] def withStep (current : DirectSwitchedState curve source)
    (ready : AllReady current.parents) (histories : PreparedDeferredRecipeReplay.Histories current.parents)
    (target : Coordinate) (positive : 0 < target)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : Except (PendingStep current target positive)
      (Integration.Preparation.Replay.PreparedSourceRefinementReplay.Restoration.RestoredStep current target positive) →
        m Result) : m Result :=
  withSelected current.parents current.proper [source] target positive control directory fun result =>
    match result with
    | .error pending => use (.error (.selection pending))
    | .ok selected =>
        withBankCenters control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("centers"))))
          selected.val.meshes ready histories 0 fun result =>
          match result with
          | .error pending => use (.error (.centers selected.val selected.property pending))
          | .ok centers => use (.ok
              ⟨PreparedSourceRefinementReplay.step current target selected.val centers,
               PreparedSourceRefinementReplay.step_eq current target positive
                 selected.val selected.property centers,
               PreparedSourceRefinementReplay.step_ready current ready target selected.val centers,
               PreparedDeferredRecipeReplay.Histories.blocks selected.val.meshes centers histories⟩)

/-- Serialize the source-only selection or remaining selected-center obligation. -/
@[expose] def PendingStep.report {current : DirectSwitchedState curve source}
    {target : Coordinate} {positive : 0 < target} : PendingStep current target positive → Json
  | .selection pending => pending.report
  | .centers selected _ pending => Json.mkObj
      [("reason", toJson "selected original source-only geometry retained; coefficient centres unresolved"),
       ("selectedDepth", toJson selected.depth),
       ("selectedDiameter", toJson (IntegrationCheckpoint.fractionData selected.rootDiameter)),
       ("pending", pendingBankCentersReport pending)]

end Source

end PreparedRefinementCheckpoint

end
