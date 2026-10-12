module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularCapArc
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ArcError
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RamifiedReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularReciprocalAreaComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Synchronized arc plans for the original exterior requests

Every plan retains the regular request already chosen by the intrinsic
chart dispatcher. Shared maxima select one source subdivision and one
energy subdivision. Proof-side selection reads these stored plans without
repeating a source evaluation or searching for equal dependent records.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.SegmentComparison.CapRequest

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RegularCapRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh (SegmentComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison (CapPreparation
  CapRequest RegularCapRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
  (Evaluation)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry (arcArea)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Riemann.Meshes.GridLiftedMesh.LiftedMesh
    vertices edges faces}
  {start finish : Data.Gaussian.Basic.Canonical} {segment : Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial
    (Curves.Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
  {owner : Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Riemann.Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {placement : Riemann.Meshes.GridLiftedMesh.LiftedMesh.SegmentFace mesh segment} {differential :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {compared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison placement piece
    differential parentSheet}

variable {prepared :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation regular
  compared} {target areaTarget : Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {sample :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The original regular request's retained inverse-arc plan; a ramified request has no such plan. -/
@[expose] def ArcPlan (request : SegmentComparison.CapRequest prepared target areaTarget floor)
    (sample : Primitives.Sample cap differential index box) (arcTarget : InverseRootPolynomial.Coordinate) : Type :=
  match request with
  | .regular request => RegularCapRequest.ArcRequest request sample arcTarget
  | .ramified _ _ => PEmpty

namespace ArcPlan

variable {arcTarget : Riemann.Normalization.InverseRootPolynomial.Coordinate} {request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest prepared target
  areaTarget floor}

/-- Prepare the original regular inverse-arc request from retained polynomial energy bounds; the even degree identity
excludes the ramified case. -/
@[expose] def build (request : SegmentComparison.CapRequest prepared target areaTarget floor)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) (bounds : Charts.Reciprocal.Cap.EnergyBounds sample)
    (arcTarget : InverseRootPolynomial.Coordinate) (positive : 0 < arcTarget) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.SegmentComparison.CapRequest.ArcPlan request sample
      arcTarget := by
  cases request with
  | regular request => exact ArcRequest.build request bounds arcTarget positive
  | ramified odd request =>
      have impossible : False := by omega
      exact impossible.elim

/-- The actual uniform fine subdivision required by the retained original regular arc plan. -/
@[expose] def fine (plan :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.SegmentComparison.CapRequest.ArcPlan request sample
  arcTarget) : Nat :=
  match request, plan with
  | .regular _, plan => plan.uniform.depth
  | .ramified _ _, plan => nomatch plan

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.SegmentComparison.CapRequest.ArcPlan
/-- The energy subdivision floor required by the original retained arc plan at the supplied fine depth. -/
@[expose] def energyMinimum (plan :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.SegmentComparison.CapRequest.ArcPlan request sample
  arcTarget) (fine : Nat) : Nat :=
  match request, plan with
  | .regular _, plan => plan.minimumAt fine
  | .ramified _ _, plan => nomatch plan

/-- The original numerical result is an input. The local arc comparison is used only for its proved error; no new
polynomial path is evaluated to explain the already cached energy boundary. -/
theorem error (plan : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.SegmentComparison.CapRequest.ArcPlan
  request sample arcTarget) {fine readingIndex : Nat}
    (evaluated : CapRequest.Evaluation request sample fine readingIndex) (energyDepth : Nat)
    (fineLater : plan.fine ≤ fine) (energyLater : plan.energyMinimum fine ≤ energyDepth) :
    Data.Gaussian.Norm.Basic.normSq (ReciprocalRadialGeometry.arcArea sample.primitive.value.eval energyDepth
      finish start +
      BoundaryRibbon.area (sample.primitive.value.eval start⁻¹) (sample.primitive.value.eval finish⁻¹) +
        evaluated.right.area) < arcTarget := by
  cases request with
  | regular request =>
      have rightEq : evaluated.right.area = evaluated.data.cap.cap.area := by
        rcases evaluated with ⟨data, paths, rfl⟩
        rfl
      rw [rightEq]
      exact (plan.evaluate evaluated.data energyDepth fineLater energyLater).opposite_close
  | ramified odd request => exact nomatch plan

end ArcPlan
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.SegmentComparison.CapRequest

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RegularCapRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison (CapRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.SegmentComparison.CapRequest (ArcPlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (Entry Samples)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry (arcArea)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    base.faces.regulars}
  {index fine readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
  {localTarget localArea arcTarget : Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

set_option genInjectivity false in
/-- The dependent complete arc plan bank on the original exterior request list.

Every entry preserves its actual regular request and the shared cap sample, so later selection reuses the prepared
plans. -/
inductive ArcPlans (sample : Primitives.Sample cap differential index box) (arcTarget :
  InverseRootPolynomial.Coordinate) :
    List (AllSurfacePreparation.Entry regular domains differential localTarget localArea floor) → Type 2
  /-- The empty original request list carries an empty arc plan bank. -/ | nil :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation.ArcPlans sample arcTarget []
  /-- Retain the actual original head arc plan and the dependent plans on the unchanged request tail. -/ | cons {entry :
    AllSurfacePreparation.Entry regular domains differential localTarget localArea floor}
      {entries : List (AllSurfacePreparation.Entry regular domains differential localTarget localArea floor)}
      (head : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.SegmentComparison.CapRequest.ArcPlan
        entry.request sample arcTarget) (tail :
        Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation.ArcPlans sample arcTarget
        entries) : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation.ArcPlans sample
        arcTarget (entry :: entries)

constructive_injectivity ArcPlans

namespace ArcPlans

/-- Prepare the arc plan for each actual original exterior request, preserving the dependent list and shared cap sample.
-/
@[expose] def build (degree : curve.polynomial.natDegree = 2 * genus + 2) (bounds : Charts.Reciprocal.Cap.EnergyBounds
    sample)
    (arcTarget : InverseRootPolynomial.Coordinate) (positive : 0 < arcTarget) :
    (entries : List (AllSurfacePreparation.Entry regular domains differential localTarget localArea floor)) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation.ArcPlans sample arcTarget entries
  | [] => .nil
  | entry :: entries => .cons
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.SegmentComparison.CapRequest.ArcPlan.build entry.request
    degree bounds arcTarget positive)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation.ArcPlans.build degree bounds
    arcTarget positive entries)

/-- The maximum actual fine subdivision requested by the complete original arc plan bank. -/
@[expose] def fineMaximum : {entries : List (AllSurfacePreparation.Entry regular domains differential localTarget
  localArea floor)} → Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation.ArcPlans sample
  arcTarget entries → Nat
  | _, .nil => 0
  | _, .cons head tail => max head.fine tail.fineMaximum

/-- The maximum actual energy floor requested by all original plans at the supplied common fine depth. -/
@[expose] def energyMaximum (fine : Nat) : {entries : List (AllSurfacePreparation.Entry regular domains differential
  localTarget localArea floor)} →
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation.ArcPlans sample arcTarget entries →
  Nat
  | _, .nil => 0
  | _, .cons head tail => max (head.energyMinimum fine) (tail.energyMaximum fine)

/-- Every original request occurrence has a retained plan whose fine and energy floors are paid by the complete cached
maxima. -/
theorem bounded {entries : List (AllSurfacePreparation.Entry regular domains differential localTarget localArea floor)}
    (plans : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation.ArcPlans sample arcTarget
      entries) (fine : Nat) :
    ∀ entry ∈ entries, ∃ plan :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.SegmentComparison.CapRequest.ArcPlan entry.request
      sample arcTarget,
      plan.fine ≤ plans.fineMaximum ∧ plan.energyMinimum fine ≤ plans.energyMaximum fine := by
  induction plans with
  | nil => intro entry member; cases member
  | cons head tail ih =>
      intro entry member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact ⟨head, Data.Nat.Order.le_max_left _ _, Data.Nat.Order.le_max_left _ _⟩
      · obtain ⟨plan, fineLe, energyLe⟩ := ih entry member
        exact ⟨plan, fineLe.trans (Data.Nat.Order.le_max_right _ _), energyLe.trans (Data.Nat.Order.le_max_right _ _)⟩

/-- The acquired original exterior samples satisfy their retained local arc errors at common subdivisions paying every
stored plan. -/
theorem local_errors {entries : List (AllSurfacePreparation.Entry regular domains differential localTarget localArea
  floor)}
    (plans : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation.ArcPlans sample arcTarget
      entries) (samples : AllSurfacePreparation.Samples entries sample shared fine readingIndex)
    (energyDepth : Nat) (fineLater : plans.fineMaximum ≤ fine) (energyLater : plans.energyMaximum fine ≤ energyDepth) :
    ∀ value ∈ samples.values,
      Data.Gaussian.Norm.Basic.normSq (ReciprocalRadialGeometry.arcArea sample.primitive.value.eval energyDepth
        value.entry.occurrence.finish value.entry.occurrence.start + value.endpointArea + value.evaluated.right.area) <
          arcTarget := by
  intro value member
  have entryMember : value.entry ∈ entries := samples.entries_eq ▸ Map.mem_map.mpr ⟨value, member, rfl⟩
  obtain ⟨plan, fineLe, energyLe⟩ := plans.bounded fine value.entry entryMember
  exact plan.error value.evaluated energyDepth (fineLe.trans fineLater) (energyLe.trans energyLater)

end ArcPlans
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularArcPlans.AllSurfacePreparation
