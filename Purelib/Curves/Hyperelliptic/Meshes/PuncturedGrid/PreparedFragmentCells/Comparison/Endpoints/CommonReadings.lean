module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints.Numerical
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentAccuracy
public import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
public import Purelib.Riemann.Readings.UniformPreparedRequests.Face.Shared
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Tactic.Ring

import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootPathTransport.Numerical
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # One shared primitive reading bank for two retained regular-leaf connector preparations

The actual parent caches are inputs. Their splits and the physical retained
split determine one mesh and an actual-count numerical floor before requests
are acquired. The two controlled request banks remain separate, while both
summaries and the original physical comparison use the same cached readings.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (ParentReached)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (DomainMeshBudget DomainMeshReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums (SplitReadings FragmentSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction
open Purelib.Approximation.Rational.Budget
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann.Integration.PreparedParentSplitting (ParentSplits PreparedSplitMesh)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Integration.RectangularSharedPrimitives.SharedPrimitiveValues (atPoint)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerSelection)
open Purelib.Riemann.RootContinuation.RootPathTransport.TransportRow (Numerical)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {parent : CenteredEdge curve differential} {target : Rational}
variable {cuts : List Rational} {partition : Geometry.Rectangle.AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval} {domains : FaceDomainBank frames faces.regulars}
variable {request : LocalRequest parent count target}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {location : RegularLocation faces.regulars fragment.cell}
variable {retained : PrimitiveFragmentCell.RegularRequest domains request fragment location}
variable {upper : retained.UpperEndpoint} {parentSheet : Fin 2}
variable {lower : CoveredTracedPath retained.compared.acquired.inward.path
  (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index)}
variable {forward : CoveredTracedPath upper.acquired.outward.path
  (upper.acquired.faceFrame.owners upper.acquired.entry.sheet)}
variable {lowerParents : ParentCache lower differential parentSheet}
variable {upperParents : ParentCache forward differential parentSheet}

namespace PrimitiveFragmentCell.RegularRequest.UpperEndpoint.CommonReadings

/-- The same old lower Entry reaches every actual parent of the retained new return preparation. -/
theorem lower_reached (selected : CenteredEdge curve differential) (member : selected ∈ lowerParents.parents) :
    ParentReached location.face.cell.box
      (retained.compared.shared.models.frame.owners retained.compared.acquired.entry.sheet) selected := by
  let acquired := retained.compared.acquired
  let entry : Entry retained.compared.shared.models fragment.first
      (acquired.pointFrame.owners acquired.selected.index) :=
    ⟨acquired.entry.sheet, acquired.entry.reached.append
      (Face.Entries.Reached.ofEquivalent acquired.selected.equivalent)⟩
  have present : selected ∈ (CenteredPathChain.ofPreparedPath
      curve differential parentSheet lower.traced.prepared).parents := by
    rewrite [← lowerParents.parents_eq]
    exact member
  exact entry.parent_reached differential parentSheet lower.traced
    (InBox.ofWithin acquired.inward.path acquired.inward.within (fragment.regular_endpoints location).1)
    selected present

/-- The actual upper parents use the same retained lower face sheet through the derived sheet equality. -/
theorem upper_reached (selected : CenteredEdge curve differential) (member : selected ∈ upperParents.parents) :
    ParentReached location.face.cell.box
      (retained.compared.shared.models.frame.owners retained.compared.acquired.entry.sheet) selected := by
  have present : selected ∈ (CenteredPathChain.ofPreparedPath
      curve differential parentSheet forward.traced.prepared).parents := by
    rewrite [← upperParents.parents_eq]
    exact member
  have reached := (Entry.origin retained.compared.shared.models upper.acquired.entry.sheet).parent_reached
    differential parentSheet forward.traced
    (InBox.ofWithin upper.acquired.outward.path upper.acquired.outward.within location.face.cell.box.contains_anchor)
    selected present
  exact Eq.mp (congrArg (fun sheet => ParentReached location.face.cell.box
    (retained.compared.shared.models.frame.owners sheet) selected) upper.sheet_eq.symm) reached

/-- The cached split banks, joined bank, point list, mesh budget and actual-count accuracy before request acquisition.

All components retain their whole original factory equations. The original
physical fragment split remains an input. Explicit endpoint extras also cover
empty numerical parent words and preserve stationary or repeated points.
-/
@[expose] def Preparation (tolerance : Rational) (positive : 0 < tolerance) :=
  Σ splits :
    {value : ParentSplits retained.compared.domain.cuts lowerParents.parents //
      value = ParentSplits.build retained.compared.domain.cuts lowerParents.parents (fun edge member =>
        ⟨retained.compared.domain.covers (lower_reached (lowerParents := lowerParents) edge member).first_inside,
          retained.compared.domain.covers (lower_reached (lowerParents := lowerParents) edge member).last_inside⟩)} ×
    {value : ParentSplits retained.compared.domain.cuts upperParents.parents //
      value = ParentSplits.build retained.compared.domain.cuts upperParents.parents (fun edge member =>
        ⟨retained.compared.domain.covers (upper_reached (upperParents := upperParents) edge member).first_inside,
          retained.compared.domain.covers (upper_reached (upperParents := upperParents) edge member).last_inside⟩)},
  Σ joined : {value : ParentSplits retained.compared.domain.cuts (lowerParents.parents ++ upperParents.parents) //
    value = splits.1.val.append splits.2.val},
  Σ points : {value : List Canonical // value = joined.val.points ++
    (retained.compared.split.points ++ [fragment.first, location.face.cell.box.anchor, fragment.last])},
  Σ shared : {value : DomainMeshBudget retained.compared.domain differential points.val tolerance //
    value = DomainMeshBudget.build retained.compared.domain differential points.val tolerance positive},
  {value : FragmentAccuracy shared.val.globalBounds retained.compared.domain.steps
      (joined.val.pieceCount + retained.compared.split.count) (tolerance / 16) //
    value =
      let initial := FragmentAccuracy.build shared.val.globalBounds retained.compared.domain.steps
        (joined.val.pieceCount + retained.compared.split.count) (tolerance / 16)
        (Order.Field.div_pos_direct positive (by decide))
      let stage := max shared.val.accuracy.index initial.grid.index
      initial.atGridIndex stage (Data.Nat.Order.le_max_right _ _)}

namespace Preparation

/-- Split the two supplied parent caches and prepare one actual union mesh and floor, without acquiring requests.

The original lower Entry and derived upper sheet equality certify the same
retained domain. Splits, joined bank, point occurrences, mesh budget and
raised actual-count budget are each materialized once before requests.
-/
def build (tolerance : Rational) (positive : 0 < tolerance) :
    Preparation (lowerParents := lowerParents) (upperParents := upperParents) tolerance positive :=
  let left := ParentSplits.build retained.compared.domain.cuts lowerParents.parents (fun edge member =>
    ⟨retained.compared.domain.covers (lower_reached (lowerParents := lowerParents) edge member).first_inside,
      retained.compared.domain.covers (lower_reached (lowerParents := lowerParents) edge member).last_inside⟩)
  let right := ParentSplits.build retained.compared.domain.cuts upperParents.parents (fun edge member =>
    ⟨retained.compared.domain.covers (upper_reached (upperParents := upperParents) edge member).first_inside,
      retained.compared.domain.covers (upper_reached (upperParents := upperParents) edge member).last_inside⟩)
  let joined := left.append right
  let points := joined.points ++
    (retained.compared.split.points ++ [fragment.first, location.face.cell.box.anchor, fragment.last])
  let shared := DomainMeshBudget.build retained.compared.domain differential points tolerance positive
  let initial := FragmentAccuracy.build shared.globalBounds retained.compared.domain.steps
    (joined.pieceCount + retained.compared.split.count) (tolerance / 16)
    (Order.Field.div_pos_direct positive (by decide))
  let stage := max shared.accuracy.index initial.grid.index
  let budget := initial.atGridIndex stage (Data.Nat.Order.le_max_right _ _)
  ⟨⟨⟨left, rfl⟩, ⟨right, rfl⟩⟩, ⟨joined, rfl⟩, ⟨points, rfl⟩, ⟨shared, rfl⟩, ⟨budget, rfl⟩⟩

variable {tolerance : Rational} {positive : 0 < tolerance}
variable (prepared : Preparation (lowerParents := lowerParents) (upperParents := upperParents) tolerance positive)

/-- Read the same original lower split bank. -/
def left : ParentSplits retained.compared.domain.cuts lowerParents.parents := prepared.1.1.val

/-- Read the same original upper split bank. -/
def right : ParentSplits retained.compared.domain.cuts upperParents.parents := prepared.1.2.val

/-- Read the complete once-concatenated original split bank. -/
def joined : ParentSplits retained.compared.domain.cuts (lowerParents.parents ++ upperParents.parents) :=
  prepared.2.1.val

/-- Read the exact materialized endpoint occurrence list. -/
def points : List Canonical := prepared.2.2.1.val

/-- Read the complete original mesh and scalar-majorant cache on that point list. -/
def shared : DomainMeshBudget retained.compared.domain differential prepared.points tolerance :=
  prepared.2.2.2.1.val

/-- Read the computed actual-total-count fragment budget. -/
def budget : FragmentAccuracy prepared.shared.globalBounds retained.compared.domain.steps
    (prepared.joined.pieceCount + retained.compared.split.count) (tolerance / 16) := prepared.2.2.2.2.val

/-- The lower split cache is the complete original factory on the supplied actual lower parents. -/
theorem left_eq : prepared.left = ParentSplits.build retained.compared.domain.cuts lowerParents.parents
    (fun edge member =>
      ⟨retained.compared.domain.covers (lower_reached (lowerParents := lowerParents) edge member).first_inside,
        retained.compared.domain.covers (lower_reached (lowerParents := lowerParents) edge member).last_inside⟩) :=
  prepared.1.1.property

/-- The upper split cache is the complete original factory on the supplied actual upper parents. -/
theorem right_eq : prepared.right = ParentSplits.build retained.compared.domain.cuts upperParents.parents
    (fun edge member =>
      ⟨retained.compared.domain.covers (upper_reached (upperParents := upperParents) edge member).first_inside,
        retained.compared.domain.covers (upper_reached (upperParents := upperParents) edge member).last_inside⟩) :=
  prepared.1.2.property

/-- The same original mesh-budget factory owns every retained shared mesh and scalar majorant. -/
theorem shared_eq : prepared.shared = DomainMeshBudget.build retained.compared.domain differential
    prepared.points tolerance positive := prepared.2.2.2.1.property

/-- The whole fragment budget is selected after the actual split counts and raised to the actual shared mesh stage. -/
theorem budget_eq : prepared.budget =
    let initial := FragmentAccuracy.build prepared.shared.globalBounds retained.compared.domain.steps
      (prepared.joined.pieceCount + retained.compared.split.count) (tolerance / 16)
      (Order.Field.div_pos_direct positive (by decide))
    let stage := max prepared.shared.accuracy.index initial.grid.index
    initial.atGridIndex stage (Data.Nat.Order.le_max_right _ _) := prepared.2.2.2.2.property

/-- The whole joined cache is the original append on those two retained banks. -/
theorem joined_eq : prepared.joined = prepared.left.append prepared.right := prepared.2.1.property

/-- The whole point bank preserves the actual physical split and all three endpoint occurrences. -/
theorem points_eq : prepared.points = prepared.joined.points ++
    (retained.compared.split.points ++ [fragment.first, location.face.cell.box.anchor, fragment.last]) :=
  prepared.2.2.1.property

/-- Both retained split banks share the original common mesh without rebuilding any split or vertex data.

Body reduction is needed to identify its mesh field with the literal shared
mesh in the typed SplitReadings consumers. This is only an original structure
constructor on cached fields, not a second mesh acquisition.
-/
@[expose] def mesh : PreparedSplitMesh retained.compared.domain.cuts
    (lowerParents.parents ++ upperParents.parents)
    (retained.compared.split.points ++ [fragment.first, location.face.cell.box.anchor, fragment.last]) :=
  ⟨prepared.joined, prepared.points, prepared.points_eq, prepared.shared.mesh⟩

/-- The original lower split occurrence remains literal in the single mesh. -/
theorem left_included {edge : CenteredEdge curve differential}
    (split : Riemann.Paths.RectangularSegmentSplitting.SegmentSplit retained.compared.domain.cuts
      (edge.edge.point 0) (edge.edge.point 1)) (member : ParentSplits.Member split prepared.left) :
    ParentSplits.Member split prepared.mesh.splits :=
  Eq.mp (congrArg (fun bank => ParentSplits.Member split bank) prepared.joined_eq.symm)
    (ParentSplits.Member.append_left member prepared.right)

/-- The original upper split occurrence remains literal after the entire lower spine. -/
theorem right_included {edge : CenteredEdge curve differential}
    (split : Riemann.Paths.RectangularSegmentSplitting.SegmentSplit retained.compared.domain.cuts
      (edge.edge.point 0) (edge.edge.point 1)) (member : ParentSplits.Member split prepared.right) :
    ParentSplits.Member split prepared.mesh.splits :=
  Eq.mp (congrArg (fun bank => ParentSplits.Member split bank) prepared.joined_eq.symm)
    (ParentSplits.Member.append_right prepared.left member)

/-- Every original physical split endpoint occurrence belongs to the same materialized point bank. -/
theorem physical_included (point : Canonical) (member : point ∈ retained.compared.split.points) :
    point ∈ prepared.points := by
  rewrite [prepared.points_eq]
  exact List.mem_append_right _ (List.mem_append_left _ member)

/-- The literal lower endpoint is retained even when both numerical parent words are empty. -/
theorem first_included : fragment.first ∈ prepared.points := by
  rewrite [prepared.points_eq]
  exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)

/-- The same face anchor is an explicit occurrence in the shared point bank. -/
theorem anchor_included : location.face.cell.box.anchor ∈ prepared.points := by
  rewrite [prepared.points_eq]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- The literal upper endpoint is retained independently of a nonempty numerical word. -/
theorem last_included : fragment.last ∈ prepared.points := by
  rewrite [prepared.points_eq]
  exact List.mem_append_right _ (List.mem_append_right _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- The computed common fragment stage also pays the original shared mesh's ownership stage. -/
theorem later : prepared.shared.accuracy.index ≤ prepared.budget.grid.index := by
  have factory := prepared.2.2.2.2.property
  have indexEq := congrArg (fun value : FragmentAccuracy prepared.shared.globalBounds retained.compared.domain.steps
    (prepared.joined.pieceCount + retained.compared.split.count) (tolerance / 16) => value.grid.index) factory
  exact (Data.Nat.Order.le_max_left _ _).trans_eq indexEq.symm

/-- The actual lower count is at most the full two-row and physical-fragment count. -/
theorem left_count_le : prepared.left.pieceCount ≤ prepared.joined.pieceCount + retained.compared.split.count := by
  have joinedCount := (congrArg ParentSplits.pieceCount prepared.joined_eq).trans
    (ParentSplits.pieceCount_append prepared.left prepared.right)
  exact ((Nat.le_add_right prepared.left.pieceCount prepared.right.pieceCount).trans_eq joinedCount.symm).trans
    (Nat.le_add_right prepared.joined.pieceCount retained.compared.split.count)

/-- The actual upper count is at most the same retained full count. -/
theorem right_count_le : prepared.right.pieceCount ≤ prepared.joined.pieceCount + retained.compared.split.count := by
  have joinedCount := (congrArg ParentSplits.pieceCount prepared.joined_eq).trans
    (ParentSplits.pieceCount_append prepared.left prepared.right)
  have initial := (Nat.le_add_right prepared.right.pieceCount prepared.left.pieceCount).trans_eq
    (Nat.add_comm prepared.right.pieceCount prepared.left.pieceCount)
  exact (initial.trans_eq joinedCount.symm).trans
    (Nat.le_add_right prepared.joined.pieceCount retained.compared.split.count)

end Preparation

section Acquired

variable {tolerance : Rational} {positive : 0 < tolerance}
variable {prepared : Preparation (lowerParents := lowerParents) (upperParents := upperParents) tolerance positive}
variable {lowerEq : lower = CoveredTracedPath.build retained.compared.acquired.inward.path
  retained.compared.acquired.inward.within
  (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index)}
variable {lowerParentsEq : lowerParents = ParentCache.build lower differential parentSheet}
variable {lowerSelection : OwnerSelection retained.compared.acquired.faceFrame.owners lower.traced.finishOwner}
variable {lowerSelectionEq : lowerSelection = retained.compared.acquired.faceFrame.select lower.traced.finishOwner}
variable {forwardEq : forward = CoveredTracedPath.build upper.acquired.outward.path upper.acquired.outward.within
  (upper.acquired.faceFrame.owners upper.acquired.entry.sheet)}
variable {upperParentsEq : upperParents = ParentCache.build forward differential parentSheet}
variable {upperSelection : OwnerSelection upper.acquired.pointFrame.owners forward.traced.finishOwner}
variable {upperSelectionEq : upperSelection = upper.acquired.pointFrame.select forward.traced.finishOwner}

/-- The two separate complete numerical executions on the actual shared-mesh floor.

Each original ofPrepared call consumes the supplied retained preparation,
parent cache and finish selection; it acquires only its own controlled bank.
The two original whole rows and all factory receipts remain in those values.
-/
@[expose] def Requests :=
  {value : retained.BackwardNumerical parentSheet (tolerance / 16)
      (Order.Field.div_pos_direct positive (by decide)) prepared.budget.grid.index //
    value = Numerical.ofPrepared
      (retained.compared.acquired.backward.row retained.compared.acquired.selected.index)
      retained.compared.acquired.inward.within differential parentSheet lower lowerEq lowerParents lowerParentsEq
      lowerSelection lowerSelectionEq (tolerance / 16)
      (Order.Field.div_pos_direct positive (by decide)) prepared.budget.grid.index} ×
  {value : upper.ForwardNumerical parentSheet (tolerance / 16)
      (Order.Field.div_pos_direct positive (by decide)) prepared.budget.grid.index //
    value = Numerical.ofPrepared (upper.acquired.forward.row upper.acquired.entry.sheet)
      upper.acquired.outward.within differential parentSheet forward forwardEq upperParents upperParentsEq
      upperSelection upperSelectionEq (tolerance / 16)
      (Order.Field.div_pos_direct positive (by decide)) prepared.budget.grid.index}

namespace Requests

/-- Acquire each controlled request once, after the union mesh and actual fragment floor are materialized.

The supplied whole preparation, parent and selection factory identities are
passed to the two original ofPrepared constructors. No earlier execution is
replaced by a canonical recomputation.
-/
def build : Requests (prepared := prepared) (lowerEq := lowerEq) (lowerParentsEq := lowerParentsEq)
    (lowerSelection := lowerSelection) (lowerSelectionEq := lowerSelectionEq) (forwardEq := forwardEq)
    (upperParentsEq := upperParentsEq) (upperSelection := upperSelection) (upperSelectionEq := upperSelectionEq) :=
  let left := Numerical.ofPrepared
    (retained.compared.acquired.backward.row retained.compared.acquired.selected.index)
    retained.compared.acquired.inward.within differential parentSheet lower lowerEq lowerParents lowerParentsEq
    lowerSelection lowerSelectionEq (tolerance / 16)
    (Order.Field.div_pos_direct positive (by decide)) prepared.budget.grid.index
  let right := Numerical.ofPrepared (upper.acquired.forward.row upper.acquired.entry.sheet)
    upper.acquired.outward.within differential parentSheet forward forwardEq upperParents upperParentsEq
    upperSelection upperSelectionEq (tolerance / 16)
    (Order.Field.div_pos_direct positive (by decide)) prepared.budget.grid.index
  ⟨⟨left, rfl⟩, ⟨right, rfl⟩⟩

variable (requested : Requests (prepared := prepared) (lowerEq := lowerEq) (lowerParentsEq := lowerParentsEq)
    (lowerSelection := lowerSelection) (lowerSelectionEq := lowerSelectionEq) (forwardEq := forwardEq)
    (upperParentsEq := upperParentsEq) (upperSelection := upperSelection) (upperSelectionEq := upperSelectionEq))

/-- Read the complete lower numerical execution, including its retained old row and original new preparation. -/
def backward : retained.BackwardNumerical parentSheet (tolerance / 16)
    (Order.Field.div_pos_direct positive (by decide)) prepared.budget.grid.index := requested.1.val

/-- Read the complete upper numerical execution with its original target-frame selection. -/
def outward : upper.ForwardNumerical parentSheet (tolerance / 16)
    (Order.Field.div_pos_direct positive (by decide)) prepared.budget.grid.index := requested.2.val

/-- The complete lower execution is the original request-only factory on the supplied retained prefix caches. -/
theorem backward_eq : requested.backward = Numerical.ofPrepared
    (retained.compared.acquired.backward.row retained.compared.acquired.selected.index)
    retained.compared.acquired.inward.within differential parentSheet lower lowerEq lowerParents lowerParentsEq
    lowerSelection lowerSelectionEq (tolerance / 16)
    (Order.Field.div_pos_direct positive (by decide)) prepared.budget.grid.index := requested.1.property

/-- The complete upper execution is the original request-only factory on its distinct retained prefix caches. -/
theorem outward_eq : requested.outward = Numerical.ofPrepared
    (upper.acquired.forward.row upper.acquired.entry.sheet) upper.acquired.outward.within differential parentSheet
    forward forwardEq upperParents upperParentsEq upperSelection upperSelectionEq (tolerance / 16)
    (Order.Field.div_pos_direct positive (by decide)) prepared.budget.grid.index := requested.2.property

/-- Read the same whole lower request on the supplied actual lower parent-cache index. -/
def lowerRequest : ControlledSumRequest lowerParents.parents genus (tolerance / 16) :=
  requested.backward.requestedOn lower lowerEq lowerParents lowerParentsEq

/-- Read the same whole upper request on the supplied actual upper parent-cache index. -/
def upperRequest : ControlledSumRequest upperParents.parents genus (tolerance / 16) :=
  requested.outward.requestedOn forward forwardEq upperParents upperParentsEq

/-- The lower parent-list transport preserves its entire controlled request, not only its scalar readings. -/
theorem lowerRequest_heq : HEq requested.lowerRequest requested.backward.requested :=
  requested.backward.requestedOn_heq lower lowerEq lowerParents lowerParentsEq

/-- The upper parent-list transport likewise preserves its entire controlled request. -/
theorem upperRequest_heq : HEq requested.upperRequest requested.outward.requested :=
  requested.outward.requestedOn_heq forward forwardEq upperParents upperParentsEq

/-- The lower numerical request retains the already selected common stage. -/
theorem lower_minimumIndex : requested.lowerRequest.minimumIndex = prepared.budget.grid.index :=
  requested.backward.requestedOn_minimumIndex lower lowerEq lowerParents lowerParentsEq

/-- The upper numerical request retains that same selected stage. -/
theorem upper_minimumIndex : requested.upperRequest.minimumIndex = prepared.budget.grid.index :=
  requested.outward.requestedOn_minimumIndex forward forwardEq upperParents upperParentsEq

end Requests

variable {requested : Requests (prepared := prepared) (lowerEq := lowerEq) (lowerParentsEq := lowerParentsEq)
    (lowerSelection := lowerSelection) (lowerSelectionEq := lowerSelectionEq) (forwardEq := forwardEq)
    (upperParentsEq := upperParentsEq) (upperSelection := upperSelection) (upperSelectionEq := upperSelectionEq)}

/-- The original two fragment-summary types share one exact mesh, primitive bank and reading owner. -/
@[expose] def Summaries (numerics : DomainPrimitives retained.compared.domain differential prepared.budget.grid.index)
    (shared : DomainMeshReadings prepared.shared numerics) :=
  FragmentSum (bank := bank) (frames := frames) (face := location.face) (models := retained.compared.shared.models)
    (sheet := retained.compared.acquired.entry.sheet) (patch := retained.compared.domain.patch)
    (gridRequest := prepared.budget.grid) (mesh := prepared.mesh) prepared.shared.bounds shared.readings
    prepared.left requested.lowerRequest.requests ×
  FragmentSum (bank := bank) (frames := frames) (face := location.face) (models := retained.compared.shared.models)
    (sheet := retained.compared.acquired.entry.sheet) (patch := retained.compared.domain.patch)
    (gridRequest := prepared.budget.grid) (mesh := prepared.mesh) prepared.shared.bounds shared.readings
    prepared.right requested.upperRequest.requests

/-- Build both original summaries from the same cached readings and their separate original request banks.

The original Member transports keep each retained split occurrence in the
one common mesh. The structural reading constructors consume those same
values and parent reachability proofs in their original order.
-/
def summarize (numerics : DomainPrimitives retained.compared.domain differential prepared.budget.grid.index)
    (shared : DomainMeshReadings prepared.shared numerics) :
    Summaries (requested := requested) numerics shared :=
  let mesh := prepared.mesh
  let left := SplitReadings.build (bank := bank) (frames := frames) (face := location.face)
    (models := retained.compared.shared.models) (sheet := retained.compared.acquired.entry.sheet)
    (patch := retained.compared.domain.patch) (gridRequest := prepared.budget.grid) (mesh := mesh)
    prepared.shared.bounds shared.readings prepared.left requested.lowerRequest.requests
    prepared.left_included (lower_reached (lowerParents := lowerParents))
  let right := SplitReadings.build (bank := bank) (frames := frames) (face := location.face)
    (models := retained.compared.shared.models) (sheet := retained.compared.acquired.entry.sheet)
    (patch := retained.compared.domain.patch) (gridRequest := prepared.budget.grid) (mesh := mesh)
    prepared.shared.bounds shared.readings prepared.right requested.upperRequest.requests
    prepared.right_included (upper_reached (upperParents := upperParents))
  ⟨FragmentSum.build left, FragmentSum.build right⟩

/-- One numerical primitive cache, one shared reading execution and both complete original summaries.

The original physical split is not rebuilt. The two summaries keep their
separate requests and signed parent incidences, while anchors, offsets and
all mesh vertex observations are literally shared.
-/
@[expose] def Readings :=
  Σ numerics : {value : DomainPrimitives retained.compared.domain differential prepared.budget.grid.index //
    value = DomainPrimitives.build retained.compared.domain differential prepared.budget.grid.index},
  Σ shared : {value : DomainMeshReadings prepared.shared numerics.val //
    value = DomainMeshReadings.build prepared.shared numerics.val prepared.later},
  {values : Summaries (requested := requested) numerics.val shared.val //
    values = summarize (requested := requested) numerics.val shared.val}

namespace Readings

/-- Execute one primitive bank and one shared reading bank, then fold the two retained subspines.

The actual domain, differential and common stage determine one complete
primitive/anchor/offset cache. Both summaries retain this single original
reading result; no second face or numerical owner is selected.
-/
def build : Readings (requested := requested) :=
  let numerics := DomainPrimitives.build retained.compared.domain differential prepared.budget.grid.index
  let shared := DomainMeshReadings.build prepared.shared numerics prepared.later
  let summaries := summarize (requested := requested) numerics shared
  ⟨⟨numerics, rfl⟩, ⟨shared, rfl⟩, ⟨summaries, rfl⟩⟩

variable (observed : Readings (requested := requested))

/-- Read the complete original primitive, anchor, offset and four-corner cache. -/
def numerics : DomainPrimitives retained.compared.domain differential prepared.budget.grid.index := observed.1.val

/-- Read the one complete shared mesh-reading result. -/
def shared : DomainMeshReadings prepared.shared observed.numerics := observed.2.1.val

/-- Read both complete original summaries, retaining their original observation spines. -/
def summaries : Summaries (requested := requested) observed.numerics observed.shared :=
  observed.2.2.val

/-- The complete primitive cache is its original factory at the common paid index. -/
theorem numerics_eq : observed.numerics = DomainPrimitives.build retained.compared.domain differential
    prepared.budget.grid.index := observed.1.property

/-- The complete mesh readings are the original factory on these literal anchors, offsets and mesh. -/
theorem shared_eq : observed.shared = DomainMeshReadings.build prepared.shared observed.numerics prepared.later :=
  observed.2.1.property

/-- Both complete summaries are the same paired factory on the single retained reading result. -/
theorem summaries_eq : observed.summaries =
    summarize (requested := requested) observed.numerics observed.shared := observed.2.2.property

/-- The actual lower fragment discrepancy is paid by the actual common-count allowance and retained request floor. -/
theorem lower_bound_lt : observed.summaries.1.bound < tolerance / 16 := by
  have floor := prepared.budget.grid_ge.trans_eq requested.lower_minimumIndex.symm
  exact observed.summaries.1.bound_lt_of_count_le prepared.left_count_le
    (RequestedFragments.indices_of_le floor requested.lowerRequest.requests requested.lowerRequest.indices_ge)

/-- The actual upper fragment discrepancy uses that same common allowance with its own retained floor. -/
theorem upper_bound_lt : observed.summaries.2.bound < tolerance / 16 := by
  have floor := prepared.budget.grid_ge.trans_eq requested.upper_minimumIndex.symm
  exact observed.summaries.2.bound_lt_of_count_le prepared.right_count_le
    (RequestedFragments.indices_of_le floor requested.upperRequest.requests requested.upperRequest.indices_ge)

/-- The lower shared increment is compared to the SAME lower controlled primitive sum. -/
theorem lower_accurate : normSq (observed.summaries.1.value - requested.lowerRequest.primitiveSum) < tolerance / 16 :=
  observed.summaries.1.controlled_accurate.trans_lt observed.lower_bound_lt

/-- The upper shared increment is compared to its distinct original controlled primitive sum. -/
theorem upper_accurate : normSq (observed.summaries.2.value - requested.upperRequest.primitiveSum) < tolerance / 16 :=
  observed.summaries.2.controlled_accurate.trans_lt observed.upper_bound_lt

/-- The actual lower parent chain telescopes only the single shared reading function at its original endpoints. -/
theorem lower_increment : observed.summaries.1.value =
    atPoint observed.shared.readings location.face.cell.box.anchor -
      atPoint observed.shared.readings fragment.first := by
  obtain ⟨chain⟩ := lowerParents.chain
  rewrite [observed.summaries.1.value_eq, observed.summaries.1.values_eq]
  have telescope := observed.summaries.1.entries.sum_eq_increment
    (start := ⟨fragment.first, parentSheet⟩)
    (finish := ⟨location.face.cell.box.anchor, parentSheet⟩) chain
  exact telescope

/-- The actual upper parent chain telescopes the SAME retained reading function from anchor to upper Point. -/
theorem upper_increment : observed.summaries.2.value =
    atPoint observed.shared.readings fragment.last -
      atPoint observed.shared.readings location.face.cell.box.anchor := by
  obtain ⟨chain⟩ := upperParents.chain
  rewrite [observed.summaries.2.value_eq, observed.summaries.2.values_eq]
  have telescope := observed.summaries.2.entries.sum_eq_increment
    (start := ⟨location.face.cell.box.anchor, parentSheet⟩)
    (finish := ⟨fragment.last, parentSheet⟩) chain
  exact telescope

/-- The two cached row values telescope at the literal common anchor without cancelling any Owner observation jump. -/
theorem increment : observed.summaries.1.value + observed.summaries.2.value =
    atPoint observed.shared.readings fragment.last -
      atPoint observed.shared.readings fragment.first := by
  rewrite [observed.lower_increment, observed.upper_increment]
  ring1

/-- The actual two controlled primitive sums approximate the same retained endpoint increment quantitatively.

This compares their original polynomial sums. Owner observation handoffs
and independent geometric integral attachment remain separate payments.
-/
theorem primitive_accurate :
    normSq ((atPoint observed.shared.readings fragment.last -
      atPoint observed.shared.readings fragment.first) -
      (requested.lowerRequest.primitiveSum + requested.upperRequest.primitiveSum)) < tolerance / 4 := by
  rewrite [← observed.increment]
  have identity : (observed.summaries.1.value + observed.summaries.2.value) -
      (requested.lowerRequest.primitiveSum + requested.upperRequest.primitiveSum) =
      (observed.summaries.1.value - requested.lowerRequest.primitiveSum) +
        (observed.summaries.2.value - requested.upperRequest.primitiveSum) := by ring1
  rewrite [identity]
  have paid := Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 2)
    (Order.Arithmetic.add_lt_add_direct observed.lower_accurate observed.upper_accurate)
  exact (Norm.Bounds.normSq_add_le_two _ _).trans_lt (paid.trans_eq (by
    apply mul_left_cancel_of_nonzero (factor := (4 : Rational)) (by decide +kernel)
    calc
      4 * (2 * (tolerance / 16 + tolerance / 16)) = (tolerance / 16) * 16 := by ring1
      _ = tolerance := Field.div_mul_cancel_of_ne tolerance 16 (by decide +kernel)
      _ = 4 * (tolerance / 4) :=
        ((show 4 * (tolerance / 4) = (tolerance / 4) * 4 by ring1).trans
          (Field.div_mul_cancel_of_ne tolerance 4 (by decide +kernel))).symm))

/-- The lower shared row value pays both its original fragment error and actual cached child-model integral error. -/
theorem lower_integral_accurate :
    normSq (observed.summaries.1.value - requested.lowerRequest.integralSample) < tolerance / 4 := by
  have sampling := requested.lowerRequest.toPrimitiveSumRequest.accurate
  rewrite [← Norm.Basic.normSq_eq_canonical] at sampling
  have identity : observed.summaries.1.value - requested.lowerRequest.integralSample =
      (observed.summaries.1.value - requested.lowerRequest.primitiveSum) +
        (requested.lowerRequest.primitiveSum - requested.lowerRequest.integralSample) := by ring1
  rewrite [identity]
  have paid := Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 2)
    (Order.Arithmetic.add_lt_add_direct observed.lower_accurate sampling)
  exact (Norm.Bounds.normSq_add_le_two _ _).trans_lt (paid.trans_eq (by
    apply mul_left_cancel_of_nonzero (factor := (4 : Rational)) (by decide +kernel)
    calc
      4 * (2 * (tolerance / 16 + tolerance / 16)) = (tolerance / 16) * 16 := by ring1
      _ = tolerance := Field.div_mul_cancel_of_ne tolerance 16 (by decide +kernel)
      _ = 4 * (tolerance / 4) :=
        ((show 4 * (tolerance / 4) = (tolerance / 4) * 4 by ring1).trans
          (Field.div_mul_cancel_of_ne tolerance 4 (by decide +kernel))).symm))

/-- The upper shared row value pays its own distinct cached child-model integral error. -/
theorem upper_integral_accurate :
    normSq (observed.summaries.2.value - requested.upperRequest.integralSample) < tolerance / 4 := by
  have sampling := requested.upperRequest.toPrimitiveSumRequest.accurate
  rewrite [← Norm.Basic.normSq_eq_canonical] at sampling
  have identity : observed.summaries.2.value - requested.upperRequest.integralSample =
      (observed.summaries.2.value - requested.upperRequest.primitiveSum) +
        (requested.upperRequest.primitiveSum - requested.upperRequest.integralSample) := by ring1
  rewrite [identity]
  have paid := Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 2)
    (Order.Arithmetic.add_lt_add_direct observed.upper_accurate sampling)
  exact (Norm.Bounds.normSq_add_le_two _ _).trans_lt (paid.trans_eq (by
    apply mul_left_cancel_of_nonzero (factor := (4 : Rational)) (by decide +kernel)
    calc
      4 * (2 * (tolerance / 16 + tolerance / 16)) = (tolerance / 16) * 16 := by ring1
      _ = tolerance := Field.div_mul_cancel_of_ne tolerance 16 (by decide +kernel)
      _ = 4 * (tolerance / 4) :=
        ((show 4 * (tolerance / 4) = (tolerance / 4) * 4 by ring1).trans
          (Field.div_mul_cancel_of_ne tolerance 4 (by decide +kernel))).symm))

/-- The two actual retained numerical path integrals approximate the one common endpoint increment.

Both integralSample fields belong to the retained independently covered
traces and controlled requests. Their identification with the original
physical OwnerPath still retains its genuine stationary handoff payments.
-/
theorem replacement_accurate :
    normSq ((atPoint observed.shared.readings fragment.last -
      atPoint observed.shared.readings fragment.first) -
      (requested.lowerRequest.integralSample + requested.upperRequest.integralSample)) < tolerance := by
  rewrite [← observed.increment]
  have identity : (observed.summaries.1.value + observed.summaries.2.value) -
      (requested.lowerRequest.integralSample + requested.upperRequest.integralSample) =
      (observed.summaries.1.value - requested.lowerRequest.integralSample) +
        (observed.summaries.2.value - requested.upperRequest.integralSample) := by ring1
  rewrite [identity]
  have paid := Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 2)
    (Order.Arithmetic.add_lt_add_direct observed.lower_integral_accurate observed.upper_integral_accurate)
  exact (Norm.Bounds.normSq_add_le_two _ _).trans_lt (paid.trans_eq (by
    exact (show 2 * (tolerance / 4 + tolerance / 4) = (tolerance / 4) * 4 by ring1).trans
      (Field.div_mul_cancel_of_ne tolerance 4 (by decide +kernel))))

/-- Compare the original physical fragment against that single reading bank with its actual residual and full count.

The actual lower Point, Entry, original request and retained physical split
pay the sign and analytic error. This does not claim a whole-parent face
containment or a vanishing physical residual.
-/
theorem physical_accurate :
    normSq ((atPoint observed.shared.readings fragment.last -
      atPoint observed.shared.readings fragment.first) -
      (request.request.model.primitive.value.eval fragment.last -
        request.request.model.primitive.value.eval fragment.first)) ≤
      Aggregate.countCoordinate retained.compared.split.count *
        (32 * Aggregate.countCoordinate retained.compared.split.count *
          prepared.budget.grid.globalBound +
        2 * Algebra.FiniteSum.Rational.Squares.coordinateSum (retained.compared.split.pieces.map fun piece =>
          request.facePieceCharge retained.compared.domain prepared.shared.bounds piece prepared.budget.grid.index)) :=
  request.faceSharedSplit_increment_le retained.sample retained.compared.acquired.entry retained.compared.domain
    retained.compared.split interval.lower fragment.lower_inside fragment.first_eq.symm
    (fragment.request_endpoints request).1 (fragment.request_endpoints request).2
    prepared.shared.bounds prepared.budget.grid prepared.shared.mesh prepared.physical_included
    observed.shared.readings

end Readings

end Acquired

end PrimitiveFragmentCell.RegularRequest.UpperEndpoint.CommonReadings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
