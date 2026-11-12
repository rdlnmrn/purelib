module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints
public import Purelib.Riemann.RootContinuation.RootPathTransport.Numerical
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
import Purelib.Riemann.RootContinuation.RootPathTransport.RoundTrip
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Tactic.QuotientFreeOmega

/-! # New numerical banks on the two retained regular-leaf connector routes

The old backward and forward rows remain complete comparison inputs. New
covered preparations on their same paths and starting Owners supply actual
proper numerical parents and controlled requests. The original anchor
reference and clear-face windings derive signed endpoint comparisons.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (ParentReached)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.ClearBoxRootTransport
open Purelib.Riemann.RootContinuation.RootPathTransport (TransportRow PathTransport)
open Purelib.Riemann.RootContinuation.RootPathTransport.TransportRow (Numerical)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {parent : CenteredEdge curve differential} {target : Rational}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}
variable {domains : FaceDomainBank frames faces.regulars}
variable {request : LocalRequest parent count target}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {location : RegularLocation faces.regulars fragment.cell}

namespace PrimitiveFragmentCell.RegularRequest

/-- A distinct paid numerical bank retaining the exact original lower backward row as its comparison input. -/
@[expose] def BackwardNumerical (retained : RegularRequest domains request fragment location)
    (parentSheet : Fin 2) (tolerance : Rational) (positive : 0 < tolerance) (minimum : Nat) :=
  Numerical (retained.compared.acquired.backward.row retained.compared.acquired.selected.index)
    retained.compared.acquired.inward.within differential parentSheet tolerance positive minimum

/-- Acquire one new covered lower return and its proper numerical parents and controlled requests. -/
def acquireBackwardNumerical (retained : RegularRequest domains request fragment location)
    (parentSheet : Fin 2) (tolerance : Rational) (positive : 0 < tolerance) (minimum : Nat) :
    retained.BackwardNumerical parentSheet tolerance positive minimum :=
  Numerical.build (retained.compared.acquired.backward.row retained.compared.acquired.selected.index)
    retained.compared.acquired.inward.within differential parentSheet tolerance positive minimum

namespace BackwardNumerical

variable {retained : RegularRequest domains request fragment location}
variable {parentSheet : Fin 2} {tolerance : Rational} {positive : 0 < tolerance} {minimum : Nat}
variable (numerics : retained.BackwardNumerical parentSheet tolerance positive minimum)

/-- The new backward finish selects the same original face-frame index as the old cached backward row. -/
private theorem target_eq : (Numerical.selected numerics).index =
    retained.compared.acquired.backward.target retained.compared.acquired.selected.index := by
  exact TracedPath.selection_eq_of_ownerPath_from_finish
    (LoopMonodromy.BranchCellBank.referenceAt bank location.face.cell.box.anchor
      (location.face.cell.anchor_mem location.face.member)).toLoop
    retained.compared.acquired.inward.within (Numerical.covered numerics).traced
    (retained.compared.acquired.backward.row retained.compared.acquired.selected.index).traced.trace.get
    retained.compared.acquired.faceFrame (Numerical.selected numerics)
    (retained.compared.acquired.backward.row retained.compared.acquired.selected.index).selected
    (PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original
      (retained.compared.acquired.backward.row retained.compared.acquired.selected.index).traced).symm

/-- Compare the independently prepared lower finish to the literal original lower-row finish Owner. -/
def finishEquivalent : NamedEquivalent (ownerName (Numerical.covered numerics).traced.finishOwner)
    (ownerName
      (retained.compared.acquired.backward.row retained.compared.acquired.selected.index).traced.finishOwner) :=
  let same := congrArg (fun index => ownerName (retained.compared.shared.models.frame.owners index))
    numerics.target_eq
  (Numerical.selected numerics).equivalent.trans
    (NamedEquivalent.transport same.symm rfl
      (retained.compared.acquired.backward.row retained.compared.acquired.selected.index).equivalent.symm)

/-- Compare the new lower return's actual finish to the SAME lower retained sheet anchor. -/
def anchorEquivalent : NamedEquivalent (ownerName (Numerical.covered numerics).traced.finishOwner)
    (ownerName (retained.compared.shared.models.frame.owners retained.compared.acquired.entry.sheet)) :=
  NamedEquivalent.transport rfl
    (congrArg (fun index => ownerName (retained.compared.shared.models.frame.owners index))
      retained.compared.acquired.sheet_eq.symm)
    (numerics.finishEquivalent.trans
      (retained.compared.acquired.backward.row retained.compared.acquired.selected.index).equivalent)

/-- Every new lower numerical parent retains the old face Entry and actual source-selection handoff. -/
theorem parent_reached (selected : CenteredEdge curve differential)
    (member : selected ∈ (Numerical.parents numerics).parents) :
    ParentReached location.face.cell.box
      (retained.compared.shared.models.frame.owners retained.compared.acquired.entry.sheet) selected := by
  let acquired := retained.compared.acquired
  let entry : Entry retained.compared.shared.models fragment.first
      (acquired.pointFrame.owners acquired.selected.index) :=
    ⟨acquired.entry.sheet, acquired.entry.reached.append
      (Face.Entries.Reached.ofEquivalent acquired.selected.equivalent)⟩
  have present : selected ∈ (CenteredPathChain.ofPreparedPath
      curve differential parentSheet (Numerical.covered numerics).traced.prepared).parents := by
    rewrite [← (Numerical.parents numerics).parents_eq]
    exact member
  exact entry.parent_reached differential parentSheet (Numerical.covered numerics).traced
    (InBox.ofWithin acquired.inward.path acquired.inward.within (fragment.regular_endpoints location).1)
    selected present

end BackwardNumerical

namespace UpperEndpoint

/-- A distinct paid numerical bank retaining the literal original upper forward row as its comparison input. -/
@[expose] def ForwardNumerical {retained : RegularRequest domains request fragment location}
    (upper : retained.UpperEndpoint) (parentSheet : Fin 2) (tolerance : Rational)
    (positive : 0 < tolerance) (minimum : Nat) :=
  Numerical (upper.acquired.forward.row upper.acquired.entry.sheet) upper.acquired.outward.within
    differential parentSheet tolerance positive minimum

/-- Acquire a new covered upper outward path and its proper numerical parents and controlled requests. -/
def acquireForwardNumerical {retained : RegularRequest domains request fragment location}
    (upper : retained.UpperEndpoint) (parentSheet : Fin 2) (tolerance : Rational)
    (positive : 0 < tolerance) (minimum : Nat) : upper.ForwardNumerical parentSheet tolerance positive minimum :=
  Numerical.build (upper.acquired.forward.row upper.acquired.entry.sheet) upper.acquired.outward.within
    differential parentSheet tolerance positive minimum

namespace ForwardNumerical

variable {retained : RegularRequest domains request fragment location} {upper : retained.UpperEndpoint}
variable {parentSheet : Fin 2} {tolerance : Rational} {positive : 0 < tolerance} {minimum : Nat}
variable (numerics : upper.ForwardNumerical parentSheet tolerance positive minimum)

/-- Compare the new upper finish with the actual original forward-row finish through the same anchor reference. -/
def finishEquivalent : NamedEquivalent (ownerName (Numerical.covered numerics).traced.finishOwner)
    (ownerName (upper.acquired.forward.row upper.acquired.entry.sheet).traced.finishOwner) :=
  TracedPath.equivalentOfOwnerPathSelections
    (LoopMonodromy.BranchCellBank.referenceAt bank location.face.cell.box.anchor
      (location.face.cell.anchor_mem location.face.member)).toLoop
    upper.acquired.outward.within (Numerical.covered numerics).traced
    (upper.acquired.forward.row upper.acquired.entry.sheet).traced.trace.get upper.acquired.pointFrame
    (Numerical.selected numerics) (upper.acquired.forward.row upper.acquired.entry.sheet).selected
    (PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original
      (upper.acquired.forward.row upper.acquired.entry.sheet).traced).symm

/-- Compare the independently prepared upper finish with the SAME retained upper Point Owner. -/
def pointEquivalent : NamedEquivalent (ownerName (Numerical.covered numerics).traced.finishOwner)
    (ownerName upper.sample.owner) := numerics.finishEquivalent.trans upper.acquired.equivalent

/-- Every new upper numerical parent is reached from its literal retained face-sheet source Owner. -/
theorem parent_reached (selected : CenteredEdge curve differential)
    (member : selected ∈ (Numerical.parents numerics).parents) :
    ParentReached location.face.cell.box
      (retained.compared.shared.models.frame.owners upper.acquired.entry.sheet) selected := by
  have present : selected ∈ (CenteredPathChain.ofPreparedPath
      curve differential parentSheet (Numerical.covered numerics).traced.prepared).parents := by
    rewrite [← (Numerical.parents numerics).parents_eq]
    exact member
  exact (Entry.origin retained.compared.shared.models upper.acquired.entry.sheet).parent_reached
    differential parentSheet (Numerical.covered numerics).traced
    (InBox.ofWithin upper.acquired.outward.path upper.acquired.outward.within location.face.cell.box.contains_anchor)
    selected present

end ForwardNumerical

end UpperEndpoint

end PrimitiveFragmentCell.RegularRequest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
