module

public import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # Actual interior-entry rows in original face polynomial models

The retained forward transport row supplies the trace and point frame
already used to acquire the incoming owner's face sheet. The original
trace_aligned operation and the two cached selections identify the SAME
owner in every original cell refinement, without acquiring another trace.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann.Paths.ClearBoxPaths (Route)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank}
variable {models : FaceModels frames face} {point : Canonical} {inside : face.cell.box.Contains point}
variable {owner : Owner (curve.polynomial.eval point)} {inner : Box}

/-- The same original cell refinement is aligned with the actual owner of the retained interior-entry acquisition.

The row's actual preparation and point frame are read from acquired.
trace_aligned consumes that exact row; its returned root relation composes
with acquired.equivalent on the same old owner and original selections.
-/
theorem acquired_aligned (acquired : Entry.Acquisition models inside owner)
    (cell : TransportedCell models.bounds (models.frame.owners acquired.entry.sheet) inner)
    (differential : Differential genus) (pointInside : inner.Contains point) (index : Nat) :
    RootAligned ((Model.overlapRefine cell.model) index) point (ownerName owner) := by
  let row := acquired.forward.row acquired.entry.sheet
  intro count patch patchInside sample roots otherIndex
  exact cell.trace_aligned (entered := TracedPath.build
      (Polynomial.Geometry.ClearPath.nil (polynomial := curve.polynomial) (ambient := face.cell.box)
        face.cell.box.anchor) (.nil face.cell.box.anchor) (models.frame.owners acquired.entry.sheet))
    face.cell.box.contains_anchor differential
    (BranchIsolation.degreePositive curve)
    (LoopMonodromy.BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop row.traced
    (InBox.ofWithin acquired.outward.path acquired.outward.within face.cell.box.contains_anchor)
    acquired.pointFrame pointInside index patch patchInside sample
    (acquired.equivalent.trans roots) otherIndex

/-- The actual original Entry suffices to align a cell polynomial, independently of any complete grid edge.

Both traced paths begin at the retained face-frame owner and have the same
face-potential winding. The original source-anchor reference identifies
their actual finish owners; the original trace_aligned certificate then
changes only its root name. Auxiliary traces here occur only in this proof.
-/
theorem entry_aligned (entry : Entry models point owner)
    (cell : TransportedCell models.bounds (models.frame.owners entry.sheet) inner)
    (differential : Differential genus) (pointInside : inner.Contains point) (index : Nat) :
    RootAligned ((Model.overlapRefine cell.model) index) point (ownerName owner) := by
  obtain ⟨ownerTrace, winding⟩ := entry.reached
  let route := Route.build face.clearance face.cell.box.anchor point face.cell.box.contains_anchor
    (cell.geometry.refines.contains pointInside)
  let traced := TracedPath.build route.path route.within (models.frame.owners entry.sheet)
  let frame := OwnerFrame.build owner.parameterNonzero
  have equivalent := RootContinuation.ClearBoxRootTransport.TracedPath.equivalentOfOwnerPathSelections
    (LoopMonodromy.BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop
    route.within traced ownerTrace frame (frame.select traced.finishOwner) (frame.select owner)
    ((Paths.ClearBoxPathWinding.Route.winding face.clearance (BranchIsolation.degreePositive curve)
      route face.cell.box.contains_anchor).trans winding.symm)
  intro count patch patchInside sample roots otherIndex
  exact cell.trace_aligned (entered := TracedPath.build
      (Polynomial.Geometry.ClearPath.nil (polynomial := curve.polynomial) (ambient := face.cell.box)
        face.cell.box.anchor) (.nil face.cell.box.anchor) (models.frame.owners entry.sheet))
    face.cell.box.contains_anchor differential
    (BranchIsolation.degreePositive curve)
    (LoopMonodromy.BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop traced
    (InBox.ofWithin route.path route.within face.cell.box.contains_anchor) frame pointInside index
    patch patchInside sample (equivalent.trans roots) otherIndex

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison

end
