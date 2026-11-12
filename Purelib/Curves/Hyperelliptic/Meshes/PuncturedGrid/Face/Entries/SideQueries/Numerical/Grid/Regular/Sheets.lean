module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.SideQueries.Numerical.Grid.Regular
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.PuncturedFaceLookup

/-! # Lower SheetEntry on the actual cached selected regular fragment

The retained Geometry result supplies both original cell equalities. Its
complete fragment, source edge and selected face remain the nominal input.
The existing lower regular-request factory and one new lower Query run
once; the original hole branch remains separate typed preparation work.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace RegularLocation)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
variable {face : RegularFace base.bank.toBranchCellBank} {models : FaceModels frames face} {point : Canonical}
variable {inside : face.cell.box.Contains point} {sourceOwner : Owner (curve.polynomial.eval point)}

namespace SideQuery.Cache.Numerical

variable {acquired : Acquisition models inside sourceOwner} {side : GridSide}
variable {onSide : face.cell.OnSide point side}
variable {lifted : LiftedFace vertices edges face acquired.entry.sheet}
variable {differential : Differential genus} {notFinish : point ≠ side.finish face.cell.box}
variable {queried : SideQuery.Cache acquired side onSide lifted differential notFinish}
variable {centers : CenterStates curve differential acquired.entry.sheet
  (prepared acquired side lifted queried.connection).2.subdivision}
variable {bounds : Bounds queried.connection.forwardSegment} {mesh : Mesh bounds}
variable {covered : ∀ edge ∈ (prepared acquired side lifted queried.connection).2.subdivision.parameterEdges,
  edge ∈ mesh.edges}
variable {count : Nat} {target : Rational} {positive : 0 < target}
variable {numerics : SideQuery.Cache.Numerical queried centers bounds mesh covered count target positive}

namespace GridFragments.Focus.RegularGeometry

variable {axes : PrimitiveAxes base.bank.grid} {retained : GridFragments numerics axes}
variable {selected : Focus retained} {location : RegularLocation base.faces.regulars selected.fragment.cell}
variable (metadata : RegularGeometry selected location)

/-- The actual retained selected-cell equality and whole located-fragment readback identify the old fragment cell. -/
theorem cell_eq : metadata.val.face.geometry.cell = metadata.val.located.cell :=
  metadata.property.2.1.trans (congrArg (fun value => value.cell) metadata.property.1).symm

/-- The lower request uses exactly the original selected regular-location payload under its cell-index transport. -/
theorem lowerLocation_heq : HEq (SheetEntry.lowerLocation metadata.val metadata.cell_eq) location :=
  (metadata.val.face.located.castCell_heq metadata.cell_eq).trans metadata.property.2.2.2.2

/-- Acquire the complete existing lower regular request and one lower Query on this SAME retained fragment.

The needed cell-index equality is derived from the original cached
geometric certificate. The complete input fragment, including its source
edge and selected location, remains the SheetEntry's nominal owner; no
regular-face reclassification or geometric relation is requested. -/
def acquireSheet (domains : FaceDomainBank frames base.faces.regulars) :
    SheetEntry.Acquisition metadata.val metadata.cell_eq domains numerics.request :=
  SheetEntry.acquire metadata.val metadata.cell_eq domains numerics.request

end GridFragments.Focus.RegularGeometry
end SideQuery.Cache.Numerical
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

end
