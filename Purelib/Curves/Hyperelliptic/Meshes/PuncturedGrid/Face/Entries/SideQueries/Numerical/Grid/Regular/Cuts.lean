module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.SideQueries.Numerical.Grid.Regular.Sheets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Comparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Queries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Queries.Refinement.Mesh
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.SideQueries.Numerical.Point
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.PuncturedFaceLookup

/-! # Partial primitive comparison on the same selected regular side fragment

The selected lower SheetEntry and original numerical Point are retained
inputs. One query-cut cache uses both complete values, deriving its signed
comparison and actual partial payments without a second Point acquisition.
The original side-domain Entry is not substituted for the selected domain.
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry
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

variable {domains : FaceDomainBank frames base.faces.regulars}
variable (attached : SheetEntry.Acquisition metadata.val metadata.cell_eq domains numerics.request)
variable {index : Nat} (data : DomainPrimitives attached.sheetEntry.domain differential index)

/-- Construct the original query-cut cache using the same retained numerical Query and Point.

The actual Focus interval supplies containment. The original lower
SheetEntry supplies the selected face/domain/split, and the numerical
Point's whole acquisition law pays the existing Point cache field.
All original QueryCut readbacks, signed comparison and squared-fraction
before/after payments apply to the returned value. Cross-face primitive
constants, whole-word incidence and canonical attachment remain separate.
-/
def cutAtPoint (sampled : PointAcquisition numerics) :
    {cut : QueryCut.Cache attached.sheetEntry data.primitives numerics.query selected.query_inside //
      cut.point = sampled.sample} :=
  QueryCut.ofPoint attached.sheetEntry data.primitives numerics.query selected.query_inside
    sampled.sample sampled.sample_eq

/-- Attach the actual numerical cut to its original three-point preparation and retained mesh readings.

One cut operation consumes the supplied Point. One preparation retains the
same polynomial pairs, extended partition, local common mesh and original
vertex locations. One mesh attachment reuses those readings and evaluates
only unmatched mesh vertices on the same anchors and offsets. The result
retains all three original caches; global face meshes and rooted words
require their own geometric certificates.
-/
def meshAtPoint (sampled : PointAcquisition numerics) :
    Σ cut : {cut : QueryCut.Cache attached.sheetEntry data.primitives numerics.query selected.query_inside //
      cut.point = sampled.sample},
    Σ prepared : QueryCut.Cache.Preparation (data := data) cut.val,
      QueryCut.Cache.Preparation.MeshReadings prepared :=
  let cut := metadata.cutAtPoint attached data sampled
  let prepared := QueryCut.Cache.prepare (data := data) cut.val
  let readings := QueryCut.Cache.Preparation.acquireMesh prepared
  ⟨cut, prepared, readings⟩

end GridFragments.Focus.RegularGeometry
end SideQuery.Cache.Numerical
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

end
