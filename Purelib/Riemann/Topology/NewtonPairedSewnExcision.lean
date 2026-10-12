module
import Purelib.Data.List.Map
import Purelib.Data.List.Filter
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Pairwise

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Integration.Surface.Sewn.Selection.Paired

public section

/-! The actual all-hole excision partitions arbitrary paired triangle
areas without rebuilding its selected or remaining geometry. -/

namespace Purelib.Riemann.Topology.NewtonPairedSewnExcision

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision AnnularEntry)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (Sewn SewnAnnulus sourceMask sourceFace)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample (FaceSelection)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint edgeListArea)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceTrace)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}

namespace AllHoleExcision

namespace Sewn

variable {localValues : Fin lifted.mesh.triangles.length →
  Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
  {sample : Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues}
    {excision : Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted}

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
open Purelib.Polynomial in
/-- The retained annuli and remaining faces partition the complete paired cut-boundary area.

The actual all-hole excision supplies disjoint source masks, and the proof reuses the selected and remaining triangle
caches for arbitrary paired primitive values. -/
theorem paired_partition (sewn : Sewn excision sample)
    (primitive : Fin lifted.cutPolygon.patch.cut.count → PrimitivePoint) :
    Geometry.Grid.CellBoundary.sumValues (fun annulus => edgeListArea primitive
      (annulus.selected.triangles.flatMap OrientedTriangle.boundary)) sewn.annuli +
    edgeListArea primitive (sewn.remaining.triangles.flatMap OrientedTriangle.boundary) =
    edgeListArea primitive lifted.cutPolygon.patch.cut.boundary := by
  have separate := excision.disjoint
  rw [← sewn.sources_eq] at separate
  have disjoint := List.Pairwise.pairwise_map.mp separate
  have masks : sewn.annuli.Pairwise (fun first second => ∀ index,
      sourceMask first.source index = true → sourceMask second.source index = true → False) :=
    disjoint.imp (fun separated index => separated (sourceFace lifted index))
  let remaining : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample (fun index =>
    !(sewn.annuli.any (fun annulus => sourceMask annulus.source index))) :=
    { traces := sewn.remaining.traces
      traces_eq := sewn.remaining.traces_eq.trans
        (Data.List.Filter.filter_congr (Item := Surface.Sewing.SewnPrimitiveFaces.FaceTrace localValues
          sample.sewn.values) _ _ (fun trace => congrArg Bool.not
          ((congrArg (fun entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted) =>
            entries.any (fun entry => sourceMask entry trace.source)) sewn.sources_eq.symm).trans
              (Data.List.Map.any_map (Item := SewnAnnulus sample) (Label :=
                Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted)
                (fun annulus : SewnAnnulus sample => annulus.source)
                (fun entry => sourceMask entry trace.source) sewn.annuli))) sample.faces.entries)
      triangles := sewn.remaining.triangles
      triangles_eq := sewn.remaining.triangles_eq
      area := sewn.remaining.area
      area_eq := sewn.remaining.area_eq }
  exact Surface.Sewn.Selection.Paired.paired_family_partition sewn.annuli (fun annulus => sourceMask annulus.source)
    masks (fun annulus => annulus.selected) remaining primitive

end Sewn
end AllHoleExcision
end Purelib.Riemann.Topology.NewtonPairedSewnExcision
