module
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.JumpPaths
public import Purelib.Topology.Surface.Cut.WordArea
public import Purelib.Topology.Surface.Cut.IntegralPairing
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Cut.IntegralPairing.CutBoundaryWord
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Cut.WordArea.CutBoundaryWord

open Purelib.Topology.Surface.Word

@[expose] public section

/-!
# The computed area matrix of the actual lifted cut boundary

The cyclic word comes from the canonical sewn polygon. Its matrix and the
primitive comparison sample retain exact provenance and all endpoint/error
terms. No standard A/B intersection form is supplied or presumed here.
-/

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open Purelib.Topology.Surface.Word.Pairing

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

/-- Read the cyclic boundary word from the original canonical sewn polygon and its retained edge pairing. -/
def cutBoundaryWord (lifted : LiftedPuncturedGrid base) :
    BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.boundary :=
  ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs

/-- Cache the actual cut-boundary primitive sample with the original polygon anchor. -/
def cutWordAreaSample (lifted : LiftedPuncturedGrid base)
    (primitive : Fin lifted.cutPolygon.patch.cut.count → PrimitivePoint) :
    CutBoundaryWord.AreaSample lifted.cutBoundaryWord primitive (primitive lifted.cutPolygon.patch.cut.anchor) :=
  AreaSample.build lifted.cutBoundaryWord primitive (primitive lifted.cutPolygon.patch.cut.anchor)

/-- Compute the retained integer paired block and remaining interactions of the actual cut boundary word. -/
def cutIntegralPairing (lifted : LiftedPuncturedGrid base) :
  Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord :=
  IntegralPairing.build lifted.cutBoundaryWord

/-- Exact comparison on all actual cut triangles. In particular, no unpaired hole or exterior edge and no compatibility
defect is discarded. -/
theorem cutSurface_eq_word_matrix (lifted : LiftedPuncturedGrid base)
    (primitive : Fin lifted.cutPolygon.patch.cut.count → PrimitivePoint)
    (sample : CutBoundaryWord.AreaSample lifted.cutBoundaryWord primitive (primitive
      lifted.cutPolygon.patch.cut.anchor)) :
    edgeListArea primitive (lifted.cutPolygon.patch.cut.triangles.flatMap OrientedTriangle.boundary) =
      edgeArea (primitive lifted.cutPolygon.patch.cut.anchor)
        (Pairing.linear lifted.cutBoundaryWord.signature.total sample.values) +
      Pairing.contract (fun row column => lifted.cutBoundaryWord.signature.matrix row column) sample.values +
        sample.correction :=
  (lifted.cutPolygon.patch.cut.boundary_area primitive).symm.trans sample.area_eq

/-- The actual cut-triangle primitive area equals its retained boundary-word matrix contraction plus the complete closed
correction. -/
theorem cutSurface_eq_word_matrix_closed (lifted : LiftedPuncturedGrid
  base)
    (primitive : Fin lifted.cutPolygon.patch.cut.count → PrimitivePoint)
    (sample : CutBoundaryWord.AreaSample lifted.cutBoundaryWord primitive (primitive
      lifted.cutPolygon.patch.cut.anchor)) :
    edgeListArea primitive (lifted.cutPolygon.patch.cut.triangles.flatMap OrientedTriangle.boundary) =
      Pairing.contract (fun row column => lifted.cutBoundaryWord.signature.matrix row column) sample.values +
        sample.closedCorrection :=
  (lifted.cutPolygon.patch.cut.boundary_area primitive).symm.trans
    (sample.closed_area_eq lifted.cutPolygon.patch.cut.closed)

/-- The paired integer block is separated from, not substituted for, all physical-boundary interactions and analytic
increment corrections. -/
theorem cutSurface_eq_integral_pairing (lifted : LiftedPuncturedGrid
  base)
    (primitive : Fin lifted.cutPolygon.patch.cut.count → PrimitivePoint)
    (sample : CutBoundaryWord.AreaSample lifted.cutBoundaryWord primitive (primitive
      lifted.cutPolygon.patch.cut.anchor))
    (pairing : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord) :
    edgeListArea primitive (lifted.cutPolygon.patch.cut.triangles.flatMap OrientedTriangle.boundary) =
      2 * Pairing.contract (fun row column => pairing.paired row column) sample.values +
        Pairing.contract (fun row column => pairing.remaining row column) sample.values + sample.closedCorrection := by
  rw [lifted.cutSurface_eq_word_matrix_closed primitive sample, pairing.contract_eq]

end Purelib.Riemann.Meshes.LiftedPuncturedGrid
