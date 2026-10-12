module
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
public import Purelib.Topology.Surface.Word.PairedWord
public import Purelib.Topology.Surface.Boundary.NormalFormArea
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
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
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.Surgery

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Boundary.NormalFormArea.CutBoundaryWord

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord

@[expose] public section

/-!
# Automatic normal form of the lifted cut-boundary pairing

The source is the paired block of the actual sewn polygon. This does not
identify the number of handles with the curve genus, or yet identify their
paths with analytic period programs. Physical-boundary terms remain in the
existing surface-area comparison.
-/

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Topology.Surface.Word.NormalForm (WordNormalForm)
open _root_.Purelib.Topology.Surface.Boundary (NormalFormArea)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

/-- Normalize the original cut-boundary pairing word while retaining its exact signed occurrences and pairing
certificate. -/
def cutWordNormalForm (lifted : LiftedPuncturedGrid base) :
    NormalForm.WordNormalForm (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord) (IntegralPairing.wordSignature
      lifted.cutIntegralPairing) :=
  IntegralPairing.wordNormalForm lifted.cutIntegralPairing

/-- Exact handle-area evaluation of the actual surface. The original physical-boundary and compatibility corrections are
still present. -/
theorem cutSurface_eq_handle_area (lifted : LiftedPuncturedGrid base)
    (primitive : Fin lifted.cutPolygon.patch.cut.count → PrimitivePoint)
    (sample : CutBoundaryWord.AreaSample lifted.cutBoundaryWord primitive (primitive
      lifted.cutPolygon.patch.cut.anchor))
    (pairing : Purelib.Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    (normal : NormalForm.WordNormalForm (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature pairing))
    (evaluated : Topology.Surface.Boundary.NormalFormArea normal.normal sample.values) :
    edgeListArea primitive (lifted.cutPolygon.patch.cut.triangles.flatMap OrientedTriangle.boundary) =
      2 * evaluated.area + Pairing.contract (fun row column => pairing.remaining row column) sample.values +
        sample.closedCorrection :=
  (lifted.cutPolygon.patch.cut.boundary_area primitive).symm.trans
    (AreaSample.closed_handle_area_eq sample pairing normal.normal evaluated lifted.cutPolygon.patch.cut.closed)

end Purelib.Riemann.Meshes.LiftedPuncturedGrid
