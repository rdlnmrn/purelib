module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Cut.ChordJumps
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.JumpPaths
public import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordNormalForm
import Purelib.Topology.Surface.Sewing.NormalFormCycles
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.ProjectedEdgePairs

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest

open Purelib.Topology.Surface.Cut.Chord

open Purelib.Topology.Surface.Cut.Chord.CutBoundaryWord
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.ChordCycleBank
open _root_.Purelib.Topology.Surface.Sewing renaming ChordCycleBank -> ChordCycleBank

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord

@[expose] public section

/-!
# Actual mesh chord jumps for computed handle coordinates

Every coordinate used by the normal form is a paired cut generator, so its
occurrence-preserving chord is constructed without a search-success input.
The sampled jump is supported on the original lifted triangle mesh. This
does not yet identify the transformed jump chains with analytic periods.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Topology.Surface.Word.NormalForm (WordNormalForm)
open Purelib.Topology.Surface.Sewing.CutCycleChains (ClosedCutCycle)
open Purelib.Topology.Surface.Cut.JumpPaths

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- Construct the occurrence-preserving paired cut chord for an actual retained normal-form handle index. -/
def handleChord (lifted : Meshes.LiftedPuncturedGrid base)
    (pairing : Purelib.Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    (normal : NormalForm.WordNormalForm (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature pairing))
    (index : Fin lifted.cutBoundaryWord.alphabet.count)
    (member : index ∈ Handle.Basic.handleIndices normal.pivots) :
    Topology.Surface.Cut.Chord.CutBoundaryWord lifted.cutBoundaryWord index :=
  Chord.build lifted.cutBoundaryWord index (IntegralPairing.normalForm_paired pairing normal index member)

/-- Fixed paired-cycle geometry is constructed without primitive values. Every later sample and analytic period can
retain this exact bank. -/
def cutChordCycleBank (lifted : Meshes.LiftedPuncturedGrid base) :
    Topology.Surface.Sewing.ChordCycleBank lifted.cutBoundaryWord :=
  ChordCycleBank.build lifted.cutBoundaryWord lifted.cutPolygon.patch.cut.closed

/-- Every component of a transformed handle chain uses only actual lifted triangle edges. Integer weights do not
introduce geometric connectors. -/
theorem cutCycle_supported (lifted : Meshes.LiftedPuncturedGrid base)
    (cycle : CutCycleChains.ClosedCutCycle lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutPolygon.patch.cut.boundary.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels))) :
    CutPath.Supported (Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces) cycle.path.surfaceEdges :=
  CutPath.supported_mono cycle.supported (by
    intro edge member
    exact SinglePolygon.boundary_member lifted.cutPolygon (by
      simpa only [lifted.cutPolygon.patch.cut.boundary_eq] using member))

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChordJumps

/-- Every edge of the retained sampled cut chord is supported on the original lifted triangle mesh. -/
theorem chord_sample_supported (lifted : Meshes.LiftedPuncturedGrid base)
    {index : Fin lifted.cutBoundaryWord.alphabet.count} {chord : Topology.Surface.Cut.Chord.CutBoundaryWord
      lifted.cutBoundaryWord index}
    {pairing : Purelib.Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    {primitive : Fin lifted.cutPolygon.patch.cut.count → Stokes.PrimitivePoint}
    {values : Fin lifted.cutBoundaryWord.alphabet.count → Stokes.PrimitivePoint}
    (sample : ChordJumps.Sample chord pairing primitive values) :
    CutPath.Supported (Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces) sample.path.surfaceEdges :=
  CutPath.supported_mono sample.supported (by
    intro edge member
    exact SinglePolygon.boundary_member lifted.cutPolygon (by
      simpa only [lifted.cutPolygon.patch.cut.boundary_eq] using member))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChordJumps

end
