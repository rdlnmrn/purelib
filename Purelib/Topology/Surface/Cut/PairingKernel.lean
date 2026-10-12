module
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Mesh.CornerWalks
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Chord.Coordinates
import Purelib.Topology.Surface.Chord.PairChordCoverage
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Cut.ChordJumps
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Riemann.Periods.CutPeriodCompleteness
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingTree

/-!
# The actual paired-matrix kernel annihilates every closed cut-surface word

Physical generators are retained until their values are explicitly zero.
Under that condition the actual chord rows evaluate to the cached paired
matrix rows. Vertex gluing and finite telescoping supply completeness.
-/

public section
open Purelib.Algebra.Ring

section

open Purelib.Algebra
open Purelib.Data
open Purelib.Riemann.Periods.CutPeriodCompleteness
open Purelib.Riemann.Periods.CutPeriodCompleteness.SewingForest
open Purelib.Topology.Chain
open Purelib.Topology.Mesh
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates
open Purelib.Topology.Surface.Chord
open Purelib.Topology.Surface.Chord.PairChordCoverage
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Cut.Chord
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewingConnected
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.PairedWord
open Purelib.Topology.Surface.Word.SignedWord

open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Mesh.CornerWalks (VertexConnection)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle triangleEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

namespace Purelib.Topology.Surface.Cut.PairingKernel.CutBoundaryWord.Chord

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges} {index : Fin word.alphabet.count}

/-- A chord coordinate reading reduces to its paired matrix row when physical generator values vanish. -/
theorem coordinates_value_of_physical_zero (chord : Chord word index) (pairing :
  IntegralPairing word)
    (paired : word.alphabet.oneSided index = false) (values : Fin word.alphabet.count → Gaussian.Basic.Canonical)
    (physical : ∀ column, word.alphabet.oneSided column = true → values column = 0) :
    WordCoordinates.combine (Coordinates.coordinates chord).totals values = WordCoordinates.combine (pairing.paired
      index) values := by
  apply FiniteSum.Fin.sumFin_congr
  intro column
  rw [Coordinates.coordinates_eq_row chord pairing paired, IntCast.add, add_mul]
  have physicalTerm : (Pairing.totalAt ((ChordJumps.physicalLetters chord).map SignedGenerator.coefficients) column :
    Gaussian.Basic.Canonical) * values column = 0 := by
    cases side : word.alphabet.oneSided column
    · rw [ChordJumps.physicalLetters, SignedGenerator.total_retain, side]
      exact zero_mul _
    · rw [physical column side, mul_zero]
  rw [physicalTerm, add_zero]

end Purelib.Topology.Surface.Cut.PairingKernel.CutBoundaryWord.Chord

namespace Purelib.Topology.Surface.Cut.PairingKernel.ProjectedEdgePairing

variable {source target : Nat} {labels : Fin source → Fin target} {boundary : List (Stokes.OrientedEdge source)}

open Purelib.Topology.Surface.Cut.PairingKernel.CutBoundaryWord in
/-- Vanishing physical values and paired-row kernel tests annihilate every retained chord reading. -/
theorem chordsZero_of_kernel (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels boundary)
    (integral : IntegralPairing (ProjectedEdgePairing.boundaryWord pairing))
    (value : Stokes.OrientedEdge target → Gaussian.Basic.Canonical)
    (physical : ∀ edge ∈ pairing.boundary, value (OrientedEdge.map labels edge) = 0)
    (kernel : ∀ index, (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = false →
      WordCoordinates.combine (integral.paired index)
        (fun column => value (OrientedEdge.map labels ((ProjectedEdgePairing.boundaryWord pairing).alphabet.generators
          column))) = 0) : ProjectedEdgePairing.ChordsZero pairing value := by
  intro index paired chord
  exact (PairingKernel.CutBoundaryWord.Chord.coordinates_value_of_physical_zero chord integral paired _
    (fun column side => physical _ (ProjectedEdgePairing.oneSided_generator_mem pairing column side))).trans (kernel
      index paired)

end Purelib.Topology.Surface.Cut.PairingKernel.ProjectedEdgePairing

namespace Purelib.Topology.Surface.Cut.PairingKernel.SewingForest.SinglePolygon

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {forest : Sewing.SewingForest faces}

open Purelib.Topology.Surface.Cut.PairingKernel in
/-- Paired-row kernel tests and zero physical readings annihilate each supported closed word.

The finite completeness statement retains unique oriented incidence, nonloop edges and connected vertex stars on the
original mesh. -/
theorem closed_value_zero_of_kernel (polygon : SewingForest.SinglePolygon forest)
    (unique : (Stokes.triangleEdgeOccurrences faces).Nodup)
    (nonloop : ∀ edge ∈ Stokes.triangleEdgeOccurrences faces, edge.start ≠ edge.finish)
    (connected : CornerWalks.VertexConnection faces)
    (pairing : ProjectedEdgePairs.ProjectedEdgePairing polygon.patch.cut.vertexLabels polygon.patch.cut.boundary)
    (integral : IntegralPairing (ProjectedEdgePairing.boundaryWord pairing))
    (value : Stokes.OrientedEdge vertexCount → Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value
      edge)
    (physical : ∀ edge ∈ pairing.boundary, value (OrientedEdge.map polygon.patch.cut.vertexLabels edge) = 0)
    (kernel : ∀ index, (ProjectedEdgePairing.boundaryWord pairing).alphabet.oneSided index = false →
      WordCoordinates.combine (integral.paired index)
        (fun column => value (OrientedEdge.map polygon.patch.cut.vertexLabels ((ProjectedEdgePairing.boundaryWord
          pairing).alphabet.generators column))) = 0)
    {edges : List (Stokes.OrientedEdge vertexCount)} {anchor : Fin vertexCount}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
    (supported : CutPath.Supported polygon.patch.boundary edges) : SewingRetraction.wordValue value edges = 0 :=
  SinglePolygon.closed_value_zero polygon unique nonloop connected pairing value anti physical
    (ProjectedEdgePairing.chordsZero_of_kernel pairing integral value physical kernel) closed supported

end Purelib.Topology.Surface.Cut.PairingKernel.SewingForest.SinglePolygon

end
