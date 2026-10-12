module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygonRequest
import Purelib.RootIsolation.SquareRoot.Grid.Subdivision.Self
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.Extension

open Purelib.Riemann.Meshes

open Purelib.Riemann.Periods

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

public section

/-! The fine compiler's literal occurrences consume the local triangle
comparison on their retained face positions and arriving sheets. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineOccurrencePolygon

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix
  mix_reverse extract_congr)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
  (ResplitRegularOccurrence)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests (PairedChartAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    LiftedMesh vertices edges base.faces}
  {domains : FaceDomainBank frames
    base.faces.regulars} {i j : Fin genus}

/-- A self-subdivided occurrence has exactly its indexed fine-face area. The occurrence's chosen arriving sheet is
unchanged. -/
theorem self_word_area_eq
    (occurrence : CircuitPartition.ResplitRegularOccurrence (faces := base.faces)
      (CoordinateInclusion.refl base.bank.grid) edges vertices)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse =
      -value edge) :
    RetracingWords.wordArea value occurrence.word = edges.chainArea vertices value
      (base.faces.regulars[occurrence.location.index.val]'occurrence.location.index.isLt).boundary occurrence.sheet :=
        by
  rcases occurrence with ⟨cell, member, ⟨position, face, indexed, same⟩, sheet, word, wordEq⟩
  cases same
  change RetracingWords.wordArea value word = edges.chainArea vertices value
    (base.faces.regulars[position.val]'position.isLt).boundary sheet
  rw [indexed]
  have comparison := Grid.self_resplit_comparison edges vertices
    (fun point member => (BranchCellBank.referenceAt base.bank.toBranchCellBank point member).toLoop)
    face.boundary (face.cell.anchor_mem face.member)
  exact (congrArg (RetracingWords.wordArea value) wordEq).trans (comparison.areas value anti sheet)

/-- The already retained source position supplies the local request; no new face search or replacement period word is
used. -/
theorem triangle_accurate
    (occurrence : CircuitPartition.ResplitRegularOccurrence (faces := base.faces)
      (CoordinateInclusion.refl base.bank.grid) edges vertices)
    (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let sources := LiftedMesh.faceSources mesh occurrence.location.index occurrence.sheet
    let request := PairedChartAreaRequest.build first second sources
      (LiftedMesh.faceSources_nonloop mesh occurrence.location.index occurrence.sheet) error positive
    let threshold := max floor request.index
    floor ≤ threshold ∧ ∀ stage (cache : RegularMeshes.Numerics domains stage)
      (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
        TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh),
      threshold ≤ stage →
      Data.Gaussian.Norm.Basic.normSq (BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea
        (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation mesh left.values)
          (CanonicalEdgeValues.edgeValuation mesh right.values) coefficient)
        occurrence.word) -
        (TriangleReadings.bilinearArea left right (mesh.triangleIndex occurrence.location.index occurrence.sheet false)
          +
          TriangleReadings.bilinearArea left right (mesh.triangleIndex occurrence.location.index occurrence.sheet
            true))) ≤ error := by
  intro sources request threshold
  constructor
  · exact Purelib.Data.Nat.Order.le_max_left _ _
  intro stage cache left right later
  have bound := (PairedPolygonRequest.face_polygon_accurate mesh occurrence.location.index occurrence.sheet first second
    error positive floor).2
    stage cache left right later
  have equal := BilinearPolarization.extract_congr (fun coefficient =>
    self_word_area_eq occurrence
    (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation mesh left.values) (CanonicalEdgeValues.edgeValuation
      mesh right.values) coefficient)
    (BilinearPolarization.mix_reverse _ _ (CanonicalEdgeValues.edgeValuation_reverse mesh left.values)
      (CanonicalEdgeValues.edgeValuation_reverse mesh right.values) coefficient))
  exact (congrArg (fun area => Data.Gaussian.Norm.Basic.normSq (area -
    (TriangleReadings.bilinearArea left right (mesh.triangleIndex occurrence.location.index occurrence.sheet false) +
      TriangleReadings.bilinearArea left right (mesh.triangleIndex occurrence.location.index occurrence.sheet true))))
        equal).trans_le bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineOccurrencePolygon
