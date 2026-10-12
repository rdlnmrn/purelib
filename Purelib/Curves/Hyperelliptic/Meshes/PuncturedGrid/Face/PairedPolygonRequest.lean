module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests
import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
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
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

/-! Requested comparison of an actual fine-cell polygon with the two
triangle wedges from its retained corner bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygonRequest

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Data.Rat
open Purelib.Integration.Path

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
open Purelib.Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization (extract_wordArea_mix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests (PairedChartAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh : LiftedMesh vertices edges
    base.faces}
  {domains : FaceDomainBank frames
    base.faces.regulars} {i j : Fin genus}

/-- Geometry, magnitudes and the caller's error determine the threshold. No equality between independently acquired edge
sources is assumed. -/
theorem face_polygon_accurate (mesh : LiftedMesh vertices edges base.faces)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2)
    (first : FaceMagnitudeBank domains (standardDifferential i))
    (second : FaceMagnitudeBank domains (standardDifferential j))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let sources := LiftedMesh.faceSources mesh position sheet
    let request := PairedChartAreaRequest.build first second sources (LiftedMesh.faceSources_nonloop mesh position
      sheet) error positive
    let threshold := max floor request.index
    floor ≤ threshold ∧ ∀ stage (cache : RegularMeshes.Numerics domains stage)
      (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
        TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh),
      threshold ≤ stage →
      Data.Gaussian.Norm.Basic.normSq (BilinearPolarization.extract (fun coefficient => edges.chainArea
        vertices
        (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation mesh left.values)
          (CanonicalEdgeValues.edgeValuation mesh right.values) coefficient)
        (base.faces.regulars[position.val]'position.isLt).boundary sheet) -
        (TriangleReadings.bilinearArea left right (mesh.triangleIndex position sheet false) +
          TriangleReadings.bilinearArea left right (mesh.triangleIndex position sheet true))) ≤ error := by
  intro sources request threshold
  constructor
  · exact Data.Nat.Order.le_max_left _ _
  intro stage cache left right later
  let value := fun edge => (⟨edgeValuation mesh left.values edge,
    CanonicalEdgeValues.edgeValuation mesh right.values edge⟩ : PrimitivePoint)
  let word := edges.indexedEdges vertices (base.faces.regulars[position.val]'position.isLt).boundary sheet
  have projected : PairedIncrementArea.area (sources.map (fun source => value (source.project
    mesh.triangulation.faces))) =
      PairedIncrementArea.area (word.map value) := by
    unfold word sources
    rw [← LiftedMesh.faceSources_project mesh position sheet, Data.List.Map.map_map]
    rfl
  let boundComparison := request.realize .paired left right ((Data.Nat.Order.le_max_right _ _).trans later)
  have bound := boundComparison.pay
  rw [boundComparison.residual_readback] at bound
  change Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area
    ((LiftedMesh.faceSources mesh position sheet).map
      (fun source => (⟨source.increment left.values, source.increment right.values⟩ : PrimitivePoint))) -
    PairedIncrementArea.area
      (sources.map (fun source => value (source.project mesh.triangulation.faces)))) ≤ error at bound
  rw [TriangleReadings.faceSources_area left right position sheet, projected] at bound
  have read : BilinearPolarization.extract (fun coefficient => edges.chainArea vertices
      (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation mesh left.values) (CanonicalEdgeValues.edgeValuation
        mesh right.values) coefficient)
      (base.faces.regulars[position.val]'position.isLt).boundary sheet) = PairedIncrementArea.area (word.map value) :=
    extract_wordArea_mix _ _ word
  rw [read]
  have reverse (a b : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Norm.Basic.normSq (a - b) =
    Data.Gaussian.Norm.Basic.normSq (b - a) := by
    rw [show a - b = -(b - a) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
  rw [reverse]
  exact bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygonRequest

end
