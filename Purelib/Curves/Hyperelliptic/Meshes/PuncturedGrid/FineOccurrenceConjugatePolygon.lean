module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineOccurrencePolygon
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ConjugatePolygonRequest
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
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid.Extension

open Purelib.Riemann.Meshes

open Purelib.Riemann.Periods

open Purelib.Topology.Mesh

public section

/-! Conjugate comparison on each literal fine compiler occurrence. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineOccurrenceConjugatePolygon

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
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

/-- The already retained source position supplies the local request; no new face search or replacement period word is
used. -/
theorem conjugate_triangle_accurate
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
        (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation mesh
          left.values edge)) (CanonicalEdgeValues.edgeValuation mesh right.values) coefficient)
        occurrence.word) -
        (TriangleReadings.conjugateArea left right (mesh.triangleIndex occurrence.location.index occurrence.sheet false)
          +
          TriangleReadings.conjugateArea left right (mesh.triangleIndex occurrence.location.index occurrence.sheet
            true))) ≤ error := by
  intro sources request threshold
  constructor
  · exact Nat.Order.le_max_left _ _
  intro stage cache left right later
  have bound := (ConjugatePolygonRequest.face_conjugate_polygon_accurate mesh occurrence.location.index occurrence.sheet
    first second error positive floor).2
    stage cache left right later
  have equal := BilinearPolarization.extract_congr (fun coefficient => FineOccurrencePolygon.self_word_area_eq
    occurrence
    (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation mesh
      left.values edge)) (CanonicalEdgeValues.edgeValuation mesh right.values) coefficient)
    (BilinearPolarization.mix_reverse _ _ (fun edge => by rw [CanonicalEdgeValues.edgeValuation_reverse]; rfl)
      (CanonicalEdgeValues.edgeValuation_reverse mesh right.values) coefficient))
  exact (congrArg (fun area => Data.Gaussian.Norm.Basic.normSq (area -
    (TriangleReadings.conjugateArea left right (mesh.triangleIndex occurrence.location.index occurrence.sheet false) +
      TriangleReadings.conjugateArea left right (mesh.triangleIndex occurrence.location.index occurrence.sheet true))))
        equal).trans_le bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineOccurrenceConjugatePolygon
