module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineOccurrencePolygon
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
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
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.Extension

open Purelib.Riemann.Meshes

open Purelib.Riemann.Periods

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Topology.Mesh

public section

/-! One numerical threshold pays every retained fine-cell polygon, with
its literal position, arriving sheet and finite multiplicity preserved. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FinePolygonAggregate

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
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
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    LiftedMesh vertices edges base.faces}
  {domains : FaceDomainBank frames
    base.faces.regulars} {i j : Fin genus}

/-- An actual retained fine regular-face occurrence on the original grid, including its location, arriving sheet and
word. -/
abbrev FineOccurrence (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank base.bank.grid)
  :=
  CircuitPartition.ResplitRegularOccurrence (faces := base.faces) (CoordinateInclusion.refl base.bank.grid) edges
    vertices

variable {stage : Nat} {cache :
  Numerics domains stage}

/-- The sum of the two original triangle bilinear areas at the retained fine occurrence and sheet. -/
@[expose] def fineTriangleArea (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
  TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (occurrence : FineOccurrence edges vertices) :
      Gaussian :=
  TriangleReadings.bilinearArea left right (mesh.triangleIndex occurrence.location.index occurrence.sheet false) +
    TriangleReadings.bilinearArea left right (mesh.triangleIndex occurrence.location.index occurrence.sheet true)

/-- The actual polarized canonical word area minus the retained fine occurrence's two triangle areas. -/
@[expose] def finePolygonResidual (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
  TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (occurrence : FineOccurrence edges vertices) :
      Gaussian :=
  BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea
    (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation mesh left.values) (CanonicalEdgeValues.edgeValuation
      mesh right.values) coefficient)
    occurrence.word) - fineTriangleArea left right
      occurrence

/-- Every later original cache and pair of triangle readings bounds each retained occurrence residual by the supplied
allowance. -/
@[expose] def FinePolygonsSmallAt (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) (i j : Fin genus)
    (error : Fraction.Rational) (occurrences : List
      (FineOccurrence edges vertices)) (threshold : Nat)
      : Prop :=
  ∀ stage (cache : RegularMeshes.Numerics domains stage)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh),
    threshold ≤ stage → ∀ occurrence ∈ occurrences, Data.Gaussian.Norm.Basic.normSq
      (finePolygonResidual left right occurrence) ≤ error

/-- Only the already certified common stage is needed by later samples; the expensive supplied magnitude banks are
reused for every occurrence. -/
@[expose] def finePolygonRequests (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    (occurrences : List (FineOccurrence edges vertices))
      →
      { threshold : Nat // floor ≤ threshold ∧
        FinePolygonsSmallAt mesh domains i j error
        occurrences threshold }
  | [] => ⟨floor, le_rfl, fun _ _ _ _ _ _ member => (List.not_mem_nil member).elim⟩
  | occurrence :: rest =>
      let sources := LiftedMesh.faceSources mesh occurrence.location.index occurrence.sheet
      let request := PairedChartAreaRequest.build first second sources
        (LiftedMesh.faceSources_nonloop mesh occurrence.location.index occurrence.sheet) error positive
      let headIndex := max floor request.index
      let tail := finePolygonRequests mesh first
        second error positive floor rest
      ⟨max headIndex tail.val, (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _), by
        intro stage cache left right later entry member
        rcases Data.List.Membership.mem_cons.mp member with rfl | member
        · exact (FineOccurrencePolygon.triangle_accurate entry mesh first second error positive floor).2 stage cache
            left right
            ((Data.Nat.Order.le_max_left _ _).trans later)
        · exact tail.property.2 stage cache left right ((Data.Nat.Order.le_max_right _ _).trans later) entry member⟩

/-- Bilinear polarization extraction preserves the pointwise sum of two Gaussian functions. -/
private theorem extract_add (first second : Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
      coefficient => first coefficient + second coefficient) =
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract first +
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract second :=
      by
  unfold BilinearPolarization.extract
  ring1

/-- The sum of the original occurrence residuals is the polarized sum of their actual word areas minus the sum of their
retained triangle areas. -/
private theorem residuals_sum (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
  TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (occurrences : List (FineOccurrence edges vertices))
      :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (occurrences.map
      (finePolygonResidual left right)) =
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
        coefficient => CellBoundary.sumValues (fun occurrence => RetracingWords.wordArea
        (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation mesh left.values)
          (CanonicalEdgeValues.edgeValuation mesh right.values) coefficient)
        occurrence.word) occurrences) - CellBoundary.sumValues
          (fineTriangleArea left right) occurrences := by
  induction occurrences with
  | nil =>
    change (0 : Data.Gaussian.Basic.Canonical) = BilinearPolarization.extract (fun _ => 0) - 0; unfold
      BilinearPolarization.extract; ring1
  | cons occurrence rest ih =>
      change finePolygonResidual left right occurrence +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (rest.map
        (finePolygonResidual left right)) =
        BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea
          (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation mesh left.values)
            (CanonicalEdgeValues.edgeValuation mesh right.values) coefficient)
          occurrence.word + CellBoundary.sumValues (fun other => RetracingWords.wordArea
          (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation mesh left.values)
            (CanonicalEdgeValues.edgeValuation mesh right.values) coefficient)
          other.word) rest) - (fineTriangleArea left
            right occurrence + CellBoundary.sumValues
            (fineTriangleArea left right) rest)
      rw [ih, extract_add]
      unfold finePolygonResidual
      ring1

/-- The complete retained list is compared on one cache and one pair of triangle readings. The budget pays repeated
occurrences rather than dropping them. -/
theorem fine_polygons_sum_accurate (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat)
    (occurrences : List (FineOccurrence edges vertices))
      :
    let request := finePolygonRequests mesh first second
      (Aggregate.perTerm error occurrences.length)
      (Aggregate.perTerm_positive positive _) floor occurrences
    floor ≤ request.val ∧ ∀ stage (cache : RegularMeshes.Numerics domains stage)
      (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
        TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh),
      request.val ≤ stage →
      Data.Gaussian.Norm.Basic.normSq (BilinearPolarization.extract (fun coefficient => CellBoundary.sumValues
        (fun occurrence => RetracingWords.wordArea
        (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation mesh left.values)
          (CanonicalEdgeValues.edgeValuation mesh right.values) coefficient)
        occurrence.word) occurrences) - CellBoundary.sumValues
          (fineTriangleArea left right) occurrences) <
          error := by
  intro request
  refine ⟨request.property.1, ?_⟩
  intro stage cache left right later
  rw [← residuals_sum]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro value member
  obtain ⟨occurrence, present, rfl⟩ := Map.mem_map.mp member
  rw [Data.List.Map.length_map]
  exact request.property.2 stage cache left right later occurrence present

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FinePolygonAggregate
