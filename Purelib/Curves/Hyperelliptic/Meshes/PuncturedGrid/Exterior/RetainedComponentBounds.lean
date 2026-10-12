module
import Purelib.Data.Fin
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalExteriorComponents
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Read the existing retained-component bound on any canonical word or lap. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request
namespace Evaluation

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
open Purelib.Data.List
open Purelib.Topology.Mesh
open Purelib.Topology.Polygon
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (Request)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples (SampledComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid (exteriorBoundaries)
open Purelib.Riemann.Normalization
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {index depth readingIndex floor : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {shared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
    {localTarget localArea : Coordinate}

section AllSurfacePreparation.Request.Evaluation
variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target areaTarget : Coordinate}
  {request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared
    target areaTarget floor}

/-- The existing evaluated request bounds every literal canonical exterior component on its own shared triangle
readings. -/
theorem
  canonical_word_small
    (evaluated : AllSurfacePreparation.Request.Evaluation request sample shared depth readingIndex)
    (canonical : prepared.components.map (fun component => component.program.indexed) = lifted.exteriorBoundaries)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) (readings : TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh)
    (word : List (Stokes.OrientedEdge lifted.vertices.count)) (member : word ∈ lifted.exteriorBoundaries) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (word.map
      (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values))) < target := by
  rw [← canonical] at member
  obtain ⟨component, present, equal⟩ := Map.mem_map.mp member
  have inGroups : component ∈ evaluated.components.groups.map SampledComponent.component :=
    evaluated.components.components_eq.symm ▸ present
  obtain ⟨group, member, same⟩ := Map.mem_map.mp inGroups
  have wordEq := (congrArg (fun component => component.program.indexed) same).trans equal
  have bound := evaluated.canonical_component_small degree evaluated.components group member readings
  rw [wordEq] at bound
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (RetracingWords.sum_map_eq_wordValue
    (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) word)).trans_lt bound

/-- In even degree each one-sheet exterior walk is one of the retained canonical components, including either incoming
sheet. -/
theorem
  canonical_one_lap_small
    (evaluated : AllSurfacePreparation.Request.Evaluation request sample shared depth readingIndex)
    (canonical : prepared.components.map (fun component => component.program.indexed) = lifted.exteriorBoundaries)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) (readings : TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh)
    (sheet : Fin 2) :
    Data.Gaussian.Norm.Basic.normSq (lifted.edges.chainValue lifted.vertices (CanonicalEdgeValues.edgeValuation
      lifted.mesh readings.values)
      base.bank.exterior sheet) < target := by
  have member : lifted.edges.indexedEdges lifted.vertices base.bank.exterior sheet ∈ lifted.exteriorBoundaries := by
    cases shape : curve.degreeShape with
    | odd oddDegree =>
        have impossible : False := by omega
        exact impossible.elim
    | even _ =>
        have sheets : sheet = 0 ∨ sheet = 1 := by
          refine Data.Fin.cases_induction ?_
            (Data.Fin.cases_induction ?_ (fun empty => Fin.elim0 empty)) sheet
          · exact Or.inl rfl
          · exact Or.inr rfl
        rw [exteriorBoundaries, shape]
        rcases sheets with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
  have bound := evaluated.canonical_word_small canonical degree readings _ member
  have readback := RetracingWords.sum_map_eq_wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
    (lifted.edges.indexedEdges lifted.vertices base.bank.exterior sheet)
  exact (congrArg Data.Gaussian.Norm.Basic.normSq readback.symm).trans_lt bound

end AllSurfacePreparation.Request.Evaluation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation
