module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleChartRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! The actual stem sources may traverse a triangle edge backwards. Reuse
the existing positive-source chart request and its antisymmetric valuation;
do not silently replace a backward occurrence by a positive one. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges
    base.faces}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- Reverse the two endpoints of the same original triangle source. -/
@[expose] def oppositeSource (source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge mesh.triangles.length) :
  Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge mesh.triangles.length :=
  ⟨source.source, source.last, source.first⟩

/-- Every nonloop triangle source or its reversal has the positive triangle orientation. -/
theorem source_orientation (source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge mesh.triangles.length)
  (different : source.first ≠ source.last) :
    Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source mesh.triangulation.faces ∨
      Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive
      (Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests.oppositeSource source) mesh.triangulation.faces :=
      by
  have pairs : ∀ a b : Fin 3, a ≠ b →
      (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨
      (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 1) ∨ (a = 0 ∧ b = 2) := by decide +kernel
  rcases source with ⟨index, first, last⟩
  rcases pairs first last different with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl List.mem_cons_self
  · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact Or.inr List.mem_cons_self
  · exact Or.inr (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

set_option genInjectivity false in
/-- A positive-source chart request retaining the original source's forward or backward orientation.

The backward case compares the reversed source and transports its accuracy through the antisymmetric canonical
valuation. -/
inductive SignedSourceChartRequest (source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge
  mesh.triangles.length)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (target :
      Fraction.Rational) where
  /-- The comparison on the original positively oriented source. -/ | forward (request :
    Hyperelliptic.Meshes.PuncturedGrid.TriangleChartRequests.SourceChartRequest source differential domains target)
  /-- The comparison on the reversal of the original negatively oriented source. -/ | backward (request :
    Hyperelliptic.Meshes.PuncturedGrid.TriangleChartRequests.SourceChartRequest
    (Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests.oppositeSource source) differential domains target)

constructive_injectivity SignedSourceChartRequest

namespace SignedSourceChartRequest

variable {source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge mesh.triangles.length} {target :
  Fraction.Rational}

/-- Inspect the original nonloop source orientation and retain the corresponding positive-source chart comparison. -/
@[expose] def build (source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge mesh.triangles.length) (different
  : source.first ≠ source.last)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (target : Fraction.Rational) (positive : 0 < target) :
      Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests.SignedSourceChartRequest source differential domains
      target :=
  if forward : Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source mesh.triangulation.faces then
    .forward (Hyperelliptic.Meshes.PuncturedGrid.TriangleChartRequests.SourceChartRequest.build source forward
      differential domains target positive)
  else .backward (Hyperelliptic.Meshes.PuncturedGrid.TriangleChartRequests.SourceChartRequest.build
    (Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests.oppositeSource source)
    ((Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests.source_orientation source different).resolve_left
      forward) differential domains target positive)

/-- The sufficient stage of the actual retained oriented comparison. -/
@[expose] def index : Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests.SignedSourceChartRequest source
  differential domains target → Nat
  | .forward request => request.index
  | .backward request => request.index

/-- The actual original signed source increment meets its canonical edge comparison target at a sufficient stage. -/
theorem accurate (request : Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests.SignedSourceChartRequest source
  differential domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (source.increment readings.values -
      Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh readings.values (source.project
      mesh.triangulation.faces)) < target := by
  cases request with
  | forward request => exact request.accurate later readings
  | backward request =>
      have bound := request.accurate later readings
      have project : (Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests.oppositeSource source).project
        mesh.triangulation.faces =
          (source.project mesh.triangulation.faces).reverse := rfl
      have increment : (Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests.oppositeSource source).increment
        readings.values = -source.increment readings.values := by
        unfold Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests.oppositeSource
          Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment
        ring1
      rw [project, Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse, increment,
        show -source.increment readings.values - -Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
          mesh readings.values (source.project mesh.triangulation.faces) =
          -(source.increment readings.values - Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh
            readings.values (source.project mesh.triangulation.faces)) by ring1,
        Gaussian.Norm.Basic.normSq_neg] at bound
      exact bound

end SignedSourceChartRequest

/-- Each actual source occurrence of the retained paired walk has distinct triangle endpoints. -/
theorem paired_sources_nonloop {start finish : Gaussian.Basic.Canonical} {walk : Geometry.Grid.Walks.Walk base.bank.grid
  start finish}
    (paired : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk) (sheet : Fin 2)
    (source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge mesh.triangles.length) (member : source ∈
      paired.sources sheet) : source.first ≠ source.last := by
  have projected : source.project mesh.triangulation.faces ∈
      (paired.sources sheet).map (fun source => source.project mesh.triangulation.faces) :=
    Data.List.Map.mem_map_of_mem member
  rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk.sources_project paired] at projected
  have supported := Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.indexedWalk_supported mesh walk sheet _
    projected
  have nonloop : (source.project mesh.triangulation.faces).start ≠ (source.project mesh.triangulation.faces).finish :=
    supported.elim
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
      mesh _) (fun member same =>
      Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
      mesh _ member same.symm)
  intro equal
  exact nonloop (congrArg (Topology.Surface.Sewing.SewnPrimitiveFaces.corner (mesh.triangulation.faces source.source))
    equal)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests

end
