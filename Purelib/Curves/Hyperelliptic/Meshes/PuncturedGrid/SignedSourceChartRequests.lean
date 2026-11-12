module
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator
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

open Purelib.Topology.Surface.Sewing

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
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Riemann.Readings

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges
    base.faces}
  {domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Differentials.Basic.Differential genus}

/-- Reverse the two endpoints of the same original triangle source. -/
@[expose] def oppositeSource (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) :
  SewnPrimitiveContacts.SourceEdge mesh.triangles.length :=
  ⟨source.source, source.last, source.first⟩

/-- Every nonloop triangle source or its reversal has the positive triangle orientation. -/
theorem source_orientation (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length)
  (different : source.first ≠ source.last) :
    Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source mesh.triangulation.faces ∨
      Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive
      (SignedSourceChartRequests.oppositeSource source) mesh.triangulation.faces :=
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
inductive SignedSourceChartRequest (source : SewnPrimitiveContacts.SourceEdge
  mesh.triangles.length)
    (differential : Differentials.Basic.Differential genus) (domains :
      Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (target :
      Fraction.Rational) (polynomial : Option (Ordinary curve.polynomial) := none) where
  /-- The comparison on the original positively oriented source. -/ | forward (request :
    TriangleChartRequests.SourceChartRequest source differential domains target polynomial)
  /-- The comparison on the reversal of the original negatively oriented source. -/ | backward (request :
    TriangleChartRequests.SourceChartRequest
    (SignedSourceChartRequests.oppositeSource source) differential domains target polynomial)

constructive_injectivity SignedSourceChartRequest

namespace SignedSourceChartRequest

variable {source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length} {target :
  Fraction.Rational}

/-- Inspect the original nonloop source orientation and retain the corresponding positive-source chart comparison. -/
@[expose] def build (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) (different
  : source.first ≠ source.last)
    (differential : Differentials.Basic.Differential genus) (domains :
      Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (target : Fraction.Rational) (positive : 0 < target)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
      SignedSourceChartRequest source differential domains
      target polynomial :=
  if forward : Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source mesh.triangulation.faces then
    .forward (TriangleChartRequests.SourceChartRequest.build source forward
      differential domains target positive polynomial)
  else .backward (TriangleChartRequests.SourceChartRequest.build
    (SignedSourceChartRequests.oppositeSource source)
    ((SignedSourceChartRequests.source_orientation source different).resolve_left
      forward) differential domains target positive polynomial)

/-- The sufficient stage of the actual retained oriented comparison. -/
@[expose] def index {polynomial : Option (Ordinary curve.polynomial)} :
    SignedSourceChartRequest source differential domains target polynomial → Nat
  | .forward request => request.index
  | .backward request => request.index

/-- Reversing the original source and canonical edge preserves their squared comparison error. -/
private theorem opposite_error (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length)
    (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    Gaussian.Norm.Basic.normSq ((SignedSourceChartRequests.oppositeSource source).increment values -
      CanonicalEdgeValues.edgeValuation mesh values
        ((SignedSourceChartRequests.oppositeSource source).project mesh.triangulation.faces)) =
    Gaussian.Norm.Basic.normSq (source.increment values -
      CanonicalEdgeValues.edgeValuation mesh values (source.project mesh.triangulation.faces)) := by
  have project : (SignedSourceChartRequests.oppositeSource source).project mesh.triangulation.faces =
      (source.project mesh.triangulation.faces).reverse := rfl
  have increment : (SignedSourceChartRequests.oppositeSource source).increment values =
      -source.increment values := by
    unfold SignedSourceChartRequests.oppositeSource SewnPrimitiveContacts.SourceEdge.increment
    ring1
  rewrite [project, CanonicalEdgeValues.edgeValuation_reverse, increment,
    show -source.increment values - -CanonicalEdgeValues.edgeValuation
      mesh values (source.project mesh.triangulation.faces) =
      -(source.increment values - CanonicalEdgeValues.edgeValuation mesh
        values (source.project mesh.triangulation.faces)) by ring1]
  exact Gaussian.Norm.Basic.normSq_neg _

/-- The actual original signed source increment meets its canonical edge comparison target at a sufficient stage. -/
theorem accurate (request : SignedSourceChartRequest source
  differential domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (source.increment readings.values -
      CanonicalEdgeValues.edgeValuation mesh readings.values (source.project
      mesh.triangulation.faces)) < target := by
  cases request with
  | forward request => exact request.accurate later readings
  | backward request =>
      have bound := request.accurate later readings
      exact Eq.mp (congrArg (fun value => value < target) (opposite_error source readings.values)) bound

/-- Retain the actual forward or backward positive-source common comparison cache without changing its orientation. -/
@[expose] def Comparison {polynomial : Option (Ordinary curve.polynomial)}
    (request : SignedSourceChartRequest source differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) : Type _ :=
  match request with
  | .forward request => request.Comparison shared
  | .backward request => request.Comparison shared

/-- Execute the one actual positive-source comparison selected by the retained signed request. -/
def compare {polynomial : Option (Ordinary curve.polynomial)}
    (request : SignedSourceChartRequest source differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) :
    request.Comparison shared :=
  match request with
  | .forward request => request.compare shared
  | .backward request => request.compare shared

/-- The SAME retained common comparison bounds the original signed source discrepancy at every paid stage. -/
theorem comparison_accurate {polynomial : Option (Ordinary curve.polynomial)}
    (request : SignedSourceChartRequest source differential domains target polynomial)
    {stage : Nat} (later : request.index ≤ stage)
    {shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (compared : request.Comparison shared) (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (source.increment readings.values -
      CanonicalEdgeValues.edgeValuation mesh readings.values (source.project mesh.triangulation.faces)) < target := by
  cases request with
  | forward request => exact request.comparison_accurate later compared readings
  | backward request =>
      have bound := request.comparison_accurate later compared readings
      exact Eq.mp (congrArg (fun value => value < target) (opposite_error source readings.values)) bound

end SignedSourceChartRequest

/-- Each actual source occurrence of the retained paired walk has distinct triangle endpoints. -/
theorem paired_sources_nonloop {start finish : Gaussian.Basic.Canonical} {walk : Geometry.Grid.Walks.Walk base.bank.grid
  start finish}
    (paired : Paired.WalkOccurrences.PairedWalk mesh walk) (sheet : Fin 2)
    (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) (member : source ∈
      paired.sources sheet) : source.first ≠ source.last := by
  have projected : source.project mesh.triangulation.faces ∈
      (paired.sources sheet).map (fun source => source.project mesh.triangulation.faces) :=
    List.Map.mem_map_of_mem member
  rw [Paired.WalkOccurrences.PairedWalk.sources_project paired] at projected
  have supported := SkeletonFaceAssignments.indexedWalk_supported mesh walk sheet _
    projected
  have nonloop : (source.project mesh.triangulation.faces).start ≠ (source.project mesh.triangulation.faces).finish :=
    supported.elim
      (Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
      mesh _) (fun member same =>
      Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
      mesh _ member same.symm)
  intro equal
  exact nonloop (congrArg (SewnPrimitiveFaces.corner (mesh.triangulation.faces source.source))
    equal)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests

end
