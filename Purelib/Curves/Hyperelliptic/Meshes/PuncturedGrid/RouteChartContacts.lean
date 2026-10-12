module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPreparation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

public section

/-! Automatic chart changes on one actual indexed edge. Equal positive
sources cancel exactly; opposite incident faces use the existing prepared
source-contact request and retain its shared segment and root owner. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count}

set_option genInjectivity false in
/-- A classification of two source routes on the same retained indexed edge.

Exact source agreement retains its pointwise increment equality. Distinct incident
faces retain their actual positive contact, both source projections and the exact mismatch identity. -/
inductive ChartChange (first last : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) where
  /-- The two original source choices give equal increments for every retained primitive reading. -/ | exact (equal : ∀
    values, first.sourceEdge.increment values = last.sourceEdge.increment values)
  /-- The actual positive source contact with the exact original mismatch identity. -/ | contact (source :
    Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces)
      (positive : Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source.left mesh.triangulation.faces ∧
        Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source.right mesh.triangulation.faces)
      (error_eq : ∀ values, Data.Gaussian.Norm.Basic.normSq (first.sourceEdge.increment values -
        last.sourceEdge.increment values) = source.mismatch values)

constructive_injectivity ChartChange

/-- The original backward route reads the negative of its retained forward source increment. -/
theorem backward_increment (location : Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation mesh.lifts edge.reverse)
    (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    (Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute.backward location).sourceEdge.increment values =
      -location.sourceEdge.increment values := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute.sourceEdge
    Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment
  ring1

/-- Retain the actual opposite incident source occurrences as a contact on their common indexed edge. -/
@[expose] def forwardContact (first : Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation mesh.lifts edge)
    (last : Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation mesh.lifts edge.reverse) :
      Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces :=
  ⟨first.sourceEdge, last.sourceEdge,
    last.sourceEdge_project.trans (congrArg Topology.Polygon.Stokes.OrientedEdge.reverse first.sourceEdge_project).symm⟩

/-- Classify two original routes by their retained source agreement or geometric contact.

The four forward/backward combinations retain the original incident face locations.
Matching sources give exact increment agreement; opposite orientations retain their actual contact. -/
@[expose] def chartChange (first last : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) :
  Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.ChartChange first last := by
  cases first with
  | forward first =>
    cases last with
    | forward last =>
      have same := Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.source_eq_of_project_eq
        mesh (Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
          first)
          (Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
          last)
        (first.sourceEdge_project.trans last.sourceEdge_project.symm)
      exact .exact (fun values => congrArg (fun source => source.increment values) same)
    | backward last =>
      refine .contact (Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.forwardContact first last)
        ⟨(Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
        first),
        (Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive last)⟩
        ?_
      intro values
      rw [Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.backward_increment]
      change Data.Gaussian.Norm.Basic.normSq (first.sourceEdge.increment values - -last.sourceEdge.increment values)
        =
        Data.Gaussian.Norm.Basic.normSq (first.sourceEdge.increment values + last.sourceEdge.increment values)
      exact congrArg Data.Gaussian.Norm.Basic.normSq
        (show first.sourceEdge.increment values - -last.sourceEdge.increment values =
          first.sourceEdge.increment values + last.sourceEdge.increment values by ring1)
  | backward first =>
    cases last with
    | forward last =>
      refine .contact (Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.forwardContact last first)
        ⟨(Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
        last), (Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
        first)⟩ ?_
      intro values
      rw [Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.backward_increment]
      change Data.Gaussian.Norm.Basic.normSq (-first.sourceEdge.increment values - last.sourceEdge.increment values)
        =
        Data.Gaussian.Norm.Basic.normSq (last.sourceEdge.increment values + first.sourceEdge.increment values)
      rw [show -first.sourceEdge.increment values - last.sourceEdge.increment values =
        -(last.sourceEdge.increment values + first.sourceEdge.increment values) by ring1]
      exact Gaussian.Norm.Basic.normSq_neg _
    | backward last =>
      have same := Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.source_eq_of_project_eq
        mesh (Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
          first)
          (Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
          last)
        (first.sourceEdge_project.trans last.sourceEdge_project.symm)
      refine .exact ?_
      intro values
      rw [Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.backward_increment,
        Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.backward_increment, same]

set_option genInjectivity false in
/-- A paid chart-change request between two retained routes on one indexed edge.

Exact source agreement carries the positive target directly. A contact request
retains its geometric source, prepared contact cache, mismatch identity and paid scalar budget. -/
inductive ChartRequest (first last : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) (differential
  : Hyperelliptic.Differentials.Basic.Differential genus)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) (target :
      Fraction.Rational) where
  /-- A positive target and exact agreement of the original source increments. -/ | exact (positive : 0 < target)
      (equal : ∀ values, first.sourceEdge.increment values = last.sourceEdge.increment values)
  /-- The actual original contact preparation, exact mismatch identity and paid scalar budget. -/ | contact (source :
    Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces)
      (error_eq : ∀ values, Data.Gaussian.Norm.Basic.normSq (first.sourceEdge.increment values -
        last.sourceEdge.increment values) = source.mismatch values)
      (prepared : ContactPreparation source differential domains)
      (positive : 0 < target) (budget : prepared.Budget target)

constructive_injectivity ChartRequest

namespace ChartRequest

variable {first last : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} {target :
    Fraction.Rational}

/-- Reuse exact source equality or prepare the actual original contact with its paid scalar budget. -/
@[expose] def ofChange (change : Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.ChartChange first last)
  (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) (target :
      Fraction.Rational) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.ChartRequest first last differential domains target :=
  match change with
  | .exact equal => .exact positive equal
  | .contact source sourcePositive equal =>
    let prepared := ContactPreparation.build mesh source
      sourcePositive differential domains
    .contact source equal prepared positive (prepared.budget target positive)

/-- Classify the two actual original edge routes and prepare their required contact comparison. -/
@[expose] def build (first last : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) (differential :
  Hyperelliptic.Differentials.Basic.Differential genus)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) (target :
      Fraction.Rational) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.ChartRequest first last differential domains target :=
  Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.ChartRequest.ofChange
    (Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.chartChange first last) differential domains target positive

/-- Read zero for exact source agreement or the original contact budget's sufficient stage. -/
@[expose] def index : Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.ChartRequest first last differential domains
  target → Nat
  | .exact _ _ => 0
  | .contact _ _ prepared _ budget => prepared.budgetIndex budget

/-- Every sufficiently late shared primitive bank makes the two original route increments differ by less than the
retained target. -/
theorem accurate (request : Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.ChartRequest first last differential
  domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (first.sourceEdge.increment readings.values - last.sourceEdge.increment
      readings.values) < target := by
  cases request with
  | exact positive equal => rw [equal, sub_self, Gaussian.Norm.Basic.normSq_zero]; exact positive
  | contact source equal prepared positive budget =>
    rw [equal]
    exact prepared.accurate positive budget later readings

end ChartRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts

end
