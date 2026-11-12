module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces

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
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Riemann.Readings

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {edge : OrientedEdge vertices.count}

set_option genInjectivity false in
/-- A classification of two source routes on the same retained indexed edge.

Exact source agreement retains its pointwise increment equality. Distinct incident
faces retain their actual positive contact, both source projections and the exact mismatch identity. -/
inductive ChartChange (first last : MeshPathWalks.EdgeRoute mesh edge) where
  /-- The two original source choices give equal increments for every retained primitive reading. -/ | exact (equal : ∀
    values, first.sourceEdge.increment values = last.sourceEdge.increment values)
  /-- The actual positive source contact with the exact original mismatch identity. -/ | contact (source :
    Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces)
      (positive : Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source.left mesh.triangulation.faces ∧
        Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source.right mesh.triangulation.faces)
      (error_eq : ∀ values, Gaussian.Norm.Basic.normSq (first.sourceEdge.increment values -
        last.sourceEdge.increment values) = source.mismatch values)

constructive_injectivity ChartChange

/-- The original backward route reads the negative of its retained forward source increment. -/
theorem backward_increment (location : Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation mesh.lifts edge.reverse)
    (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    (MeshPathWalks.EdgeRoute.backward location).sourceEdge.increment values =
      -location.sourceEdge.increment values := by
  unfold MeshPathWalks.EdgeRoute.sourceEdge
    Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment
  ring1

/-- Retain the actual opposite incident source occurrences as a contact on their common indexed edge. -/
@[expose] def forwardContact (first : Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation mesh.lifts edge)
    (last : Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation mesh.lifts edge.reverse) :
      Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces :=
  ⟨first.sourceEdge, last.sourceEdge,
    last.sourceEdge_project.trans (congrArg OrientedEdge.reverse first.sourceEdge_project).symm⟩

/-- Classify two original routes by their retained source agreement or geometric contact.

The four forward/backward combinations retain the original incident face locations.
Matching sources give exact increment agreement; opposite orientations retain their actual contact. -/
@[expose] def chartChange (first last : MeshPathWalks.EdgeRoute mesh edge) :
  ChartChange first last := by
  cases first with
  | forward first =>
    cases last with
    | forward last =>
      have same := TriangleSourceUniqueness.LiftedMesh.source_eq_of_project_eq
        mesh (EdgeLocation.sourceEdge_positive
          first)
          (EdgeLocation.sourceEdge_positive
          last)
        (first.sourceEdge_project.trans last.sourceEdge_project.symm)
      exact .exact (fun values => congrArg (fun source => source.increment values) same)
    | backward last =>
      refine .contact (RouteChartContacts.forwardContact first last)
        ⟨(EdgeLocation.sourceEdge_positive
        first),
        (EdgeLocation.sourceEdge_positive last)⟩
        ?_
      intro values
      rw [RouteChartContacts.backward_increment]
      change Gaussian.Norm.Basic.normSq (first.sourceEdge.increment values - -last.sourceEdge.increment values)
        =
        Gaussian.Norm.Basic.normSq (first.sourceEdge.increment values + last.sourceEdge.increment values)
      exact congrArg Gaussian.Norm.Basic.normSq
        (show first.sourceEdge.increment values - -last.sourceEdge.increment values =
          first.sourceEdge.increment values + last.sourceEdge.increment values by ring1)
  | backward first =>
    cases last with
    | forward last =>
      refine .contact (RouteChartContacts.forwardContact last first)
        ⟨(EdgeLocation.sourceEdge_positive
        last), (EdgeLocation.sourceEdge_positive
        first)⟩ ?_
      intro values
      rw [RouteChartContacts.backward_increment]
      change Gaussian.Norm.Basic.normSq (-first.sourceEdge.increment values - last.sourceEdge.increment values)
        =
        Gaussian.Norm.Basic.normSq (last.sourceEdge.increment values + first.sourceEdge.increment values)
      rw [show -first.sourceEdge.increment values - last.sourceEdge.increment values =
        -(last.sourceEdge.increment values + first.sourceEdge.increment values) by ring1]
      exact Gaussian.Norm.Basic.normSq_neg _
    | backward last =>
      have same := TriangleSourceUniqueness.LiftedMesh.source_eq_of_project_eq
        mesh (EdgeLocation.sourceEdge_positive
          first)
          (EdgeLocation.sourceEdge_positive
          last)
        (first.sourceEdge_project.trans last.sourceEdge_project.symm)
      refine .exact ?_
      intro values
      rw [RouteChartContacts.backward_increment,
        RouteChartContacts.backward_increment, same]

set_option genInjectivity false in
/-- A paid chart-change request between two retained routes on one indexed edge.

Exact source agreement carries the positive target directly. A contact request
retains its geometric source, prepared contact cache, mismatch identity and paid scalar budget. -/
inductive ChartRequest (first last : MeshPathWalks.EdgeRoute mesh edge) (differential
  : Differentials.Basic.Differential genus)
    (domains : Face.DomainBanks.FaceDomainBank frames faces.regulars) (target :
      Fraction.Rational) (polynomial : Option (Ordinary curve.polynomial) := none) where
  /-- A positive target and exact agreement of the original source increments. -/ | exact (positive : 0 < target)
      (equal : ∀ values, first.sourceEdge.increment values = last.sourceEdge.increment values)
  /-- The actual original contact preparation, exact mismatch identity and paid scalar budget. -/ | contact (source :
    Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces)
      (error_eq : ∀ values, Gaussian.Norm.Basic.normSq (first.sourceEdge.increment values -
        last.sourceEdge.increment values) = source.mismatch values)
      (prepared : ContactPreparation source differential domains)
      (positive : 0 < target) (budget : prepared.Budget target polynomial)

constructive_injectivity ChartRequest

namespace ChartRequest

variable {first last : MeshPathWalks.EdgeRoute mesh edge} {differential :
  Differentials.Basic.Differential genus}
  {domains : Face.DomainBanks.FaceDomainBank frames faces.regulars} {target :
    Fraction.Rational}

/-- Reuse exact source equality or prepare the actual original contact with its paid scalar budget. -/
@[expose] def ofChange (change : ChartChange first last)
  (differential : Differentials.Basic.Differential genus)
    (domains : Face.DomainBanks.FaceDomainBank frames faces.regulars) (target :
      Fraction.Rational) (positive : 0 < target) (polynomial : Option (Ordinary curve.polynomial) := none) :
    ChartRequest first last differential domains target polynomial :=
  match change with
  | .exact equal => .exact positive equal
  | .contact source sourcePositive equal =>
    let prepared := ContactPreparation.build mesh source
      sourcePositive differential domains
    .contact source equal prepared positive (prepared.budget target positive polynomial)

/-- Classify the two actual original edge routes and prepare their required contact comparison. -/
@[expose] def build (first last : MeshPathWalks.EdgeRoute mesh edge) (differential :
  Differentials.Basic.Differential genus)
    (domains : Face.DomainBanks.FaceDomainBank frames faces.regulars) (target :
      Fraction.Rational) (positive : 0 < target) (polynomial : Option (Ordinary curve.polynomial) := none) :
    ChartRequest first last differential domains target polynomial :=
  ChartRequest.ofChange
    (RouteChartContacts.chartChange first last) differential domains target positive polynomial

/-- Select a new actual budget on the SAME retained route equality or contact preparation.

The original source, mismatch identity and prepared contact are forwarded
unchanged. Only the positive target and its real numerical budget change;
no route classification, root query or contact preparation is repeated.
-/
def rebudget {previous : Fraction.Rational} {previousPolynomial : Option (Ordinary curve.polynomial)}
    (request : ChartRequest first last differential domains previous previousPolynomial)
    (target : Fraction.Rational) (positive : 0 < target)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
    ChartRequest first last differential domains target polynomial :=
  match request with
  | .exact _ equal => .exact positive equal
  | .contact source equal prepared _ _ =>
      .contact source equal prepared positive (prepared.budget target positive polynomial)

/-- Read zero for exact source agreement or the original contact budget's sufficient stage. -/
@[expose] def index {polynomial : Option (Ordinary curve.polynomial)} :
    ChartRequest first last differential domains target polynomial → Nat
  | .exact _ _ => 0
  | .contact _ _ prepared _ budget => prepared.budgetIndex (polynomial := polynomial) budget

/-- Every sufficiently late shared primitive bank makes the two original route increments differ by less than the
retained target. -/
theorem accurate (request : ChartRequest first last differential
  domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (first.sourceEdge.increment readings.values - last.sourceEdge.increment
      readings.values) < target := by
  cases request with
  | exact positive equal => rw [equal, sub_self, Gaussian.Norm.Basic.normSq_zero]; exact positive
  | contact source equal prepared positive budget =>
    rw [equal]
    exact prepared.accurate positive budget later readings

/-- Retain the exact original post-bank contact cache, or the trivial cache for exact route agreement. -/
@[expose] def Comparison {polynomial : Option (Ordinary curve.polynomial)}
    (request : ChartRequest first last differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) : Type _ :=
  match request with
  | .exact _ _ => PUnit
  | .contact _ _ prepared _ budget => prepared.Comparison budget shared

/-- Execute the requested post-bank contact comparison once and retain its original whole common-model cache. -/
def compare {polynomial : Option (Ordinary curve.polynomial)}
    (request : ChartRequest first last differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) :
    request.Comparison shared :=
  match request with
  | .exact _ _ => ⟨⟩
  | .contact _ _ prepared _ budget => prepared.compare budget shared

/-- The actual retained contact comparison bounds the two original route increments at every paid face stage. -/
theorem comparison_accurate {polynomial : Option (Ordinary curve.polynomial)}
    (request : ChartRequest first last differential domains target polynomial)
    {stage : Nat} (later : request.index ≤ stage)
    {shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (compared : request.Comparison shared) (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (first.sourceEdge.increment readings.values -
      last.sourceEdge.increment readings.values) < target := by
  cases request with
  | exact positive equal => rw [equal, sub_self, Gaussian.Norm.Basic.normSq_zero]; exact positive
  | contact source equal prepared positive budget =>
      rewrite [equal]
      exact prepared.comparison_accurate positive budget later compared readings

end ChartRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts

end
