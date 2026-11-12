module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Topology.Surface.Sewing

public section

/-! Canonical cochain circulation on an actual retained triangle. Its own
three source increments cancel exactly, and all chart changes are requested
before the shared numerical bank is sampled. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleChartRequests

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Topology.Polygon.Stokes
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Riemann.Readings
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- A chart comparison from one positive original triangle source to its canonical edge route.

The retained location certifies the exact projected source, so the comparison controls that source's actual increment.
-/
structure SourceChartRequest (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length)
    (differential : Differentials.Basic.Differential genus) (domains :
      Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (target : Fraction.Rational) (polynomial : Option (Ordinary curve.polynomial) := none) where
  /-- The original source projects to a positive edge. -/ positive :
    Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source mesh.triangulation.faces
  /-- The retained location of that exact projected source. -/ location : Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation
    mesh.lifts (source.project mesh.triangulation.faces)
  /-- The retained location projects to the original source. -/ source_eq : location.sourceEdge = source
  /-- The chart-change request from the actual source route to its canonical route. -/ request :
    RouteChartContacts.ChartRequest (.forward location)
    (CanonicalEdgeValues.orderedRoute mesh (source.project mesh.triangulation.faces)
      (Or.inl (Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member positive)))
    differential domains target polynomial

constructive_injectivity SourceChartRequest

namespace SourceChartRequest

variable {source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length} {target :
  Fraction.Rational}

/-- Locate the original positive source and retain its exact canonical chart comparison. -/
@[expose] def build (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length)
  (sourcePositive : Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source mesh.triangulation.faces)
    (differential : Differentials.Basic.Differential genus) (domains :
      Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (target : Fraction.Rational) (positive : 0 < target)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
      SourceChartRequest source differential domains target polynomial :=
  let location := mesh.locateEdge _ (Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member sourcePositive)
  ⟨sourcePositive, location,
    TriangleSourceUniqueness.LiftedMesh.source_eq_of_project_eq
      mesh (TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
        location) sourcePositive location.sourceEdge_project,
    RouteChartContacts.ChartRequest.build (.forward location)
      (CanonicalEdgeValues.orderedRoute mesh _ (Or.inl
        (Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member sourcePositive))) differential domains target
        positive polynomial⟩

/-- The sufficient stage of the retained chart-change request. -/
@[expose] def index {polynomial : Option (Ordinary curve.polynomial)}
    (request : SourceChartRequest source differential domains target polynomial) : Nat := request.request.index

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleChartRequests.SourceChartRequest in
/-- The actual source increment differs from its canonical edge valuation by at most the requested allowance at a
sufficient stage. -/
theorem accurate (request : SourceChartRequest source
  differential domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (source.increment readings.values -
      CanonicalEdgeValues.edgeValuation mesh readings.values (source.project
      mesh.triangulation.faces)) < target := by
  have accurate := request.request.accurate later readings
  rw [CanonicalEdgeValues.orderedRoute_value] at accurate
  change Gaussian.Norm.Basic.normSq (request.location.sourceEdge.increment readings.values - _) < target
    at accurate
  rw [request.source_eq] at accurate
  exact accurate

/-- The exact common contact cache retained by the source's actual chart-change request. -/
@[expose] def Comparison {polynomial : Option (Ordinary curve.polynomial)}
    (request : SourceChartRequest source differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) : Type _ :=
  request.request.Comparison shared

/-- Construct the original source's requested common contact cache once from the GIVEN polynomial primitive bank. -/
def compare {polynomial : Option (Ordinary curve.polynomial)}
    (request : SourceChartRequest source differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) :
    request.Comparison shared := request.request.compare shared

/-- The actual retained common comparison controls the original positive source against its canonical edge valuation. -/
theorem comparison_accurate {polynomial : Option (Ordinary curve.polynomial)}
    (request : SourceChartRequest source differential domains target polynomial)
    {stage : Nat} (later : request.index ≤ stage)
    {shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (compared : request.Comparison shared) (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (source.increment readings.values -
      CanonicalEdgeValues.edgeValuation mesh readings.values (source.project mesh.triangulation.faces)) < target := by
  have accurate := request.request.comparison_accurate later compared readings
  rewrite [CanonicalEdgeValues.orderedRoute_value] at accurate
  change Gaussian.Norm.Basic.normSq (request.location.sourceEdge.increment readings.values - _) < target at accurate
  rewrite [request.source_eq] at accurate
  exact accurate

end SourceChartRequest

/-- The original oriented triangle source from the first to second vertex. -/
@[expose] def firstSource (triangle : Fin mesh.triangles.length) :
  SewnPrimitiveContacts.SourceEdge mesh.triangles.length := ⟨triangle, 0, 1⟩

/-- The original oriented triangle source from the second to third vertex. -/
@[expose] def secondSource (triangle : Fin mesh.triangles.length) :
  SewnPrimitiveContacts.SourceEdge mesh.triangles.length := ⟨triangle, 1, 2⟩

/-- The original oriented triangle source from the third to first vertex. -/
@[expose] def thirdSource (triangle : Fin mesh.triangles.length) :
  SewnPrimitiveContacts.SourceEdge mesh.triangles.length := ⟨triangle, 2, 0⟩

set_option genInjectivity false in
/-- Three original source chart comparisons with one paid triangle-boundary allowance.

The retained common index suffices for every side, whose original increments telescope around the triangle. -/
structure TriangleChartRequest (triangle : Fin mesh.triangles.length) (differential :
  Differentials.Basic.Differential genus)
    (domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (target :
      Fraction.Rational) (polynomial : Option (Ordinary curve.polynomial) := none) where
  /-- The requested whole-triangle error is positive. -/ positive : 0 < target
  /-- The retained common local side allowance. -/ allowance : Fraction.Rational
  /-- The local allowance is the original three-term allocation. -/ allowance_eq : allowance =
    Rational.Budget.Aggregate.perTerm target 3
  /-- The retained comparison for the first original side. -/ first :
    SourceChartRequest
    (TriangleChartRequests.firstSource triangle) differential domains allowance polynomial
  /-- The retained comparison for the second original side. -/ second :
    SourceChartRequest
    (TriangleChartRequests.secondSource triangle) differential domains allowance polynomial
  /-- The retained comparison for the closing original side. -/ third :
    SourceChartRequest
    (TriangleChartRequests.thirdSource triangle) differential domains allowance polynomial
  /-- The cached common sufficient comparison stage. -/ index : Nat
  /-- The common stage is exactly the maximum of the three retained request stages. -/ index_eq : index = max
    first.index (max second.index third.index)

constructive_injectivity TriangleChartRequest

namespace TriangleChartRequest

variable {triangle : Fin mesh.triangles.length} {target : Fraction.Rational}

/-- Allocate the original triangle target and retain its three actual source comparisons with a common sufficient stage.
-/
@[expose] def build (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) (triangle : Fin
  mesh.triangles.length)
    (differential : Differentials.Basic.Differential genus) (domains :
      Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (target : Fraction.Rational) (positive : 0 < target)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
      TriangleChartRequest triangle differential domains target polynomial
      :=
  let allowance := Rational.Budget.Aggregate.perTerm target 3
  have allowancePositive := Rational.Budget.Aggregate.perTerm_positive positive 3
  let first := SourceChartRequest.build
    (TriangleChartRequests.firstSource triangle) (by exact List.mem_cons_self)
    differential domains allowance allowancePositive polynomial
  let second := SourceChartRequest.build
    (TriangleChartRequests.secondSource triangle) (by
      exact List.mem_cons_of_mem _ List.mem_cons_self)
    differential domains allowance allowancePositive polynomial
  let third := SourceChartRequest.build
    (TriangleChartRequests.thirdSource triangle) (by
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    differential domains allowance allowancePositive polynomial
  ⟨positive, allowance, rfl, first, second, third, max first.index (max second.index third.index), rfl⟩

/-- Three paid original source increments bound the canonical triangle circulation for the SAME supplied readings. -/
private theorem boundary_accurate (triangle : Fin mesh.triangles.length)
    {stage : Nat} {numerator : CoefficientPolynomial}
    {shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains (numerator := numerator)}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh)
    {target allowance : Fraction.Rational} (positive : 0 < target)
    (allowanceEq : allowance = Rational.Budget.Aggregate.perTerm target 3)
    (first : Gaussian.Norm.Basic.normSq
      ((TriangleChartRequests.firstSource triangle).increment readings.values -
        CanonicalEdgeValues.edgeValuation mesh readings.values
          ((TriangleChartRequests.firstSource triangle).project mesh.triangulation.faces)) < allowance)
    (second : Gaussian.Norm.Basic.normSq
      ((TriangleChartRequests.secondSource triangle).increment readings.values -
        CanonicalEdgeValues.edgeValuation mesh readings.values
          ((TriangleChartRequests.secondSource triangle).project mesh.triangulation.faces)) < allowance)
    (third : Gaussian.Norm.Basic.normSq
      ((TriangleChartRequests.thirdSource triangle).increment readings.values -
        CanonicalEdgeValues.edgeValuation mesh readings.values
          ((TriangleChartRequests.thirdSource triangle).project mesh.triangulation.faces)) < allowance) :
    Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values)
      (mesh.triangulation.faces triangle).boundary) < target := by
  let a := (TriangleChartRequests.firstSource triangle).increment readings.values -
    CanonicalEdgeValues.edgeValuation mesh readings.values
    ((TriangleChartRequests.firstSource triangle).project mesh.triangulation.faces)
  let b := (TriangleChartRequests.secondSource triangle).increment readings.values -
    CanonicalEdgeValues.edgeValuation mesh readings.values
    ((TriangleChartRequests.secondSource triangle).project mesh.triangulation.faces)
  let c := (TriangleChartRequests.thirdSource triangle).increment readings.values -
    CanonicalEdgeValues.edgeValuation mesh readings.values
    ((TriangleChartRequests.thirdSource triangle).project mesh.triangulation.faces)
  have equal : SewingRetraction.wordValue
    (CanonicalEdgeValues.edgeValuation mesh readings.values)
    (mesh.triangulation.faces triangle).boundary =
      -(Gaussian.Norm.Sum.Basic.gaussianSum [a, b, c]) := by
    dsimp [a, b, c, TriangleChartRequests.firstSource,
      TriangleChartRequests.secondSource,
      TriangleChartRequests.thirdSource,
      SewnPrimitiveContacts.SourceEdge.increment,
      SewnPrimitiveContacts.SourceEdge.project,
        SewnPrimitiveFaces.corner, SewingRetraction.wordValue,
        OrientedTriangle.boundary, Gaussian.Norm.Sum.Basic.gaussianSum]
    ring1
  rw [equal, Gaussian.Norm.Basic.normSq_neg]
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at first second third
  have sumBound : Gaussian.Norm.Sum.Basic.gaussianNormSqSum [a, b, c] ≤ 3 * allowance := by
    change Gaussian.Basic.Canonical.normSq a + (Gaussian.Basic.Canonical.normSq b + (Gaussian.Basic.Canonical.normSq c +
      0)) ≤ _
    exact (add_le_add first.le (add_le_add second.le (add_le_add third.le le_rfl))).trans_eq (by ring1)
  have bounded := (Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le [a, b, c]).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound (by decide : (0 : Fraction.Rational) ≤ 3))
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  apply bounded.trans_lt
  rw [allowanceEq]
  exact Rational.Budget.Aggregate.count_mul_perTerm_lt positive 3

/-- The canonical triangle boundary has squared norm below the target once all three original source comparisons are
valid. -/
theorem accurate (request : TriangleChartRequest triangle
  differential domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values)
      (mesh.triangulation.faces triangle).boundary) < target := by
  have first := request.first.accurate ((Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)) readings
  have second := request.second.accurate ((Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _
    _).trans (request.index_eq ▸ later))) readings
  have third := request.third.accurate ((Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _ _).trans
    (request.index_eq ▸ later))) readings
  exact boundary_accurate triangle readings request.positive request.allowance_eq first second third

/-- The three exact post-bank common comparison caches in original triangle-side occurrence order. -/
@[expose] def Comparison {polynomial : Option (Ordinary curve.polynomial)}
    (request : TriangleChartRequest triangle differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) : Type _ :=
  request.first.Comparison shared × request.second.Comparison shared × request.third.Comparison shared

/-- Execute each retained side comparison once on the SAME given polynomial primitive bank. -/
def compare {polynomial : Option (Ordinary curve.polynomial)}
    (request : TriangleChartRequest triangle differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) :
    request.Comparison shared :=
  let first := request.first.compare shared
  let second := request.second.compare shared
  let third := request.third.compare shared
  ⟨first, second, third⟩

/-- The three SAME retained common comparisons internally pay the canonical polynomial triangle circulation. -/
theorem comparison_accurate {polynomial : Option (Ordinary curve.polynomial)}
    (request : TriangleChartRequest triangle differential domains target polynomial)
    {stage : Nat} (later : request.index ≤ stage)
    {shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (compared : request.Comparison shared) (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values)
      (mesh.triangulation.faces triangle).boundary) < target := by
  have first := request.first.comparison_accurate
    ((Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)) compared.1 readings
  have second := request.second.comparison_accurate
    ((Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)))
    compared.2.1 readings
  have third := request.third.comparison_accurate
    ((Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)))
    compared.2.2 readings
  exact boundary_accurate triangle readings request.positive request.allowance_eq first second third

end TriangleChartRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleChartRequests

end
