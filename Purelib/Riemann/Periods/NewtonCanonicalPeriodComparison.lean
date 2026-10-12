module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.List.Permutation
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Riemann.Periods.NewtonCanonicalPeriodData

public section

/-! Requested comparisons of the fixed original A/B programs with canonical
resplit words, consuming the retained preparations and one numerical bank. -/
namespace Purelib.Riemann.Periods.NewtonCanonicalPeriodComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered
  anchor)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces (MeshWordReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Periods.NewtonPeriodGeometry (PeriodGeometry)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodData (ACanonicalPreparation BCanonicalPreparation aCanonicalAssigned
  bCanonicalAssigned aCanonicalFaces bCanonicalFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank (FaceScalarBudgets)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords (RouteRequest canonicalRoute)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {differential cycle : Fin genus}
  {target : Rational} {minimum : Nat} {prepared :
    Prepared paired}
  {boundary : PeriodGeometry base.bank.toBranchCellBank}

open Purelib.Approximation.Rational.Budget in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints.ClearGrid.RegularPrimitiveSplits.SheetEntries
  in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes in
open Purelib.Data in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Topology.Surface.Sewing in
/-- Compare the canonical resplit A-word with the original A-period program at paid stages.

The retained scalar, route and chart requests share one numerical bank, while the original fragment schedule supplies
the program stage. Their combined error is strictly below the positive target. -/
theorem ACanonicalPreparation.accurate
    (data : ACanonicalPreparation prepared boundary differential cycle target minimum)
    (positive : 0 < target) (numericalIndex : Nat)
    (cache : RegularMeshes.Numerics boundary.domains numericalIndex)
    (triangles : TrianglePrimitiveReadings.TriangleReadings (cache.get differential) boundary.lifted.mesh)
    (later : data.numericalIndex ≤ numericalIndex) (stage : Nat) (after : data.request.fragments.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation boundary.lifted.mesh triangles.values)
      (aCanonicalAssigned (cycle := cycle) prepared boundary).indexed -
      ((prepared.periodData.aProgram differential cycle).integral.model stage).integralSample) < target := by
  let grid := boundary.grid
  let included := grid.shrunk.included
  let member := lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet)
  let faces := aCanonicalFaces (cycle := cycle) prepared boundary
  let assigned := aCanonicalAssigned (cycle := cycle) prepared boundary
  let part := target / 32
  have partPositive : 0 < part := Field.div_pos_direct positive (by decide +kernel)
  have innerPositive := Aggregate.perTerm_positive partPositive assigned.indexed.length
  let request := data.request
  let sources := data.sources
  let charts := data.charts
  change max (FaceScalarBudgets.index request.scalars) (max data.route.index charts.index) ≤ numericalIndex at later
  have scalarLater := (Data.Nat.Order.le_max_left _ _).trans later
  have retainedRouteLater := (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later)
  have chartLater := (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later)
  have routeLater : (RouteRequest.build (LiftedSources.pieces sources) RouteWords.canonicalRoute part
    partPositive).index ≤ numericalIndex := by
    rw [← data.route_eq]
    exact retainedRouteLater
  let readings := request.readWith innerPositive
    (List.ofFn boundary.lifted.vertices.coordinate ++ boundary.points) (cache.get differential) scalarLater
  have vertices : ∀ vertex, boundary.lifted.vertices.coordinate vertex ∈
      request.points (List.ofFn boundary.lifted.vertices.coordinate ++ boundary.points) := by
    intro vertex
    exact List.mem_append_right _ (List.mem_append_left _ (List.Permutation.ofFn_mem _ vertex))
  let corners := MeshWordReadings.build readings.meshes vertices assigned
  apply PeriodCanonical.period_accurate corners positive charts chartLater
    triangles _ readings.a.value
  · exact (readings.a_accurate stage after).trans_le (Aggregate.perTerm_le partPositive.le _)
  · have routed := PeriodRoutes.routed_accurate sources member included faces part partPositive
      readings.meshes readings.a routeLater (by
        intro piece present
        have ends := LiftedSources.endpoints_mem sources piece present
        exact ⟨List.mem_append_left _ (List.mem_append_left _ ends.1),
          List.mem_append_left _ (List.mem_append_left _ ends.2)⟩)
    rw [corners.value_eq, corners.values_eq]
    exact routed
  · rw [corners.bound_eq, corners.count_eq]
    exact PeriodCanonical.requested_corner_bound partPositive assigned.indexed.length request.pieces

open Purelib.Approximation.Rational.Budget in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints.ClearGrid.RegularPrimitiveSplits.SheetEntries
  in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes in
open Purelib.Data in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Topology.Surface.Sewing in
/-- Compare the canonical resplit B-word with the original B-period program at paid stages.

The retained scalar, route and chart requests share one numerical bank, while the original fragment schedule supplies
the program stage. Their combined error is strictly below the positive target. -/
theorem BCanonicalPreparation.accurate
    (data : BCanonicalPreparation prepared boundary differential cycle target minimum)
    (positive : 0 < target) (numericalIndex : Nat)
    (cache : RegularMeshes.Numerics boundary.domains numericalIndex)
    (triangles : TrianglePrimitiveReadings.TriangleReadings (cache.get differential) boundary.lifted.mesh)
    (later : data.numericalIndex ≤ numericalIndex) (stage : Nat) (after : data.request.fragments.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation boundary.lifted.mesh triangles.values)
      (bCanonicalAssigned (cycle := cycle) prepared boundary).indexed -
      ((prepared.periodData.bProgram differential cycle).integral.model stage).integralSample) < target := by
  let grid := boundary.grid
  let included := grid.shrunk.included
  let member := lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet)
  let faces := bCanonicalFaces (cycle := cycle) prepared boundary
  let assigned := bCanonicalAssigned (cycle := cycle) prepared boundary
  let part := target / 32
  have partPositive : 0 < part := Field.div_pos_direct positive (by decide +kernel)
  have innerPositive := Aggregate.perTerm_positive partPositive assigned.indexed.length
  let request := data.request
  let sources := data.sources
  let charts := data.charts
  change max (FaceScalarBudgets.index request.scalars) (max data.route.index charts.index) ≤ numericalIndex at later
  have scalarLater := (Data.Nat.Order.le_max_left _ _).trans later
  have retainedRouteLater := (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later)
  have chartLater := (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later)
  have routeLater : (RouteRequest.build (LiftedSources.pieces sources) RouteWords.canonicalRoute part
    partPositive).index ≤ numericalIndex := by
    rw [← data.route_eq]
    exact retainedRouteLater
  let readings := request.readWith innerPositive
    (List.ofFn boundary.lifted.vertices.coordinate ++ boundary.points) (cache.get differential) scalarLater
  have vertices : ∀ vertex, boundary.lifted.vertices.coordinate vertex ∈
      request.points (List.ofFn boundary.lifted.vertices.coordinate ++ boundary.points) := by
    intro vertex
    exact List.mem_append_right _ (List.mem_append_left _ (List.Permutation.ofFn_mem _ vertex))
  let corners := MeshWordReadings.build readings.meshes vertices assigned
  apply PeriodCanonical.period_accurate corners positive charts chartLater
    triangles _ readings.b.value
  · exact (readings.b_accurate stage after).trans_le (Aggregate.perTerm_le partPositive.le _)
  · have routed := PeriodRoutes.routed_accurate sources member included faces part partPositive
      readings.meshes readings.b routeLater (by
        intro piece present
        have ends := LiftedSources.endpoints_mem sources piece present
        exact ⟨List.mem_append_left _ (List.mem_append_right _ ends.1),
          List.mem_append_left _ (List.mem_append_right _ ends.2)⟩)
    rw [corners.value_eq, corners.values_eq]
    exact routed
  · rw [corners.bound_eq, corners.count_eq]
    exact PeriodCanonical.requested_corner_bound partPositive assigned.indexed.length request.pieces

end Purelib.Riemann.Periods.NewtonCanonicalPeriodComparison
