module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels

@[expose] public section

/-! The actual standard-row constructor discharges the route equality, so
the physical standard-cycle comparison has no remaining route-sum residual. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedBoundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings (StandardBoundaryReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings.StandardBoundaryReadings
  (a_routes_value_ofPeriod b_routes_value_ofPeriod)
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_zero)
open Purelib.Riemann.Integration.PreparedRefinementPrograms (rawPeriodDataOfData)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row :
    IntersectionRow lifted integral index}
  {minimum : Nat} {target : Rational} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {extraPoints : List Purelib.Data.Gaussian.Basic.Canonical}

/-- When the retained A reading equals its route sum, the actual physical A boundary approximates the original period
program strictly within the paid target. -/
theorem a_boundary_error_of_routes
    (readings : BoundaryReadings.StandardBoundaryReadings row differential minimum target domains extraPoints)
    (same : readings.a.value = readings.aRoutes.sum)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (row.pair.aFaces.geometry.values fun _ route => route.sourceEdge.increment readings.triangles.values) -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential index).integral.model
        stage).integralSample) < target := by
  have estimate := readings.a_boundary_error stage later
  rw [same, sub_self, Data.Gaussian.Norm.Basic.normSq_zero, mul_zero, zero_add] at estimate
  exact estimate

/-- The actual row constructor pays the full A comparison below the request, with no caller route-transport equality or
residual term. -/
theorem a_boundary_error_ofPeriod
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
    (period : PreparedCycleModels.RootClosedPeriodRow curve)
    (periodEq : period = (RootClosedPeriodBank.ofData curve branches).rows index)
    (readings : BoundaryReadings.StandardBoundaryReadings (IntersectionRow.ofPeriod lifted integral normal index period
      periodEq)
      differential minimum target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum ((IntersectionRow.ofPeriod
      lifted integral normal index period periodEq).pair.aFaces.geometry.values
        fun _ route => route.sourceEdge.increment readings.triangles.values) -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential index).integral.model
        stage).integralSample) < target :=
  a_boundary_error_of_routes readings
    (StandardBoundaryReadings.a_routes_value_ofPeriod normal period periodEq readings) stage later

/-- When the retained B reading equals its route sum, the actual physical B boundary approximates the original period
program strictly within the paid target. -/
theorem b_boundary_error_of_routes
    (readings : BoundaryReadings.StandardBoundaryReadings row differential minimum target domains extraPoints)
    (same : readings.b.value = readings.bRoutes.sum)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (row.pair.bFaces.geometry.values fun _ route => route.sourceEdge.increment readings.triangles.values) -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential index).integral.model
        stage).integralSample) < target := by
  have estimate := readings.b_boundary_error stage later
  rw [same, sub_self, Data.Gaussian.Norm.Basic.normSq_zero, mul_zero, zero_add] at estimate
  exact estimate

/-- The actual row constructor pays the full B comparison below the request, with no caller route-transport equality or
residual term. -/
theorem b_boundary_error_ofPeriod
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
    (period : PreparedCycleModels.RootClosedPeriodRow curve)
    (periodEq : period = (RootClosedPeriodBank.ofData curve branches).rows index)
    (readings : BoundaryReadings.StandardBoundaryReadings (IntersectionRow.ofPeriod lifted integral normal index period
      periodEq)
      differential minimum target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum ((IntersectionRow.ofPeriod
      lifted integral normal index period periodEq).pair.bFaces.geometry.values
        fun _ route => route.sourceEdge.increment readings.triangles.values) -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential index).integral.model
        stage).integralSample) < target :=
  b_boundary_error_of_routes readings
    (StandardBoundaryReadings.b_routes_value_ofPeriod normal period periodEq readings) stage later

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedBoundary
