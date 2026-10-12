module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedTrace
public import Purelib.Integration.Path.NoisyPathArea
public import Purelib.Integration.Path.TraceLengths
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BasisReadings
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterLengths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonConjugateSideArea
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.BasisReadings

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Geometry

open Purelib.Integration.Path

open Purelib.Integration.Path.TraceLengths

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.State

open Purelib.Topology.Polygon.Stokes

public section

/-! Coefficient-independent requests and conjugate Newton area bounds on
the retained whole-face side traces. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (BasisReadings)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces (pairValues)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2}
  {partitions : SurfacePartitions observations grid} {coarse :
    SurfaceMeshes partitions domains sheet}
  {fixed : Preflights domains sheet} {error :
    Rational}
  {energy : SurfaceRequest partitions coarse fixed error}
  {stage : Nat} {cache : Numerics domains
    stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {assemblies : ExteriorRequest.Assemblies energy
    cache coefficients} {perimeters : Perimeters
    assemblies}
  {position : Fin grid.faces.regulars.length}

open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)

namespace FacePerimeterTraces

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample area)
open _root_.Purelib.Data.Gaussian.Basic (conj)

variable {trace : Purelib.Integration.Path.JoinedTrace.VertexTrace
  (OwnedVertex ((domains.get position).domain
  sheet).geometry)}

open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable (geometry : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry (domains.get
  position).models (fun vertex => (trace.indexed vertex).point))

/-- The complete original basis-pair side comparison requests on the retained whole-face trace geometry. -/
@[expose] def PairRequests (tolerance : Fraction.Rational) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    SideGeometry.Request geometry ((domains.get position).domain sheet)
      (PeriodMatrix.standardDifferential first) (PeriodMatrix.standardDifferential second) tolerance))

/-- Every original retained basis-pair request is available at the supplied common numerical stage. -/
@[expose] def PairRequests.IndexBound {tolerance : Fraction.Rational} (entries :
  PairRequests geometry tolerance) (index
  : Nat) : Prop :=
  ∀ first second, ((entries.get first).get second).index ≤ index

set_option genInjectivity false in
/-- One coefficient-independent comparison schedule for every basis pair on an original whole-face side trace. -/
structure SideRequest (tolerance : Fraction.Rational) where
  /-- The actual original basis-pair request bank on the retained side geometry. -/ entries :
    PairRequests geometry tolerance
  /-- The cached common stage paying every original basis-pair side request. -/ index : Nat
  /-- The common stage dominates every actual retained basis-pair request index. -/ index_ge : entries.IndexBound
    geometry index

constructive_injectivity SideRequest

namespace SideRequest

variable {geometry} {tolerance : Rational}

/-- Prepare the original comparison request for every basis pair and cache their common paid stage. -/
@[expose] def build (geometry : SidePreparation.SideGeometry (domains.get position).models (fun vertex => (trace.indexed
  vertex).point))
    (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
      Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces.SideRequest geometry tolerance :=
      by
  let entries : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces.PairRequests geometry
    tolerance := DependentVector.ofFn fun first => DependentVector.ofFn fun second =>
    SideGeometry.Request.build geometry ((domains.get position).domain sheet)
      (PeriodMatrix.standardDifferential first) (PeriodMatrix.standardDifferential second) tolerance positive
  refine ⟨entries, entries.maximum (fun _ row => row.maximum fun _ request => request.index), ?_⟩
  intro first second
  exact ((entries.get first).get_le_maximum (fun _ request => request.index) second).trans
    (entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.index) first)

/-- The Newton area bound consumes the actual cached basis readings and retained geometric lengths of the complete side.
-/
theorem pair_area_bound {allowance : Fraction.Rational} (budget : NoisyPathArea.LengthErrorBudget trace.rest.length
  allowance)
    (request : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces.SideRequest geometry
      budget.tolerance) (first second : Fin genus)
    {bandAmbient : Rational.Box} {current : Raw.RawWindingState curve.polynomial bandAmbient}
    {profile : NewtonBandBounds.Profile curve.squarefree current.box}
    {leftProfile : NewtonBandDifferentials.DifferentialProfile profile (PeriodMatrix.standardDifferential
      first).exponent}
    {rightProfile : NewtonBandDifferentials.DifferentialProfile profile (PeriodMatrix.standardDifferential
      second).exponent}
    {leftTarget rightTarget density : Fraction.Rational}
    (leftBand : PreparedNewtonBandSamples.PreparedBandRequest leftProfile leftTarget) (rightBand :
      PreparedNewtonBandSamples.PreparedBandRequest rightProfile rightTarget)
    (leftInside : ∀ vertex, leftBand.sample.output.box.Contains (trace.indexed vertex).point)
    (leftSide : ∀ first last, PreparedBoundarySegments.SameSide leftBand.sample.output.box (trace.indexed first).point
      (trace.indexed last).point)
    (rightInside : ∀ vertex, rightBand.sample.output.box.Contains (trace.indexed vertex).point)
    (rightSide : ∀ first last, PreparedBoundarySegments.SameSide rightBand.sample.output.box (trace.indexed first).point
      (trace.indexed last).point)
    (densityNonnegative : 0 ≤ density)
    (leftDensity : PreparedNewtonBandSamples.Sample.preparedDensity leftBand.sample leftProfile leftBand.error ≤
      density)
    (rightDensity : PreparedNewtonBandSamples.Sample.preparedDensity rightBand.sample rightProfile rightBand.error ≤
      density)
    (later : request.index ≤ stage) (readings : BasisReadings trace cache)
    (sample : CenteredBilinearPath.Sample (FacePerimeterTraces.pairValues cache trace first second))
    {coordinate : RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry →
      Fraction.Rational}
    (lengths : VertexTrace.Lengths trace coordinate)
    (movement : ∀ edge : Fin trace.rest.length,
      Data.Gaussian.Norm.Basic.normSq ((trace.indexed edge.succ).point - (trace.indexed edge.castSucc).point) =
        (lengths.values edge)^2) :
    Data.Gaussian.Norm.Basic.normSq sample.centeredArea ≤
      4 * (3 * budget.tolerance + 4 * density * leftBand.sample.output.box.diagonalSq) *
        (4 * density + 3) * (lengths.total + allowance)^2 := by
  have estimate := NewtonConjugateSideArea.conjugate_area_bound budget
    ((request.entries.get first).get second) leftBand rightBand
    leftInside leftSide rightInside rightSide densityNonnegative leftDensity rightDensity
    ((request.index_ge first second).trans later) (cache.atDomain position sheet first) (cache.atDomain position sheet
      second)
    (readings.rows.get first) (readings.rows.get second)
    (values := FacePerimeterTraces.pairValues cache trace first second)
    (fun vertex => congrArg₂ PrimitivePoint.mk (congrArg Data.Gaussian.Basic.conj (readings.value_eq first
      vertex).symm)
      (readings.value_eq second vertex).symm)
    sample (fun edge => lengths.values edge) lengths.nonnegative movement
  rw [← lengths.total_eq] at estimate
  exact estimate

end SideRequest
end FacePerimeterTraces
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
