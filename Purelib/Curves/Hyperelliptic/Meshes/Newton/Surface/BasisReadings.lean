module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Batteries.Logic
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters

open Purelib.Data.Vector

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularOwnedTriangulation

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularPointReadings

open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Shared cached basis readings on a retained complete-face side. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces (basisValue pairValues)

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

open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)

section FacePerimeterTraces

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample area)
open _root_.Purelib.Data.Gaussian.Basic (conj)

variable (trace : Purelib.Integration.Path.JoinedTrace.VertexTrace
  (Purelib.Riemann.Integration.RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain
  sheet).geometry))

namespace BasisReadings.FacePerimeterTraces

/-- The original basis point-reading bank on the exact retained trace coordinates. -/
def ReadingRows (cache : LocalMeshes.Numerics domains stage) :=
  Data.Vector.DependentVector (fun row : Fin genus => RectangularPointReadings.PointReadings
    (cache.atDomain position sheet row).anchors (cache.atDomain position sheet row).offsets
    (fun vertex => (trace.indexed vertex).point))

end BasisReadings.FacePerimeterTraces

namespace BasisReadings.FacePerimeterTraces.ReadingRows

/-- Every original basis row retains the identical supplied vector of actual trace vertex owners. -/
def Owned {cache : LocalMeshes.Numerics domains stage} (rows :
  Curves.Hyperelliptic.Meshes.Newton.Surface.BasisReadings.FacePerimeterTraces.ReadingRows trace cache)
    (owners : Data.Vector (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain
      sheet).geometry)
      (trace.rest.length + 1)) : Prop :=
  ∀ row vertex, (rows.get row).owners vertex = owners vertex

end BasisReadings.FacePerimeterTraces.ReadingRows

set_option genInjectivity false in
/-- Every basis row reuses one cached owner vector, and each primitive value is evaluated once in the supplied retained
numerical bank. -/
structure BasisReadings (cache : LocalMeshes.Numerics domains stage) where
  /-- The cached original trace vertex owners shared by every basis row. -/ owners : Data.Vector
    (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry)
    (trace.rest.length + 1)
  /-- Each retained owner is exactly the original trace's indexed vertex. -/ owners_eq : ∀ vertex, owners vertex =
    trace.indexed vertex
  /-- The actual original basis point readings from the supplied numerical bank. -/ rows :
    Curves.Hyperelliptic.Meshes.Newton.Surface.BasisReadings.FacePerimeterTraces.ReadingRows trace cache
  /-- Every basis reading row reuses that same cached original owner vector. -/ owned : rows.Owned trace owners

constructive_injectivity BasisReadings

namespace BasisReadings

variable {trace}

/-- Cache the original trace owner vector once and evaluate each basis primitive once at those exact retained owners. -/
def build (trace : JoinedTrace.VertexTrace (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain
  sheet).geometry))
    (cache : LocalMeshes.Numerics domains stage) :
      BasisReadings trace cache := by
  let owners := Data.Vector.Basic.vectorOfFn (fun vertex => trace.indexed vertex)
  have ownerEq (vertex) : owners vertex = trace.indexed vertex := Data.Vector.Basic.vectorOfFn_apply _ vertex
  let rows : Curves.Hyperelliptic.Meshes.Newton.Surface.BasisReadings.FacePerimeterTraces.ReadingRows trace cache :=
    DependentVector.ofFn fun row =>
    PointReadings.build (cache.atDomain position sheet row).anchors
      (cache.atDomain position sheet row).offsets (fun vertex => (trace.indexed vertex).point) owners
      (fun vertex => congrArg OwnedVertex.point (ownerEq vertex))
  refine ⟨owners, ownerEq, rows, ?_⟩
  intro row vertex
  dsimp only [rows]
  rw [DependentVector.ofFn_get]
  rfl

/-- Every cached basis reading equals the aligned value of its actual original trace owner. -/
theorem value_eq (readings : BasisReadings
  trace cache) (row : Fin genus) (vertex : Fin (trace.rest.length + 1)) :
    (readings.rows.get row).values vertex = FacePerimeterTraces.basisValue cache trace row vertex := by
  rw [(readings.rows.get row).value_eq, readings.owned row vertex, readings.owners_eq vertex]
  rfl

/-- Pointwise equality of the actual finite vertex pairs preserves their complete polygon area. -/
public theorem area_congr {count : Nat} {first last : Fin (count + 1) → Stokes.PrimitivePoint}
    (equal : ∀ vertex, first vertex = last vertex) : CenteredBilinearPath.area first = CenteredBilinearPath.area last :=
      by
  apply FiniteSum.Fin.sumFin_congr
  intro edge
  exact congrArg₂ Stokes.edgeArea (equal edge.castSucc) (equal edge.succ)

/-- Transport the original centered sample across pointwise vertex readback while retaining every cached value and area.
-/
public def sample_readback {count : Nat} {first last : Fin (count + 1) → Stokes.PrimitivePoint}
    (sample : CenteredBilinearPath.Sample first) (equal : ∀ vertex, first vertex = last vertex) :
      CenteredBilinearPath.Sample last :=
  { centered := sample.centered
    centered_eq := fun vertex => (sample.centered_eq vertex).trans (congrArg₂ PrimitivePoint.sub (equal vertex) (equal
      0))
    centeredArea := sample.centeredArea
    centeredArea_eq := sample.centeredArea_eq
    endpoint := sample.endpoint
    endpoint_eq := sample.endpoint_eq.trans (congrArg₂ Stokes.edgeArea (equal 0)
      (congrArg₂ PrimitivePoint.sub (equal (Fin.last count)) (equal 0)))
    originalArea := sample.originalArea
    originalArea_eq := sample.originalArea_eq.trans
      (area_congr
      equal)
    decomposition := sample.decomposition }

/-- Center pair samples from the cached scalar readings, transporting only pointwise certificates to the actual
surface-value specification. -/
def pairSample (readings : BasisReadings
  trace cache) (first second : Fin genus) :
    CenteredBilinearPath.Sample (FacePerimeterTraces.pairValues cache trace first second) :=
  sample_readback
    (CenteredBilinearPath.Sample.build (fun vertex =>
    ⟨conj ((readings.rows.get first).values vertex), (readings.rows.get second).values vertex⟩))
    (fun vertex => congrArg₂ PrimitivePoint.mk (congrArg Data.Gaussian.Basic.conj (readings.value_eq first
      vertex))
      (readings.value_eq second vertex))

/-- Cache all actual conjugate/direct basis-pair centered samples from the retained scalar reading bank. -/
def pairSamples (readings : BasisReadings
  trace cache) :=
  DependentVector.ofFn fun first : Fin genus => DependentVector.ofFn fun second : Fin genus =>
    readings.pairSample first second

end BasisReadings
end FacePerimeterTraces
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
