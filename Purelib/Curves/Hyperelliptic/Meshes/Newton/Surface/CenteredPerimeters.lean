module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Integration.Path.CenteredAreaCombination
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Cached centered samples on the complete face boundary retain their
exact outer endpoint polygon for the global period comparison. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Topology.Polygon.Stokes (edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces (FacePerimeterTraces)

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

/-- The same aligned coefficient combination used by the complete face. -/
def ownerValues (cache : LocalMeshes.Numerics domains stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (position : Fin grid.faces.regulars.length) (owner : RectangularOwnedTriangulation.OwnedVertex ((domains.get
      position).domain sheet).geometry) :=
  SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point

/-- The original aligned coefficient pair read at each actual retained trace vertex owner. -/
def traceValues (cache : LocalMeshes.Numerics domains stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (trace : JoinedTrace.VertexTrace (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain
      sheet).geometry)) :=
  fun vertex => ownerValues cache
    coefficients position (trace.indexed vertex)

/-- Basis values at the identical retained owner, before coefficient combination. -/
def basisValue (cache : LocalMeshes.Numerics domains stage)
    (trace : JoinedTrace.VertexTrace (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain
      sheet).geometry))
    (row : Fin genus) (vertex : Fin (trace.rest.length + 1)) : Gaussian :=
  let owner := trace.indexed vertex
  (cache.atDomain position sheet row).anchors.alignedValue (cache.atDomain position sheet row).offsets
    owner.column owner.row owner.point

/-- The conjugate/direct basis pair read at the identical original retained trace vertex. -/
def pairValues (cache : LocalMeshes.Numerics domains stage)
    (trace : JoinedTrace.VertexTrace (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain
      sheet).geometry))
    (first second : Fin genus) :=
  fun vertex => (⟨Data.Gaussian.Basic.conj
    (basisValue cache trace first
    vertex),
    basisValue cache trace second
      vertex⟩ : Stokes.PrimitivePoint)

/-- A common pairwise bound controls arbitrary coefficient vectors on this actual owned trace. The coefficients do not
enter the refinement request. -/
theorem centered_combination_bound
    (trace : JoinedTrace.VertexTrace (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain
      sheet).geometry))
    (combined : CenteredBilinearPath.Sample
      (traceValues cache coefficients
      trace))
    (pairs : (i j : Fin genus) → CenteredBilinearPath.Sample
      (pairValues cache trace i j))
    {allowance : Fraction.Rational}
    (bounded : ∀ i j, Data.Gaussian.Norm.Basic.normSq (pairs i j).centeredArea ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq combined.centeredArea ≤
      (genus : Fraction.Rational) ^ 2 * Purelib.Riemann.Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients ^ 2 * allowance := by
  have estimate := CenteredAreaCombination.Sample.centeredArea_combination_bound
    (fun row => Data.Gaussian.Basic.conj (coefficients row)) (fun row => coefficients row)
    (fun row vertex => Data.Gaussian.Basic.conj
      (basisValue cache trace row
      vertex))
    (basisValue cache trace) combined
      pairs bounded
  have conjugateNorm := FiniteSum.Fin.sumFin_congr (fun row : Fin genus => Data.Gaussian.Norm.Basic.normSq_conj
    (coefficients row))
  rw [conjugateNorm] at estimate
  have coefficientNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Data.Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
  rw [coefficientNorm] at estimate
  exact estimate.trans_eq (by unfold PreparedObservationCoercivity.coefficientNormSq; ring1)

set_option genInjectivity false in
/-- The four cached centered samples on the complete original face boundary.

Every sample retains its actual owned trace and endpoint correction alongside the centered area. -/
structure Centered (traces : PerimeterTraces.FacePerimeterTraces energy position) (cache : LocalMeshes.Numerics domains
  stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) where
  /-- The cached centered sample on the complete original bottom trace. -/ bottom : CenteredBilinearPath.Sample
    (traceValues cache coefficients
    traces.bottom)
  /-- The cached centered sample on the complete original right trace. -/ right : CenteredBilinearPath.Sample
    (traceValues cache coefficients
    traces.right)
  /-- The cached centered sample on the complete original top trace. -/ top : CenteredBilinearPath.Sample
    (traceValues cache coefficients
    traces.top)
  /-- The cached centered sample on the complete original left trace. -/ left : CenteredBilinearPath.Sample
    (traceValues cache coefficients
    traces.left)

constructive_injectivity Centered

namespace Centered

variable {traces : FacePerimeterTraces energy
  position}

/-- Acquire the four original complete owned boundary traces as centered samples, retaining their actual endpoint terms.
-/
def build (traces : PerimeterTraces.FacePerimeterTraces energy position) (cache : LocalMeshes.Numerics domains stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
      Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache
      coefficients :=
  ⟨CenteredBilinearPath.Sample.build
    (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.traceValues cache coefficients
    traces.bottom),
    CenteredBilinearPath.Sample.build
      (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.traceValues cache coefficients
      traces.right),
    CenteredBilinearPath.Sample.build
      (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.traceValues cache coefficients
      traces.top),
    CenteredBilinearPath.Sample.build
      (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.traceValues cache coefficients
      traces.left)⟩

/-- The actual original bottom trace area splits into its cached centered area and retained endpoint term. -/
theorem bottom_area (samples :
  Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients)
  :
    traces.bottom.area (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues
      cache coefficients position) = samples.bottom.centeredArea + samples.bottom.endpoint :=
  (traces.bottom.indexed_area _).symm.trans (samples.bottom.originalArea_eq.symm.trans samples.bottom.decomposition)

/-- The actual original right trace area splits into its cached centered area and retained endpoint term. -/
theorem right_area (samples : Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered
  traces cache coefficients) :
    traces.right.area (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues
      cache coefficients position) = samples.right.centeredArea + samples.right.endpoint :=
  (traces.right.indexed_area _).symm.trans (samples.right.originalArea_eq.symm.trans samples.right.decomposition)

/-- The actual original top trace area splits into its cached centered area and retained endpoint term. -/
theorem top_area (samples : Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered
  traces cache coefficients) :
    traces.top.area (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues cache
      coefficients position) = samples.top.centeredArea + samples.top.endpoint :=
  (traces.top.indexed_area _).symm.trans (samples.top.originalArea_eq.symm.trans samples.top.decomposition)

/-- The actual original left trace area splits into its cached centered area and retained endpoint term. -/
theorem left_area (samples : Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered
  traces cache coefficients) :
    traces.left.area (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues
      cache coefficients position) = samples.left.centeredArea + samples.left.endpoint :=
  (traces.left.indexed_area _).symm.trans (samples.left.originalArea_eq.symm.trans samples.left.decomposition)

/-- The retained bottom endpoint term is the actual edge area between the original outer face corners. -/
theorem bottom_endpoint (samples :
  Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients)
  (face : FaceAssembly perimeters position) :
    samples.bottom.endpoint = Stokes.edgeArea (face.corners 0 0).lowerLeft (face.corners (Fin.last (PieceIndices.columns
      (partitions.get position))) 0).lowerRight := by
  rw [samples.bottom.endpoint_eq]
  dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.traceValues,
    Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues]
  rw [show traces.bottom.indexed (Fin.last traces.bottom.rest.length) = traces.bottom.last from
    DyadicTrace.indexed_last _ _]
  rw [show traces.bottom.indexed 0 = traces.bottom.first from rfl,
    traces.bottom_last_value face, traces.bottom_first_value face]
  simp only [Stokes.edgeArea, PrimitivePoint.sub]
  ring1

/-- The retained right endpoint term is the actual edge area between the original outer face corners. -/
theorem right_endpoint (samples :
  Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients)
  (face : FaceAssembly perimeters position) :
    samples.right.endpoint = Stokes.edgeArea (face.corners (Fin.last (PieceIndices.columns (partitions.get position)))
      0).lowerRight (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) (Fin.last
      (PieceIndices.rows (partitions.get position)))).upperRight := by
  rw [samples.right.endpoint_eq]
  dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.traceValues,
    Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues]
  rw [show traces.right.indexed (Fin.last traces.right.rest.length) = traces.right.last from
    DyadicTrace.indexed_last _ _]
  rw [show traces.right.indexed 0 = traces.right.first from rfl,
    traces.right_last_value face, traces.right_first_value face]
  simp only [Stokes.edgeArea, PrimitivePoint.sub]
  ring1

/-- The retained top endpoint term is the actual edge area between the original outer face corners. -/
theorem top_endpoint (samples :
  Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients)
  (face : FaceAssembly perimeters position) :
    samples.top.endpoint = Stokes.edgeArea (face.corners 0 (Fin.last (PieceIndices.rows (partitions.get
      position)))).upperLeft (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) (Fin.last
      (PieceIndices.rows (partitions.get position)))).upperRight := by
  rw [samples.top.endpoint_eq]
  dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.traceValues,
    Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues]
  rw [show traces.top.indexed (Fin.last traces.top.rest.length) = traces.top.last from
    DyadicTrace.indexed_last _ _]
  rw [show traces.top.indexed 0 = traces.top.first from rfl,
    traces.top_last_value face, traces.top_first_value face]
  simp only [Stokes.edgeArea, PrimitivePoint.sub]
  ring1

/-- The retained left endpoint term is the actual edge area between the original outer face corners. -/
theorem left_endpoint (samples :
  Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients)
  (face : FaceAssembly perimeters position) :
    samples.left.endpoint = Stokes.edgeArea (face.corners 0 0).lowerLeft (face.corners 0 (Fin.last (PieceIndices.rows
      (partitions.get position)))).upperLeft := by
  rw [samples.left.endpoint_eq]
  dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.traceValues,
    Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues]
  rw [show traces.left.indexed (Fin.last traces.left.rest.length) = traces.left.last from
    DyadicTrace.indexed_last _ _]
  rw [show traces.left.indexed 0 = traces.left.first from rfl,
    traces.left_last_value face, traces.left_first_value face]
  simp only [Stokes.edgeArea, PrimitivePoint.sub]
  ring1

/-- The four endpoint terms form the actual outer corner polygon. -/
theorem endpoint_total (samples :
  Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients)
  (face : FaceAssembly perimeters position) :
    samples.bottom.endpoint + samples.right.endpoint - samples.top.endpoint - samples.left.endpoint =
      BilinearGridBoundary.cornerArea (face.corners 0 0).lowerLeft
        (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) 0).lowerRight
        (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) (Fin.last (PieceIndices.rows
          (partitions.get position)))).upperRight
        (face.corners 0 (Fin.last (PieceIndices.rows (partitions.get position)))).upperLeft := by
  rw [samples.bottom_endpoint face, samples.right_endpoint face, samples.top_endpoint face, samples.left_endpoint face]
  simp only [BilinearGridBoundary.cornerArea, Stokes.edgeArea]
  ring1

/-- No centered side area or corner term is dropped in passing to the coarse face boundary. These are the terms the
global comparison must pay. -/
theorem exterior_eq (samples :
  Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.Centered traces cache coefficients)
  (face : FaceAssembly perimeters position) :
    face.exterior = samples.bottom.centeredArea + samples.right.centeredArea -
      samples.top.centeredArea - samples.left.centeredArea +
      BilinearGridBoundary.cornerArea (face.corners 0 0).lowerLeft
        (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) 0).lowerRight
        (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) (Fin.last (PieceIndices.rows
          (partitions.get position)))).upperRight
        (face.corners 0 (Fin.last (PieceIndices.rows (partitions.get position)))).upperLeft := by
  have boundary := traces.exterior_eq face
  change face.exterior = traces.bottom.area
    (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues cache coefficients
    position) +
    traces.right.area (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues
      cache coefficients position) - traces.top.area
      (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues cache coefficients
      position) -
    traces.left.area (Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters.FacePerimeterTraces.ownerValues
      cache coefficients position) at boundary
  rw [samples.bottom_area, samples.right_area, samples.top_area, samples.left_area] at boundary
  rw [← samples.endpoint_total face]
  exact boundary.trans (by ring1)

end Centered
end FacePerimeterTraces
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
