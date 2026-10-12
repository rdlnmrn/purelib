module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedGlobalJump
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedPrimitives
import Purelib.Riemann.Readings.RectangularBoundaryTranslations
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
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
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-! Normalization preserves local face areas with all boundary corrections retained. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

attribute [local congr] FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
  target}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Fraction.Rational} {floor stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

variable {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}

/-- The negative original corner values for the two differentials on a retained face and sheet. -/
@[expose] def faceNormalizationOffset (cache :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage) (i j : Fin genus)
    (position : Fin faces.regulars.length) (sheet : Fin 2) : PrimitivePoint :=
  ⟨-(cache.atDomain position sheet i).corners.values 0, -(cache.atDomain position sheet j).corners.values 0⟩

/-- Normalizing the cached primitives translates each face reading by its retained corner offset. -/
theorem faceValues_normalize (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  domains stage) (i j : Fin genus)
    (position : Fin faces.regulars.length) (sheet : Fin 2) (column row : _) (point : Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet column row
      point =
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache i j position sheet column row
        point).add (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.faceNormalizationOffset cache i j position
        sheet) := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues
  rw [cache.normalize_atDomain, cache.normalize_atDomain,
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.normalize_alignedValue,
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.normalize_alignedValue]
  rfl

namespace FacePerimeters

/-- Translation by the normalization offset preserves the actual local face boundary total. -/
theorem normalized_localTotal_eq
    (original : Matched.FacePerimeters (request := request) cache i j)
    (normalized : Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (position : Fin faces.regulars.length) (sheet : Fin 2) :
    ((normalized.assemblies.get position).get sheet).localTotal =
      ((original.assemblies.get position).get sheet).localTotal := by
  rw [((normalized.assemblies.get position).get sheet).localTotal_eq,
    ((original.assemblies.get position).get sheet).localTotal_eq]
  exact Meshes.RectangularObservationMesh.ObservationPieces.localBoundary_eq_of_translation
    ((request.entries.get sheet).meshes.entries.get position).pieces
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache i j position sheet)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
    (fun _ _ => Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.faceNormalizationOffset cache i j position sheet)
    (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.faceValues_normalize cache i j position sheet) _

/-- The normalized exterior, seam and corner terms sum to the original local face total. -/
theorem normalized_corrected_exterior_eq
    (original : Matched.FacePerimeters (request := request) cache i j)
    (normalized : Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (position : Fin faces.regulars.length) (sheet : Fin 2) :
    ((normalized.assemblies.get position).get sheet).exterior +
      ((normalized.assemblies.get position).get sheet).seams +
      ((normalized.assemblies.get position).get sheet).cornerTotal =
        ((original.assemblies.get position).get sheet).localTotal :=
  ((normalized.assemblies.get position).get sheet).decomposition.symm.trans
    (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.normalized_localTotal_eq
      original normalized position sheet)

/-- Sum all retained local face totals over their original positions and both sheets. -/
@[expose] def localTotalSum (perimeters : Matched.FacePerimeters
  (request := request) cache i j) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet => ((perimeters.assemblies.get position).get
    sheet).localTotal))

/-- Sum the retained face seam corrections over all original positions and sheets. -/
@[expose] def seamTotalSum (perimeters : Matched.FacePerimeters
  (request := request) cache i j) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet => ((perimeters.assemblies.get position).get
    sheet).seams))

/-- Sum the retained face corner corrections over all original positions and sheets. -/
@[expose] def cornerTotalSum (perimeters : Matched.FacePerimeters
  (request := request) cache i j) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet => ((perimeters.assemblies.get position).get
    sheet).cornerTotal))

/-- Normalizing the cached primitives preserves the complete original local-total sum. -/
theorem normalized_localTotalSum_eq
    (original : Matched.FacePerimeters (request := request) cache i j)
    (normalized : Matched.FacePerimeters (request := request)
      cache.normalize i j) :
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum normalized =
      Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original :=
  FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_congr (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.normalized_localTotal_eq
      original normalized position sheet))

/-- The original local-total sum decomposes into the normalized exterior total and all normalized seam and corner
corrections. -/
theorem normalized_total_decomposition
    (original : Matched.FacePerimeters (request := request) cache i j)
    (normalized : Matched.FacePerimeters (request := request)
      cache.normalize i j) :
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original =
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.exteriorTotal normalized +
        Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.seamTotalSum normalized +
        Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.cornerTotalSum normalized := by
  have equal := FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_congr
    (fun sheet => Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.normalized_corrected_exterior_eq
      original normalized position sheet))
  simpa only [FiniteSum.Fin.sumFin_add,
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum,
    Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.exteriorTotal,
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.seamTotalSum,
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.cornerTotalSum, -eq_self, -iff_self] using
      equal.symm

end FacePerimeters
namespace CrossingRequests

/-- The normalized crossing request bounds the corrected original local-total jump.

The expression retains the normalized seam and corner corrections, physical perimeter and cached endpoint jump at the
same sufficient stage. -/
theorem TotalRequest.original_local_jump_bound {retained :
  Matched.CrossingBank request mesh} {target : Fraction.Rational}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent (target / 4) floor)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (original : Matched.FacePerimeters (request := request) cache i j)
    (normalized : Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (later : total.allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
      Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.seamTotalSum normalized -
      Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.cornerTotalSum normalized -
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors -
      samples.endpointJump) ≤ target := by
  have equal : Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.localTotalSum original -
      Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.seamTotalSum normalized -
      Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.cornerTotalSum normalized =
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.exteriorTotal normalized := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas.FacePerimeters.normalized_total_decomposition
      original normalized]
    ring1
  rw [equal]
  exact
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedGlobalJump.CrossingRequests.TotalRequest.normalized_exterior_jump_bound
    total samples normalized neighbors later

end CrossingRequests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas
