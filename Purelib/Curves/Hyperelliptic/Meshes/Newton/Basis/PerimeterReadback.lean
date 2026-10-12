module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

@[expose] public section

/-! Read common-basis physical perimeters in the actual Newton energy primitive. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.PerimeterReadback
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Coordinate} {grid :
    NewtonGrid preparation target radius}
  {lifted : LiftedPuncturedGrid grid.punctured} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames grid.faces.regulars}
  {occurrence :
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

open Purelib.Riemann.Normalization.RectangularInverseModels
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal)
variable {stage : Nat}
  {cuts : GridCuts ((domains.get
    occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    ObservationMesh cuts meshBox}

namespace SharedPerimeter
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter (gridValues
  values)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Basic (conj_add conj_mul)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter in
/-- Gaussian conjugation commutes with the original explicit finite sum. -/
private theorem conjugate_sum {count : Nat} (values : Fin count → InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin values) = FiniteSum.Fin.sumFin (fun row =>
      Data.Gaussian.Basic.conj (values row)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [FiniteSum.Fin.sumFin_succ, Data.Gaussian.Basic.conj_add, ih,
      FiniteSum.Fin.sumFin_succ]

/-- Both constructions read the same weighted primitive in the same retained owner. -/
theorem gridValues_eq_seam (cache : RegularMeshes.Numerics domains stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (column row : Fin (((domains.get occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).steps +
      1))
    (point : InverseRootPolynomial.Gaussian) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter.gridValues
      (occurrence := occurrence) cache coefficients column row point =
      Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas.seamValues (sheet := occurrence.sideOccurrence.sheet)
        cache coefficients occurrence.sideOccurrence.position column row point := by
  unfold SharedPerimeter.gridValues SeamAreas.seamValues Integration.Path.ConjugatePathReadback.conjugateDiagonal
  apply congrArg (fun first => (⟨first, _⟩ : Stokes.PrimitivePoint))
  exact (conjugate_sum _).trans
    (FiniteSum.Fin.sumFin_congr (fun basis => Data.Gaussian.Basic.conj_mul _ _))

variable (traces : PerimeterTraces mesh) (cache :
  Numerics domains stage)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  (assembly : ClippedAssembly mesh
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas.seamValues (sheet := occurrence.sideOccurrence.sheet)
    cache coefficients occurrence.sideOccurrence.position))
  (perimeter : assembly.Perimeter)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter
/-- Read the acquired bottom area in the Newton whole-face assembly. -/
theorem bottom_original_area_seam (sample : CenteredBilinearPath.Sample (values (occurrence := occurrence) traces cache
  coefficients .bottom)) :
    sample.originalArea = perimeter.bottom := by
  apply sample.originalArea_eq.trans
  apply Eq.trans _ (traces.bottom_area _ assembly perimeter)
  unfold CenteredBilinearPath.area
  apply FiniteSum.Fin.sumFin_congr
  intro edge
  apply congrArg₂ Stokes.edgeArea
  · exact gridValues_eq_seam cache
      coefficients _ _ _
  · exact gridValues_eq_seam cache
      coefficients _ _ _

/-- Read the acquired right area in the Newton whole-face assembly. -/
theorem right_original_area_seam (sample : CenteredBilinearPath.Sample (values (occurrence := occurrence) traces cache
  coefficients .right)) :
    sample.originalArea = perimeter.right := by
  apply sample.originalArea_eq.trans
  apply Eq.trans _ (traces.right_area _ assembly perimeter)
  unfold CenteredBilinearPath.area
  apply FiniteSum.Fin.sumFin_congr
  intro edge
  apply congrArg₂ Stokes.edgeArea
  · exact gridValues_eq_seam cache
      coefficients _ _ _
  · exact gridValues_eq_seam cache
      coefficients _ _ _

/-- Read the acquired top area in the Newton whole-face assembly. -/
theorem top_original_area_seam (sample : CenteredBilinearPath.Sample (values (occurrence := occurrence) traces cache
  coefficients .top)) :
    sample.originalArea = perimeter.top := by
  apply sample.originalArea_eq.trans
  apply Eq.trans _ (traces.top_area _ assembly perimeter)
  unfold CenteredBilinearPath.area
  apply FiniteSum.Fin.sumFin_congr
  intro edge
  apply congrArg₂ Stokes.edgeArea
  · exact gridValues_eq_seam cache
      coefficients _ _ _
  · exact gridValues_eq_seam cache
      coefficients _ _ _

/-- Read the acquired left area in the Newton whole-face assembly. -/
theorem left_original_area_seam (sample : CenteredBilinearPath.Sample (values (occurrence := occurrence) traces cache
  coefficients .left)) :
    sample.originalArea = perimeter.left := by
  apply sample.originalArea_eq.trans
  apply Eq.trans _ (traces.left_area _ assembly perimeter)
  unfold CenteredBilinearPath.area
  apply FiniteSum.Fin.sumFin_congr
  intro edge
  apply congrArg₂ Stokes.edgeArea
  · exact gridValues_eq_seam cache
      coefficients _ _ _
  · exact gridValues_eq_seam cache
      coefficients _ _ _

end SharedPerimeter
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.PerimeterReadback
