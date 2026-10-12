module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Integration.Path
open Purelib.Riemann.Meshes.GridLiftedDualSteps
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

/-! Weighted original-corner displacements are the retained triangle-source increments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceIncrementReadback

open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter (cachedIncrement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter (cornerValue)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_neg)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal conjugateDiagonal_sub)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  (sourceForward)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.LiftedMesh (faceSource)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon.TriangleReadings (faceSource_increment)

namespace SharedPerimeter
variable {stage : Nat} (cache :
  Numerics domains stage)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  (readings : (row : Fin genus) →
    TriangleReadings (cache.get row)
    lifted.mesh)

/-- The weighted source on one face reads its original four-corner cache. -/
theorem weighted_faceSource (position : Fin base.faces.regulars.length) (sheet : Fin 2)
    (kind : RectangleEdge.Kind) :
    ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
      (LiftedMesh.faceSource lifted.mesh position sheet kind).increment (readings row).values) =
      (SharedPerimeter.cornerValue (lifted := lifted) cache coefficients position sheet (FaceCorners.quad.edge
        kind).finish).sub
        (SharedPerimeter.cornerValue (lifted := lifted) cache coefficients position sheet (FaceCorners.quad.edge
          kind).start) := by
  change _ = (ConjugatePathReadback.conjugateDiagonal _).sub (ConjugatePathReadback.conjugateDiagonal _)
  rw [← ConjugatePathReadback.conjugateDiagonal_sub, ← FiniteSum.Fin.sumFin_sub]
  apply congrArg ConjugatePathReadback.conjugateDiagonal
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [TriangleReadings.faceSource_increment (readings row)]
  exact mul_sub _ _ _

/-- Negating a Gaussian value negates both coordinates of its conjugate-diagonal primitive point. -/
private theorem diagonal_neg (value : InverseRootPolynomial.Gaussian) :
    ConjugatePathReadback.conjugateDiagonal (-value) = PrimitivePoint.zero.sub (ConjugatePathReadback.conjugateDiagonal
      value) := by
  exact (congrArg ConjugatePathReadback.conjugateDiagonal (zero_sub value).symm).trans
    (ConjugatePathReadback.conjugateDiagonal_sub 0 value)

/-- Negating an original primitive-point difference reverses its endpoints. -/
private theorem reverse_difference (first last : Stokes.PrimitivePoint) :
    PrimitivePoint.zero.sub (last.sub first) = first.sub last := by
  cases first
  cases last
  apply congrArg₂ PrimitivePoint.mk <;> change (0 : InverseRootPolynomial.Gaussian) - (_ - _) = _ <;> ring1

/-- Both traversal choices preserve the signed source on the actual occurrence. -/
theorem weighted_occurrence_source (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
    ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
      occurrence.sideOccurrence.source.increment (readings row).values) =
      let total := SharedPerimeter.cachedIncrement (lifted := lifted) cache coefficients
        occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
      if SurfaceOccurrence.sourceForward occurrence then total else PrimitivePoint.zero.sub total := by
  cases backward : occurrence.sideOccurrence.backward with
  | false =>
    have source : occurrence.sideOccurrence.source =
        LiftedMesh.faceSource lifted.mesh occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
          occurrence.sideOccurrence.side.kind := by
      simp only [SideOccurrence.source, backward, if_neg (by decide : ¬ false = true), -eq_self, -iff_self]
      rfl
    rw [source,
      weighted_faceSource]
    cases side : occurrence.sideOccurrence.side <;>
      simp only [SurfaceOccurrence.sourceForward, side, backward, SharedPerimeter.cachedIncrement, GridSide.kind,
        Bool.not_false, if_neg (by decide : ¬ false = true), if_pos (Eq.refl true), -eq_self, -iff_self]
    all_goals first | rfl | exact
      (reverse_difference
      _ _).symm
  | true =>
    have reversed (row : Fin genus) :
        occurrence.sideOccurrence.source.increment (readings row).values =
          -(LiftedMesh.faceSource lifted.mesh occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
            occurrence.sideOccurrence.side.kind).increment (readings row).values := by
      simp only [SideOccurrence.source, backward, if_pos (Eq.refl true),
        LiftedMesh.faceSource, SourceEdge.increment, -eq_self, -iff_self]
      ring1
    have total : (FiniteSum.Fin.sumFin fun row => coefficients row * occurrence.sideOccurrence.source.increment
      (readings row).values) =
        -(FiniteSum.Fin.sumFin fun row => coefficients row * (LiftedMesh.faceSource lifted.mesh
          occurrence.sideOccurrence.position
          occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side.kind).increment (readings row).values) := by
      rw [← FiniteSum.Fin.sumFin_neg]
      apply FiniteSum.Fin.sumFin_congr
      intro row
      rw [reversed]
      exact mul_neg _ _
    rw [total,
      diagonal_neg,
      weighted_faceSource,
      reverse_difference]
    cases side : occurrence.sideOccurrence.side <;>
      simp only [SurfaceOccurrence.sourceForward, side, backward, SharedPerimeter.cachedIncrement, GridSide.kind,
        Bool.not_true, if_neg (by decide : ¬ false = true), if_pos (Eq.refl true), -eq_self, -iff_self]
    all_goals first | rfl | exact
      (reverse_difference
      _ _).symm

end SharedPerimeter
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceIncrementReadback
