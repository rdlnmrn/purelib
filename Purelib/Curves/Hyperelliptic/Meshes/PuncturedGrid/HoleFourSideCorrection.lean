module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Riemann.Meshes

@[expose] public section

/-! The full hole correction reads four constructed adjacent regular faces,
with the inward boundary signs and both associated source triangles intact. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection (holeSideValue holeCorrection)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
  {target : Purelib.Data.Rat.Fraction.Rational} {i j : Fin genus} {stage : Nat} {cache :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}

/-- The finite hole-side sum selects the unique retained adjacent regular face. -/
private theorem side_sum (hole : Fin base.faces.holes.length) (side : GridLiftedDualSteps.GridSide)
    (position : Fin base.faces.regulars.length) (values : Fin base.faces.regulars.length →
      Data.Gaussian.Basic.Canonical)
    (matching : side.Matches base.faces.regulars[position.val].cell.box base.faces.holes[hole.val].cell.box) :
    FiniteSum.Fin.sumFin (fun p =>
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeSideValue hole side p (values p)) =
      values position := by
  have equal (p : Fin base.faces.regulars.length) : HoleComponentCorrection.holeSideValue hole side p (values p) =
      if p = position then values p else 0 := by
    unfold HoleComponentCorrection.holeSideValue
    by_cases same : p = position
    · subst p
      rw [if_pos matching, if_pos rfl]
    · have absent : ¬ side.Matches base.faces.regulars[p.val].cell.box base.faces.holes[hole.val].cell.box :=
        fun found => same (HoleSideSelection.hole_side_unique hole p position found matching)
      rw [if_neg absent, if_neg same]
  rw [FiniteSum.Fin.sumFin_congr equal]
  exact FiniteSum.Fin.sumFin_ite_eq position values

/-- The complete correction read from the four actual adjacent regular faces.

The signed inward perimeter terms retain both associated source-triangle contributions on both sheets. -/
def fourSideHoleCorrection (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    {hole : Fin base.faces.holes.length} (adjacent : HoleAdjacentFaces base
      (base.faces.holes[hole.val]'hole.isLt)) : Gaussian :=
  (FacePerimeters.sideSum perimeters .right adjacent.left.position - FacePerimeters.sideSum perimeters .left
    adjacent.right.position -
    (FacePerimeters.sideSum perimeters .top adjacent.bottom.position - FacePerimeters.sideSum perimeters .bottom
      adjacent.top.position)) -
  FiniteSum.Fin.sumFin (fun sheet => TriangleReadings.bilinearArea left right (lifted.mesh.triangleIndex
    adjacent.left.position sheet false) +
    TriangleReadings.bilinearArea left right (lifted.mesh.triangleIndex adjacent.bottom.position sheet true))

/-- The original full hole correction equals its four retained adjacent-face readback. -/
theorem holeCorrection_eq_fourSides (perimeters : Matched.FacePerimeters (request := request) cache.normalize i
  j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    (hole : Fin base.faces.holes.length) (adjacent : HoleAdjacentFaces base
      (base.faces.holes[hole.val]'hole.isLt)) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection.holeCorrection perimeters left right hole
      = Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection.fourSideHoleCorrection perimeters left
      right adjacent := by
  unfold HoleComponentCorrection.holeCorrection HoleFourSideCorrection.fourSideHoleCorrection
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection.side_sum hole .right adjacent.left.position _
    adjacent.left.matching.reverse,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection.side_sum hole .left adjacent.right.position _
      adjacent.right.matching.reverse,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection.side_sum hole .top adjacent.bottom.position _
      adjacent.bottom.matching.reverse,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection.side_sum hole .bottom adjacent.top.position _
      adjacent.top.matching.reverse]
  congr 1
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection.side_sum hole .right adjacent.left.position _
    adjacent.left.matching.reverse,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection.side_sum hole .top adjacent.bottom.position _
      adjacent.bottom.matching.reverse]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection
