module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.FramedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.FramedPuncturedGrid.HoleAdjacentFace

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Data.Vector

open Purelib.Riemann

@[expose] public section

/-! The physical hole correction is read in actual inward-edge root-sheet order. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection (fourSideHoleCorrection)
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

open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.FramedPuncturedGrid.HoleAdjacentFace (LiftedSide)

set_option genInjectivity false in
/-- The actual root-sheet lifts of all four retained hole-adjacent faces.

Each dependent vector preserves the selected face owner and both original inward-edge sheets. -/
structure HoleSideLifts (lifted : Meshes.LiftedPuncturedGrid base) {hole : Fin base.faces.holes.length}
    (adjacent : HoleAdjacentFaces base (base.faces.holes[hole.val]'hole.isLt)) where
  /-- The two inward-root lifts of the original bottom adjacent face. -/ bottom : Data.Vector.DependentVector (fun sheet
    : Fin 2 => HoleAdjacentFace.LiftedSide adjacent.bottom lifted sheet)
  /-- The two inward-root lifts of the original top adjacent face. -/ top : Data.Vector.DependentVector (fun sheet : Fin
    2 => HoleAdjacentFace.LiftedSide adjacent.top lifted sheet)
  /-- The two inward-root lifts of the original left adjacent face. -/ left : Data.Vector.DependentVector (fun sheet :
    Fin 2 => HoleAdjacentFace.LiftedSide adjacent.left lifted sheet)
  /-- The two inward-root lifts of the original right adjacent face. -/ right : Data.Vector.DependentVector (fun sheet :
    Fin 2 => HoleAdjacentFace.LiftedSide adjacent.right lifted sheet)

constructive_injectivity HoleSideLifts

/-- Construct all four adjacent-face lifts in their original inward-root sheet order. -/
def HoleSideLifts.build (lifted : Meshes.LiftedPuncturedGrid base) {hole : Fin base.faces.holes.length}
    (adjacent : HoleAdjacentFaces base (base.faces.holes[hole.val]'hole.isLt)) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection.HoleSideLifts lifted adjacent :=
  ⟨DependentVector.ofFn (fun sheet => LiftedSide.build adjacent.bottom lifted sheet),
    DependentVector.ofFn (fun sheet => LiftedSide.build adjacent.top lifted sheet),
    DependentVector.ofFn (fun sheet => LiftedSide.build adjacent.left lifted sheet),
    DependentVector.ofFn (fun sheet => LiftedSide.build adjacent.right lifted sheet)⟩

/-- The complete physical hole correction in actual inward-edge root-sheet order.

Signed perimeter terms and both retained source-triangle terms use the selected sheet of each original adjacent-face
lift. -/
def rootedHoleCorrection (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    {hole : Fin base.faces.holes.length} {adjacent : HoleAdjacentFaces base
      (base.faces.holes[hole.val]'hole.isLt)}
    (sides : Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection.HoleSideLifts lifted adjacent) : Gaussian :=
  FiniteSum.Fin.sumFin (fun sheet =>
    ((perimeters.perimeters.get adjacent.left.position).get (sides.left.get sheet).selected.sheet).right -
    ((perimeters.perimeters.get adjacent.right.position).get (sides.right.get sheet).selected.sheet).left -
    (((perimeters.perimeters.get adjacent.bottom.position).get (sides.bottom.get sheet).selected.sheet).top -
      ((perimeters.perimeters.get adjacent.top.position).get (sides.top.get sheet).selected.sheet).bottom) -
    (TriangleReadings.bilinearArea left right (lifted.mesh.triangleIndex adjacent.left.position (sides.left.get
      sheet).selected.sheet false) +
      TriangleReadings.bilinearArea left right (lifted.mesh.triangleIndex adjacent.bottom.position (sides.bottom.get
        sheet).selected.sheet true)))

/-- The rooted hole correction equals the original four-side correction because every side lift enumerates both sheets.
-/
theorem rootedHoleCorrection_eq (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    {hole : Fin base.faces.holes.length} {adjacent : HoleAdjacentFaces base
      (base.faces.holes[hole.val]'hole.isLt)}
    (sides : Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection.HoleSideLifts lifted adjacent) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection.rootedHoleCorrection perimeters left right sides =
      HoleFourSideCorrection.fourSideHoleCorrection perimeters left right adjacent := by
  simp only [Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection.rootedHoleCorrection,
    HoleFourSideCorrection.fourSideHoleCorrection, FiniteSum.Fin.sumFin_sub,
    FiniteSum.Fin.sumFin_add,
    FacePerimeters.sideSum]
  rw [LiftedSide.sum_selected (fun sheet => sides.left.get sheet)
      (fun sheet => ((perimeters.perimeters.get adjacent.left.position).get sheet).right),
    LiftedSide.sum_selected (fun sheet => sides.right.get sheet)
      (fun sheet => ((perimeters.perimeters.get adjacent.right.position).get sheet).left),
    LiftedSide.sum_selected (fun sheet => sides.bottom.get sheet)
      (fun sheet => ((perimeters.perimeters.get adjacent.bottom.position).get sheet).top),
    LiftedSide.sum_selected (fun sheet => sides.top.get sheet)
      (fun sheet => ((perimeters.perimeters.get adjacent.top.position).get sheet).bottom),
    LiftedSide.sum_selected (fun sheet => sides.left.get sheet)
      (fun sheet => TriangleReadings.bilinearArea left right (lifted.mesh.triangleIndex adjacent.left.position sheet
        false)),
    LiftedSide.sum_selected (fun sheet => sides.bottom.get sheet)
      (fun sheet => TriangleReadings.bilinearArea left right (lifted.mesh.triangleIndex adjacent.bottom.position sheet
        true))]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
