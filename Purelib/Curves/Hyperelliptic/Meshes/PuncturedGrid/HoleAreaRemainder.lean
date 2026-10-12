module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes

open Purelib.Riemann.Meshes

@[expose] public section

/-! Hole corrections are signed full side areas minus their endpoint chords. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection (HoleSideLifts rootedHoleCorrection)
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.FramedPuncturedGrid.HoleAdjacentFace (LiftedSide)

/-- The signed area of an actual retained face side minus its endpoint chord. -/
def sideAreaRemainder (perimeters : Matched.FacePerimeters (request := request) cache i j)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side : GridLiftedDualSteps.GridSide) : Gaussian :=
  (match side with
    | .bottom => ((perimeters.perimeters.get position).get sheet).bottom
    | .right => ((perimeters.perimeters.get position).get sheet).right
    | .top => ((perimeters.perimeters.get position).get sheet).top
    | .left => ((perimeters.perimeters.get position).get sheet).left) -
    Numerics.sideChord cache i j position sheet side

/-- The complete signed inward hole remainder in original root-sheet order.

All four adjacent faces retain their selected sheets, and each actual side area is centered by its own endpoint chord.
-/
def holeAreaRemainder (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    {hole : Fin base.faces.holes.length} {adjacent : HoleAdjacentFaces base
      (base.faces.holes[hole.val]'hole.isLt)}
    (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent) : Gaussian :=
  FiniteSum.Fin.sumFin (fun sheet =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters adjacent.left.position
      (sides.left.get sheet).selected.sheet .right -
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters adjacent.right.position
      (sides.right.get sheet).selected.sheet .left -
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters adjacent.bottom.position
      (sides.bottom.get sheet).selected.sheet .top -
      Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters adjacent.top.position
        (sides.top.get sheet).selected.sheet .bottom))

/-- The original rooted hole correction equals the signed sum of its actual side-area remainders. -/
theorem rootedHoleCorrection_eq_remainder (perimeters : Matched.FacePerimeters (request := request)
  cache.normalize i j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    {hole : Fin base.faces.holes.length} {adjacent : HoleAdjacentFaces base
      (base.faces.holes[hole.val]'hole.isLt)}
    (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection.rootedHoleCorrection perimeters left right
      sides = Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.holeAreaRemainder perimeters sides :=
      by
  unfold HoleRootedCorrection.rootedHoleCorrection HoleAreaRemainder.holeAreaRemainder
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  simp only [Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder,
    Numerics.normalized_bottom_chord cache,
    Numerics.normalized_left_chord cache,
    TriangleReadings.normalized_right_chord left right,
    TriangleReadings.normalized_top_chord left right]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
