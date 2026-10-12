module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides

open Purelib.Data.Vector

open Purelib.Riemann.Meshes

@[expose] public section

/-! Complete finite classification of ordered regular-face pairs. Failed
adjacency tests retain the exact unequal physical coordinates. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
    {target : Purelib.Data.Rat.Fraction.Rational}
  {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable (request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet
  => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target)

namespace CrossingBank

/-- A proved physical-coordinate obstruction to joining the original faces across a horizontal side. -/
inductive HorizontalObstruction (firstPosition nextPosition : Fin faces.regulars.length) where
  /-- The original faces have unequal lower horizontal span coordinates. -/ | lower :
    faces.regulars[firstPosition.val].cell.box.xLower ≠ faces.regulars[nextPosition.val].cell.box.xLower →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalObstruction firstPosition
    nextPosition
  /-- The original faces have unequal upper horizontal span coordinates. -/ | upper :
    faces.regulars[firstPosition.val].cell.box.xUpper ≠ faces.regulars[nextPosition.val].cell.box.xUpper →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalObstruction firstPosition
    nextPosition
  /-- The original faces have unequal adjoining top and bottom boundary coordinates. -/ | boundary :
    faces.regulars[firstPosition.val].cell.box.yUpper ≠ faces.regulars[nextPosition.val].cell.box.yLower →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalObstruction firstPosition
    nextPosition

set_option genInjectivity false in
/-- The retained horizontal crossing or a specific proved coordinate obstruction for the original ordered face pair. -/
inductive HorizontalOutcome (first : mesh.LocatedFace firstPosition firstSheet)
    (nextPosition : Fin faces.regulars.length) where
  /-- The actual retained horizontal side crossing on the original located source owner. -/ | matched :
    LiftedSides.HorizontalCrossing request first nextPosition false false →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome first nextPosition
  /-- A specific proved obstruction to this original horizontal side match. -/ | separated :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalObstruction (faces := faces) firstPosition
    nextPosition → Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome first
    nextPosition

constructive_injectivity HorizontalOutcome

end CrossingBank

namespace CrossingBank.HorizontalOutcome

/-- Decide the three original horizontal adjacency equalities and retain either the actual crossing or the first proved
coordinate obstruction. -/
def build (first : mesh.LocatedFace firstPosition firstSheet)
    (nextPosition : Fin faces.regulars.length) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome request first nextPosition :=
  if lowerEq : faces.regulars[firstPosition.val].cell.box.xLower = faces.regulars[nextPosition.val].cell.box.xLower then
    if upperEq : faces.regulars[firstPosition.val].cell.box.xUpper = faces.regulars[nextPosition.val].cell.box.xUpper
      then
      if adjacent : faces.regulars[firstPosition.val].cell.box.yUpper = faces.regulars[nextPosition.val].cell.box.yLower
        then
        .matched (HorizontalCrossing.build request first nextPosition lowerEq upperEq adjacent false false)
      else .separated (.boundary adjacent)
    else .separated (.upper upperEq)
  else .separated (.lower lowerEq)

/-- When the three original horizontal adjacency equalities hold, the retained outcome contains an actual crossing. -/
theorem complete {first : mesh.LocatedFace firstPosition firstSheet}
    {nextPosition : Fin faces.regulars.length} (outcome :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome request first nextPosition)
    (lowerEq : faces.regulars[firstPosition.val].cell.box.xLower = faces.regulars[nextPosition.val].cell.box.xLower)
      (upperEq : faces.regulars[firstPosition.val].cell.box.xUpper = faces.regulars[nextPosition.val].cell.box.xUpper)
      (adjacent : faces.regulars[firstPosition.val].cell.box.yUpper = faces.regulars[nextPosition.val].cell.box.yLower)
      :
    ∃ joined, outcome = .matched joined := by
  cases outcome with
  | matched joined => exact ⟨joined, rfl⟩
  | separated obstruction =>
      cases obstruction with
      | lower different => exact (different lowerEq).elim
      | upper different => exact (different upperEq).elim
      | boundary different => exact (different adjacent).elim

end CrossingBank.HorizontalOutcome

namespace CrossingBank

/-- A proved physical-coordinate obstruction to joining the original faces across a vertical side. -/
inductive VerticalObstruction (firstPosition nextPosition : Fin faces.regulars.length) where
  /-- The original faces have unequal lower vertical span coordinates. -/ | lower :
    faces.regulars[firstPosition.val].cell.box.yLower ≠ faces.regulars[nextPosition.val].cell.box.yLower →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalObstruction firstPosition
    nextPosition
  /-- The original faces have unequal upper vertical span coordinates. -/ | upper :
    faces.regulars[firstPosition.val].cell.box.yUpper ≠ faces.regulars[nextPosition.val].cell.box.yUpper →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalObstruction firstPosition
    nextPosition
  /-- The original faces have unequal adjoining right and left boundary coordinates. -/ | boundary :
    faces.regulars[firstPosition.val].cell.box.xUpper ≠ faces.regulars[nextPosition.val].cell.box.xLower →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalObstruction firstPosition
    nextPosition

set_option genInjectivity false in
/-- The retained vertical crossing or a specific proved coordinate obstruction for the original ordered face pair. -/
inductive VerticalOutcome (first : mesh.LocatedFace firstPosition firstSheet)
    (nextPosition : Fin faces.regulars.length) where
  /-- The actual retained vertical side crossing on the original located source owner. -/ | matched :
    LiftedSides.VerticalCrossing request first nextPosition false false →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome first nextPosition
  /-- A specific proved obstruction to this original vertical side match. -/ | separated :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalObstruction (faces := faces) firstPosition
    nextPosition → Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome first
    nextPosition

constructive_injectivity VerticalOutcome

end CrossingBank

namespace CrossingBank.VerticalOutcome

/-- Decide the three original vertical adjacency equalities and retain either the actual crossing or the first proved
coordinate obstruction. -/
def build (first : mesh.LocatedFace firstPosition firstSheet)
    (nextPosition : Fin faces.regulars.length) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome request first nextPosition :=
  if lowerEq : faces.regulars[firstPosition.val].cell.box.yLower = faces.regulars[nextPosition.val].cell.box.yLower then
    if upperEq : faces.regulars[firstPosition.val].cell.box.yUpper = faces.regulars[nextPosition.val].cell.box.yUpper
      then
      if adjacent : faces.regulars[firstPosition.val].cell.box.xUpper = faces.regulars[nextPosition.val].cell.box.xLower
        then
        .matched (VerticalCrossing.build request first nextPosition lowerEq upperEq adjacent false false)
      else .separated (.boundary adjacent)
    else .separated (.upper upperEq)
  else .separated (.lower lowerEq)

/-- When the three original vertical adjacency equalities hold, the retained outcome contains an actual crossing. -/
theorem complete {first : mesh.LocatedFace firstPosition firstSheet}
    {nextPosition : Fin faces.regulars.length} (outcome :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome request first nextPosition)
    (lowerEq : faces.regulars[firstPosition.val].cell.box.yLower = faces.regulars[nextPosition.val].cell.box.yLower)
      (upperEq : faces.regulars[firstPosition.val].cell.box.yUpper = faces.regulars[nextPosition.val].cell.box.yUpper)
      (adjacent : faces.regulars[firstPosition.val].cell.box.xUpper = faces.regulars[nextPosition.val].cell.box.xLower)
      :
    ∃ joined, outcome = .matched joined := by
  cases outcome with
  | matched joined => exact ⟨joined, rfl⟩
  | separated obstruction =>
      cases obstruction with
      | lower different => exact (different lowerEq).elim
      | upper different => exact (different upperEq).elim
      | boundary different => exact (different adjacent).elim

end CrossingBank.VerticalOutcome

set_option genInjectivity false in
/-- The complete finite crossing classification of all original ordered regular-face pairs on both sheets.

Every successful crossing retains its actual located source owner; every failure retains the exact unequal physical
coordinates. -/
structure CrossingBank (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) where
  /-- The actual located source face on each original face position and sheet. -/ sources : Data.Vector.DependentVector
    (fun firstPosition : Fin faces.regulars.length =>
    Data.Vector.DependentVector (fun sheet : Fin 2 => mesh.LocatedFace firstPosition sheet))
  /-- The complete horizontal crossing outcomes for every retained source owner and original destination position. -/
    horizontal : Data.Vector.DependentVector (fun firstPosition : Fin faces.regulars.length =>
    Data.Vector.DependentVector (fun sheet : Fin 2 =>
      Data.Vector.DependentVector (fun nextPosition : Fin faces.regulars.length =>
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome request ((sources.get
          firstPosition).get sheet) nextPosition)))
  /-- The complete vertical crossing outcomes for every retained source owner and original destination position. -/
    vertical : Data.Vector.DependentVector (fun firstPosition : Fin faces.regulars.length =>
    Data.Vector.DependentVector (fun sheet : Fin 2 =>
      Data.Vector.DependentVector (fun nextPosition : Fin faces.regulars.length =>
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome request ((sources.get
          firstPosition).get sheet) nextPosition)))

constructive_injectivity CrossingBank

namespace CrossingBank

/-- Locate every original face on both sheets once and classify all actual ordered horizontal and vertical crossings. -/
def build (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) :
  CrossingBank request mesh := by
  let sources := DependentVector.ofFn (fun firstPosition : Fin faces.regulars.length =>
    DependentVector.ofFn (fun sheet : Fin 2 => mesh.locateFace firstPosition sheet))
  exact ⟨sources,
    DependentVector.ofFn (fun firstPosition => DependentVector.ofFn (fun sheet =>
      DependentVector.ofFn (fun nextPosition =>
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome.build request ((sources.get
          firstPosition).get sheet) nextPosition))),
    DependentVector.ofFn (fun firstPosition => DependentVector.ofFn (fun sheet =>
      DependentVector.ofFn (fun nextPosition =>
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome.build request ((sources.get
          firstPosition).get sheet) nextPosition)))⟩

/-- Every physically adjacent horizontal pair appears as an actual matched crossing in the retained complete bank. -/
theorem horizontal_complete (retained :
  CrossingBank request mesh)
    (firstPosition nextPosition : Fin faces.regulars.length) (sheet : Fin 2)
    (lowerEq : faces.regulars[firstPosition.val].cell.box.xLower = faces.regulars[nextPosition.val].cell.box.xLower)
    (upperEq : faces.regulars[firstPosition.val].cell.box.xUpper = faces.regulars[nextPosition.val].cell.box.xUpper)
    (adjacent : faces.regulars[firstPosition.val].cell.box.yUpper = faces.regulars[nextPosition.val].cell.box.yLower) :
    ∃ joined, ((retained.horizontal.get firstPosition).get sheet).get nextPosition = .matched joined :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome.complete request _ lowerEq upperEq
    adjacent

/-- Every physically adjacent vertical pair appears as an actual matched crossing in the retained complete bank. -/
theorem vertical_complete (retained :
  CrossingBank request mesh)
    (firstPosition nextPosition : Fin faces.regulars.length) (sheet : Fin 2)
    (lowerEq : faces.regulars[firstPosition.val].cell.box.yLower = faces.regulars[nextPosition.val].cell.box.yLower)
    (upperEq : faces.regulars[firstPosition.val].cell.box.yUpper = faces.regulars[nextPosition.val].cell.box.yUpper)
    (adjacent : faces.regulars[firstPosition.val].cell.box.xUpper = faces.regulars[nextPosition.val].cell.box.xLower) :
    ∃ joined, ((retained.vertical.get firstPosition).get sheet).get nextPosition = .matched joined :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome.complete request _ lowerEq upperEq
    adjacent

end CrossingBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
