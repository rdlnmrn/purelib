module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPerimeters
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSideAreaRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Mesh.IndexedQuadrilaterals
meta import Mathlib.Tactic.Linter.Lint

public section

/-! Materialized requests for every classified pair, with a single certified
late stage obtained from the retained request indices. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest
open Purelib.Data.Vector

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
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
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (CrossingBank)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank (HorizontalOutcome
  HorizontalObstruction VerticalOutcome VerticalObstruction)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest.HorizontalCrossing
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest.VerticalCrossing
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains :
    FaceDomainBank frames faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}
  {mesh : LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : TwoSheetRequest (fun sheet
  => RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
variable (firstDifferential secondDifferential : Differential genus)
  (firstParent secondParent : Fin 2)
  (tolerance : Rational) (floor : Nat)

namespace CrossingRequests

set_option genInjectivity false in
/-- The prepared original horizontal crossing request or its retained geometric separation obstruction. -/
inductive HorizontalPrepared {first : mesh.LocatedFace firstPosition firstSheet}
    {nextPosition : Fin faces.regulars.length} : CrossingBank.HorizontalOutcome request first nextPosition → Type 3
      where
  /-- Retain the actual paid area request for the original matched horizontal crossing. -/ | matched {joined} :
    HorizontalCrossing.AreaRequest
      joined firstDifferential secondDifferential
      firstParent secondParent tolerance floor →
        HorizontalPrepared (.matched joined)
  /-- Retain the original horizontal separation obstruction unchanged. -/ | separated (obstruction :
    CrossingBank.HorizontalObstruction (faces := faces) firstPosition nextPosition) :
      HorizontalPrepared (.separated
        obstruction)

constructive_injectivity HorizontalPrepared

end CrossingRequests

namespace CrossingRequests.HorizontalPrepared

/-- Prepare an area request for the actual matched horizontal crossing or preserve its original separation witness. -/
@[expose] def build {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
    (positive : 0 < tolerance) (outcome : CrossingBank.HorizontalOutcome request first nextPosition) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.HorizontalPrepared firstDifferential
      secondDifferential firstParent secondParent tolerance floor outcome :=
  match outcome with
  | .matched joined => .matched (AreaRequest.build joined firstDifferential secondDifferential
      firstParent secondParent tolerance positive floor)
  | .separated obstruction => .separated obstruction

/-- The actual original horizontal area-request stage, with zero for a separated pair. -/
@[expose] def index {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
    {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.HorizontalPrepared firstDifferential
      secondDifferential firstParent secondParent tolerance floor outcome) : Nat :=
  match prepared with
  | .matched allocated => allocated.accuracy.index
  | .separated _ => 0

/-- Read the actual retained original horizontal area request from a certified matched outcome. -/
@[expose] def allocated {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
    {joined : LiftedSides.HorizontalCrossing request first nextPosition false false}
    (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.HorizontalPrepared firstDifferential
      secondDifferential firstParent secondParent tolerance floor (.matched joined)) :
    HorizontalCrossing.AreaRequest
      joined firstDifferential secondDifferential firstParent secondParent tolerance floor :=
  match prepared with
  | .matched allocation => allocation

/-- The extracted original horizontal area request has exactly the retained preparation stage. -/
theorem allocated_index {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
    {joined : LiftedSides.HorizontalCrossing request first nextPosition false false}
    (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.HorizontalPrepared firstDifferential
      secondDifferential firstParent secondParent tolerance floor (.matched joined)) :
    (allocated firstDifferential
      secondDifferential firstParent secondParent tolerance floor prepared).accuracy.index =
      index firstDifferential
        secondDifferential firstParent secondParent tolerance floor prepared := by
  cases prepared
  rfl

end CrossingRequests.HorizontalPrepared

namespace CrossingRequests

set_option genInjectivity false in
/-- The prepared original vertical crossing request or its retained geometric separation obstruction. -/
inductive VerticalPrepared {first : mesh.LocatedFace firstPosition firstSheet}
    {nextPosition : Fin faces.regulars.length} : CrossingBank.VerticalOutcome request first nextPosition → Type 3 where
  /-- Retain the actual paid area request for the original matched vertical crossing. -/ | matched {joined} :
    VerticalCrossing.AreaRequest
      joined firstDifferential secondDifferential
      firstParent secondParent tolerance floor →
        VerticalPrepared (.matched joined)
  /-- Retain the original vertical separation obstruction unchanged. -/ | separated (obstruction :
    CrossingBank.VerticalObstruction (faces := faces) firstPosition nextPosition) :
      VerticalPrepared (.separated
        obstruction)

constructive_injectivity VerticalPrepared

end CrossingRequests

namespace CrossingRequests.VerticalPrepared

/-- Prepare an area request for the actual matched vertical crossing or preserve its original separation witness. -/
@[expose] def build {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
    (positive : 0 < tolerance) (outcome : CrossingBank.VerticalOutcome request first nextPosition) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.VerticalPrepared firstDifferential
      secondDifferential firstParent secondParent tolerance floor outcome :=
  match outcome with
  | .matched joined => .matched (AreaRequest.build joined firstDifferential secondDifferential
      firstParent secondParent tolerance positive floor)
  | .separated obstruction => .separated obstruction

/-- The actual original vertical area-request stage, with zero for a separated pair. -/
@[expose] def index {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
    {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.VerticalPrepared firstDifferential
      secondDifferential firstParent secondParent tolerance floor outcome) : Nat :=
  match prepared with
  | .matched allocated => allocated.accuracy.index
  | .separated _ => 0

/-- Read the actual retained original vertical area request from a certified matched outcome. -/
@[expose] def allocated {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
    {joined : LiftedSides.VerticalCrossing request first nextPosition false false}
    (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.VerticalPrepared firstDifferential
      secondDifferential firstParent secondParent tolerance floor (.matched joined)) :
    VerticalCrossing.AreaRequest
      joined firstDifferential secondDifferential firstParent secondParent tolerance floor :=
  match prepared with
  | .matched allocation => allocation

/-- The extracted original vertical area request has exactly the retained preparation stage. -/
theorem allocated_index {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
    {joined : LiftedSides.VerticalCrossing request first nextPosition false false}
    (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.VerticalPrepared firstDifferential
      secondDifferential firstParent secondParent tolerance floor (.matched joined)) :
    (allocated firstDifferential
      secondDifferential firstParent secondParent tolerance floor prepared).accuracy.index =
      index firstDifferential
        secondDifferential firstParent secondParent tolerance floor prepared := by
  cases prepared
  rfl

end CrossingRequests.VerticalPrepared

set_option genInjectivity false in
/- Preserve the original CrossingRequests nominal name inside its original module. -/
/-- The complete original classified crossing request bank and one common paid numerical stage.

Every face, sheet and destination index retains its actual matched request or original separation obstruction. -/
structure CrossingRequests (retained : CrossingBank request mesh) where
  /-- The actual original horizontal crossing preparations on all retained face, sheet and destination indices. -/
    horizontal : Data.Vector.DependentVector (fun a : Fin faces.regulars.length =>
    Data.Vector.DependentVector (fun b : Fin 2 => Data.Vector.DependentVector (fun c : Fin faces.regulars.length =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.HorizontalPrepared firstDifferential
        secondDifferential firstParent secondParent tolerance floor
        (((retained.horizontal.get a).get b).get c))))
  /-- The actual original vertical crossing preparations on all retained face, sheet and destination indices. -/
    vertical : Data.Vector.DependentVector (fun a : Fin faces.regulars.length =>
    Data.Vector.DependentVector (fun b : Fin 2 => Data.Vector.DependentVector (fun c : Fin faces.regulars.length =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.VerticalPrepared firstDifferential
        secondDifferential firstParent secondParent tolerance floor
        (((retained.vertical.get a).get b).get c))))
  /-- The cached common stage paying the original base request and both complete crossing banks. -/ index : Nat
  /-- The common stage pays the original synchronized two-sheet request. -/ base_le : request.index ≤ index
  /-- The common stage pays every actual original horizontal crossing preparation. -/ horizontal_le : ∀ a b c,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.HorizontalPrepared.index firstDifferential
      secondDifferential firstParent secondParent tolerance floor
      (((horizontal.get a).get b).get c) ≤ index
  /-- The common stage pays every actual original vertical crossing preparation. -/ vertical_le : ∀ a b c,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.VerticalPrepared.index firstDifferential
      secondDifferential firstParent secondParent tolerance floor
      (((vertical.get a).get b).get c) ≤ index

/- The original constructor certificates retain that same nominal route. -/

constructive_injectivity CrossingRequests

/- The builder belongs to the original CrossingRequests nominal. -/
namespace CrossingRequests

/-- Prepare every original classified crossing once and cache one stage paying the base request and all actual
allocations. -/
@[expose] def build (retained : CrossingBank request mesh) (positive : 0 < tolerance) :
    CrossingRequests firstDifferential
      secondDifferential firstParent secondParent tolerance floor retained := by
  let horizontal := DependentVector.ofFn (fun a : Fin faces.regulars.length =>
    DependentVector.ofFn (fun b : Fin 2 => DependentVector.ofFn (fun c : Fin faces.regulars.length =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.HorizontalPrepared.build firstDifferential
        secondDifferential firstParent secondParent tolerance floor positive
        (((retained.horizontal.get a).get b).get c))))
  let horizontalWeight := fun a b c =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.HorizontalPrepared.index firstDifferential
    secondDifferential firstParent secondParent tolerance floor
    (outcome := (((retained.horizontal.get a).get b).get c))
  let vertical := DependentVector.ofFn (fun a : Fin faces.regulars.length =>
    DependentVector.ofFn (fun b : Fin 2 => DependentVector.ofFn (fun c : Fin faces.regulars.length =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.VerticalPrepared.build firstDifferential
        secondDifferential firstParent secondParent tolerance floor positive
        (((retained.vertical.get a).get b).get c))))
  let verticalWeight := fun a b c =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests.VerticalPrepared.index firstDifferential
    secondDifferential firstParent secondParent tolerance floor
    (outcome := (((retained.vertical.get a).get b).get c))
  let horizontalMax := DependentVector.maximum3 horizontalWeight horizontal
  let verticalMax := DependentVector.maximum3 verticalWeight vertical
  refine ⟨horizontal, vertical, max request.index (max horizontalMax verticalMax), Data.Nat.Order.le_max_left _ _, ?_,
    ?_⟩
  · intro a b c
    exact (DependentVector.entry_le_maximum3 horizontalWeight horizontal a b c).trans
      ((Data.Nat.Order.le_max_left horizontalMax verticalMax).trans (Data.Nat.Order.le_max_right _ _))
  · intro a b c
    exact (DependentVector.entry_le_maximum3 verticalWeight vertical a b c).trans
      ((Data.Nat.Order.le_max_right horizontalMax verticalMax).trans (Data.Nat.Order.le_max_right _ _))

end CrossingRequests

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

end
