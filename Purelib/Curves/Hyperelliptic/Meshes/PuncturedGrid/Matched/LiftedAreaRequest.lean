module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSideAreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.PerimeterRequest
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
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

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations

open Purelib.Data.Rat

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide

public section

/-! Retain the trace, common-owner preparation, and numerical area request for
an actual lifted face crossing. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Rat.Fraction (Rational)

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

variable {request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet
  => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)

namespace HorizontalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

set_option genInjectivity false in
/-- The actual retained horizontal crossing trace, common-corner preparation and numerical area request.

Both original face sheets and the selected differential parents remain tied to the same trace. -/
structure AreaRequest (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    (firstDifferential secondDifferential : Differentials.Basic.Differential genus) (firstParent secondParent : Fin 2)
    (target : Fraction.Rational) (floor : Nat) where
  /-- The actual horizontal side trace at the original source mesh depth. -/ trace : joined.side.Trace
    ((request.entries.get firstSheet).meshes.entries.get firstPosition).depth
  /-- The two original face-sheet preparations sharing the retained lifted corner owner. -/ preparation :
    SidePreparation.MatchedSidePreparation
    (leftEntry := HorizontalCrossing.leftEntry joined)
    (rightEntry := HorizontalCrossing.rightEntry joined) trace
  /-- The numerical area request on those exact retained preparations and original differential parents. -/ accuracy :
    SideAreaRequest.MatchedSidePreparation.AreaRequest preparation
    firstDifferential secondDifferential firstParent secondParent target floor

constructive_injectivity AreaRequest

/-- Build the actual horizontal crossing trace, prepare both original corner owners and retain their area comparison
request. -/
@[expose] def AreaRequest.build (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper
  lastUpper)
    (firstDifferential secondDifferential : Differentials.Basic.Differential genus) (firstParent secondParent : Fin 2)
    (target : Fraction.Rational) (positive : 0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest.HorizontalCrossing.AreaRequest joined
      firstDifferential secondDifferential firstParent secondParent target floor := by
  let trace := Trace.build
    joined.side ((request.entries.get firstSheet).meshes.entries.get firstPosition).depth
  let preparation := HorizontalCrossing.preparation joined trace
  exact ⟨trace, preparation, SideAreaRequest.MatchedSidePreparation.AreaRequest.build preparation
    firstDifferential secondDifferential firstParent secondParent target positive floor⟩

end HorizontalCrossing

namespace VerticalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

set_option genInjectivity false in
/-- The actual retained vertical crossing trace, common-corner preparation and numerical area request.

Both original face sheets and the selected differential parents remain tied to the same trace. -/
structure AreaRequest (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    (firstDifferential secondDifferential : Differentials.Basic.Differential genus) (firstParent secondParent : Fin 2)
    (target : Fraction.Rational) (floor : Nat) where
  /-- The actual vertical side trace at the original source mesh depth. -/ trace : joined.side.Trace
    ((request.entries.get firstSheet).meshes.entries.get firstPosition).depth
  /-- The two original face-sheet preparations sharing the retained lifted corner owner. -/ preparation :
    VerticalSidePreparation.MatchedVerticalSidePreparation
    (leftEntry := VerticalCrossing.leftEntry joined)
    (rightEntry := VerticalCrossing.rightEntry joined) trace
  /-- The numerical area request on those exact retained preparations and original differential parents. -/ accuracy :
    VerticalSideAreaRequest.MatchedVerticalSidePreparation.AreaRequest preparation
    firstDifferential secondDifferential firstParent secondParent target floor

constructive_injectivity AreaRequest

/-- Build the actual vertical crossing trace, prepare both original corner owners and retain their area comparison
request. -/
@[expose] def AreaRequest.build (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    (firstDifferential secondDifferential : Differentials.Basic.Differential genus) (firstParent secondParent : Fin 2)
    (target : Fraction.Rational) (positive : 0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest.VerticalCrossing.AreaRequest joined
      firstDifferential secondDifferential firstParent secondParent target floor := by
  let trace := Trace.build
    joined.side ((request.entries.get firstSheet).meshes.entries.get firstPosition).depth
  let preparation := VerticalCrossing.preparation joined trace
  exact ⟨trace, preparation, VerticalSideAreaRequest.MatchedVerticalSidePreparation.AreaRequest.build preparation
    firstDifferential secondDifferential firstParent secondParent target positive floor⟩

end VerticalCrossing

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest
