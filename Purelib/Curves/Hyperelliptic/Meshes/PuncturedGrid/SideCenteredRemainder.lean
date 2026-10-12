module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.RectangularPerimeterTraces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
public import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes

open Purelib.Riemann.Integration

open Purelib.Riemann.Meshes

open Purelib.Riemann.Paths

@[expose] public section

/-! Centered trace areas and endpoint errors on the actual shared grid cache. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
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
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (faceValues)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (Centered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {target : Rational} {i j : Fin genus} {stage : Nat} {cache :
    Numerics domains stage}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}

open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

variable {position : Fin base.faces.regulars.length} {sheet : Fin 2}

/-- Read the actual centered trace area of the selected retained face side. -/
def sideCenteredArea
    {traces : RectangularPerimeterTraces.PerimeterTraces ((request.entries.get sheet).meshes.entries.get position)}
    (samples : RectangularCenteredPerimeter.Centered traces (FacePerimeters.faceValues cache i j position sheet)) :
      GridLiftedDualSteps.GridSide → Data.Gaussian.Basic.Canonical
  | .bottom => samples.bottom.centeredArea
  | .top => samples.top.centeredArea
  | .left => samples.left.centeredArea
  | .right => samples.right.centeredArea

/-- Read the actual endpoint contribution of the selected retained face side. -/
def sideEndpoint
    {traces : RectangularPerimeterTraces.PerimeterTraces ((request.entries.get sheet).meshes.entries.get position)}
    (samples : RectangularCenteredPerimeter.Centered traces (FacePerimeters.faceValues cache i j position sheet)) :
      GridLiftedDualSteps.GridSide → Data.Gaussian.Basic.Canonical
  | .bottom => samples.bottom.endpoint
  | .top => samples.top.endpoint
  | .left => samples.left.endpoint
  | .right => samples.right.endpoint

/-- The original side-area remainder splits into its centered trace area and actual endpoint-chord discrepancy. -/
theorem side_centered_remainder
    {traces : RectangularPerimeterTraces.PerimeterTraces ((request.entries.get sheet).meshes.entries.get position)}
    (samples : RectangularCenteredPerimeter.Centered traces (FacePerimeters.faceValues cache i j position sheet))
    (perimeters : Matched.FacePerimeters (request := request) cache i j) (side : GridLiftedDualSteps.GridSide) :
    HoleAreaRemainder.sideAreaRemainder perimeters position sheet side =
      sideCenteredArea samples side +
        (sideEndpoint samples side - Numerics.sideChord
        cache i j position sheet side) := by
  cases side with
  | bottom =>
    have equal := samples.bottom_eq ((perimeters.assemblies.get position).get sheet)
      ((perimeters.perimeters.get position).get sheet)
    exact (congrArg (fun area => area - Numerics.sideChord cache i j position sheet _) equal).trans
      (add_sub_assoc _ _ _)
  | top =>
    have equal := samples.top_eq ((perimeters.assemblies.get position).get sheet)
      ((perimeters.perimeters.get position).get sheet)
    exact (congrArg (fun area => area - Numerics.sideChord cache i j position sheet _) equal).trans
      (add_sub_assoc _ _ _)
  | left =>
    have equal := samples.left_eq ((perimeters.assemblies.get position).get sheet)
      ((perimeters.perimeters.get position).get sheet)
    exact (congrArg (fun area => area - Numerics.sideChord cache i j position sheet _) equal).trans
      (add_sub_assoc _ _ _)
  | right =>
    have equal := samples.right_eq ((perimeters.assemblies.get position).get sheet)
      ((perimeters.perimeters.get position).get sheet)
    exact (congrArg (fun area => area - Numerics.sideChord cache i j position sheet _) equal).trans
      (add_sub_assoc _ _ _)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
