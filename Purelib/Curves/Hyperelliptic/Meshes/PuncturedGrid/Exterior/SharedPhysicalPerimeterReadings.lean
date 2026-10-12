module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalReadingSample
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Integration.Path

open Purelib.Riemann.Meshes

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

@[expose] public section

/-! Select and sample the actual rectangle side named by an exterior occurrence. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
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
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

variable {firstBank : FacePrimitiveBank
  differential index domains} {secondBank :
  FacePrimitiveBank other index domains}

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
variable {cuts : GridCuts ((domains.get
  occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry} {meshBox :
  Purelib.Geometry.Rational.Box}
  {mesh : ObservationMesh cuts meshBox} {depth : Nat}

section SharedPhysicalPerimeterReadings
variable (traces : PerimeterTraces mesh)

/-- Keep the side-specific owner readings, including their duplicate junctions. -/
def Entries (firstBank : PrimitiveData.FacePrimitiveBank differential index domains) (secondBank :
  PrimitiveData.FacePrimitiveBank other index domains) : GridLiftedDualSteps.GridSide → Type
  | .bottom => SharedPhysicalHorizontalReadings.Data traces.bottom firstBank secondBank
  | .top => SharedPhysicalHorizontalReadings.Data traces.top firstBank secondBank
  | .left => SharedPhysicalVerticalReadings.Data traces.left firstBank secondBank
  | .right => SharedPhysicalVerticalReadings.Data traces.right firstBank secondBank

/-- Read both original shared face banks on the selected retained rectangle side, preserving its actual owner junctions.
-/
def build (firstBank : PrimitiveData.FacePrimitiveBank differential index domains) (secondBank :
  PrimitiveData.FacePrimitiveBank other index domains) :
    (side : GridLiftedDualSteps.GridSide) →
      Entries
      traces firstBank secondBank side
  | .bottom => SharedPhysicalHorizontalReadings.build traces.bottom firstBank secondBank
  | .top => SharedPhysicalHorizontalReadings.build traces.top firstBank secondBank
  | .left => SharedPhysicalVerticalReadings.build traces.left firstBank secondBank
  | .right => SharedPhysicalVerticalReadings.build traces.right firstBank secondBank

/-- The actual number of steps in the selected retained perimeter trace. -/
def count : GridLiftedDualSteps.GridSide → Nat
  | .bottom => traces.bottom.vertices.rest.length
  | .top => traces.top.vertices.rest.length
  | .left => traces.left.vertices.rest.length
  | .right => traces.right.vertices.rest.length

/-- Read the paired original face-bank values at the selected side's retained indexed vertex. -/
def values (firstBank : PrimitiveData.FacePrimitiveBank differential index domains) (secondBank :
  PrimitiveData.FacePrimitiveBank other index domains) :
    (side : GridLiftedDualSteps.GridSide) → Fin
      (count
      traces side + 1) → Stokes.PrimitivePoint
  | .bottom, vertex => ⟨SharedPhysicalHorizontalReadings.firstValue traces.bottom firstBank
    (traces.bottom.vertices.indexed vertex),
      SharedPhysicalHorizontalReadings.secondValue traces.bottom secondBank (traces.bottom.vertices.indexed vertex)⟩
  | .top, vertex => ⟨SharedPhysicalHorizontalReadings.firstValue traces.top firstBank (traces.top.vertices.indexed
    vertex),
      SharedPhysicalHorizontalReadings.secondValue traces.top secondBank (traces.top.vertices.indexed vertex)⟩
  | .left, vertex => ⟨SharedPhysicalVerticalReadings.firstValue traces.left firstBank (traces.left.vertices.indexed
    vertex),
      SharedPhysicalVerticalReadings.secondValue traces.left secondBank (traces.left.vertices.indexed vertex)⟩
  | .right, vertex => ⟨SharedPhysicalVerticalReadings.firstValue traces.right firstBank (traces.right.vertices.indexed
    vertex),
      SharedPhysicalVerticalReadings.secondValue traces.right secondBank (traces.right.vertices.indexed vertex)⟩

/-- Reuse the selected side's cached area; this adapter does not sample again. -/
def original {side : GridLiftedDualSteps.GridSide} (readings :
  Entries
  traces firstBank secondBank side) :
    CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst
      (values
      traces firstBank secondBank side vertex)) := by
  cases side with
  | bottom => exact readings.original
  | top => exact readings.original
  | left => exact readings.original
  | right => exact readings.original

/-- The number of original internal owner junctions on the selected horizontal or vertical mesh side. -/
def pieceCount (mesh : RectangularObservationMesh.ObservationMesh cuts meshBox) : GridLiftedDualSteps.GridSide → Nat
  | .bottom | .top => mesh.boundaryColumns
  | .left | .right => mesh.boundaryRows

end SharedPhysicalPerimeterReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
