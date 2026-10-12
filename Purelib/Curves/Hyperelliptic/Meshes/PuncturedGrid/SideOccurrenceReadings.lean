module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
open Purelib.Data.Rat
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing

/-! Oriented fine-area and source-chord readings for retained side occurrences.
The endpoint request pays the complete difference from the centered fine trace. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh
namespace SideOccurrence

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh (SideOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}

/-- Apply the actual rectangle-side sign and retained reversal flag to a scalar reading. -/
@[expose] def oriented (occurrence : LiftedMesh.SideOccurrence mesh) (value : Data.Gaussian.Basic.Canonical) : Gaussian
  :=
  let forward := if occurrence.side = .top ∨ occurrence.side = .left then -value else value
  if occurrence.backward then -forward else forward

/-- The retained occurrence orientation preserves subtraction. -/
theorem oriented_sub (occurrence : LiftedMesh.SideOccurrence mesh) (first last : Data.Gaussian.Basic.Canonical) :
    oriented
      occurrence (first - last) =
      oriented
      occurrence first -
      oriented
      occurrence last := by
  rcases occurrence with ⟨position, sheet, side, backward⟩
  cases side <;> cases backward <;> simp only
    [oriented,
    if_pos (by decide : Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide.top = .top ∨
      Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide.top = .left),
    if_pos (by decide : Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide.left = .top ∨
      Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide.left = .left),
    if_neg (by decide : ¬ (Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide.bottom = .top ∨
      Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide.bottom = .left)),
    if_neg (by decide : ¬ (Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide.right = .top ∨
      Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide.right = .left)),
    if_pos (Eq.refl true), if_neg (by decide : ¬ false = true), -eq_self, -iff_self] <;> ring1

/-- The retained occurrence orientation preserves squared norm. -/
theorem normSq_oriented (occurrence : LiftedMesh.SideOccurrence mesh) (value : Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq
      (oriented
      occurrence value) = Data.Gaussian.Norm.Basic.normSq value := by
  unfold
    oriented
  split <;> split <;> simp only [Data.Gaussian.Norm.Basic.normSq_neg, -eq_self, -iff_self] <;> rfl

variable {domains : FaceDomainBank frames
  faces.regulars} {stage : Nat}
  {cache : Numerics domains stage}
    {i j : Fin genus}

/-- The original source chord is exactly the oriented chord of its retained face, sheet and side. -/
theorem sourceChord (occurrence : LiftedMesh.SideOccurrence mesh)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    TriangleReadings.sourceChord left right occurrence.source =
      oriented
        occurrence (Numerics.sideChord cache.normalize i j occurrence.position occurrence.sheet occurrence.side) := by
  rcases occurrence with ⟨position, sheet, side, backward⟩
  have forward := TriangleReadings.sourceChord_side left right (mesh.locateFace position sheet) side
  cases backward with
  | false => exact forward
  | true =>
      have reversed (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) :
          TriangleReadings.sourceChord left right ⟨source.source, source.last, source.first⟩ =
            -TriangleReadings.sourceChord left right source :=
        Stokes.edgeArea_reverse _ _
      exact (reversed (LocatedFace.sideSource (mesh.locateFace position sheet) side)).trans (congrArg Neg.neg forward)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering (CenteredPerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder (sideCenteredArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh (SideOccurrence)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

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

namespace CenteredPerimeters

/-- The oriented centered area of the retained source occurrence on the original sampled perimeter. -/
@[expose] def occurrenceArea (samples : RequestedHoleCentering.CenteredPerimeters request cache i j) (occurrence :
  LiftedMesh.SideOccurrence lifted.mesh) : Gaussian :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
    occurrence (SideCenteredRemainder.sideCenteredArea ((samples.samples.get occurrence.position).get occurrence.sheet)
    occurrence.side)

end CenteredPerimeters

/-- The oriented fine perimeter area of the retained source occurrence. -/
@[expose] def occurrenceFineArea (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (occurrence : LiftedMesh.SideOccurrence lifted.mesh) : Gaussian :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
    occurrence (match occurrence.side with
    | .bottom => ((perimeters.perimeters.get occurrence.position).get occurrence.sheet).bottom
    | .right => ((perimeters.perimeters.get occurrence.position).get occurrence.sheet).right
    | .top => ((perimeters.perimeters.get occurrence.position).get occurrence.sheet).top
    | .left => ((perimeters.perimeters.get occurrence.position).get occurrence.sheet).left)

/-- The actual fine occurrence area minus its source chord equals the oriented retained side-area remainder. -/
theorem occurrence_remainder (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (occurrence : LiftedMesh.SideOccurrence lifted.mesh)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) :
    occurrenceFineArea
      perimeters occurrence - TriangleReadings.sourceChord left right occurrence.source =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
        occurrence (HoleAreaRemainder.sideAreaRemainder perimeters occurrence.position occurrence.sheet occurrence.side)
        := by
  unfold occurrenceFineArea
  rw
    [BranchCellBank.LiftedMesh.SideOccurrence.sourceChord
    occurrence left right, ←
    BranchCellBank.LiftedMesh.SideOccurrence.oriented_sub
    occurrence]
  rfl

namespace PerimeterEndpointRequest

/-- The original endpoint request bounds the occurrence's fine area minus its source chord and centered area.

The comparison retains the exact face, sheet, side and reversal of the source occurrence. -/
theorem occurrence_bound {error : Fraction.Rational} (allocated : PerimeterEndpointRequest
  fixed i j error)
    (later : allocated.index ≤ stage) (samples : RequestedHoleCentering.CenteredPerimeters request cache i j)
    (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    (occurrence : LiftedMesh.SideOccurrence lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrenceFineArea
      perimeters occurrence - TriangleReadings.sourceChord left right occurrence.source -

        CenteredPerimeters.occurrenceArea
        samples occurrence) ≤ error := by
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrence_remainder
    perimeters occurrence left right]
  change Data.Gaussian.Norm.Basic.normSq
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
    occurrence _ -
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
    occurrence _) ≤ error
  rw [←
    BranchCellBank.LiftedMesh.SideOccurrence.oriented_sub
    occurrence,
    BranchCellBank.LiftedMesh.SideOccurrence.normSq_oriented
    occurrence]
  exact allocated.bound later ((samples.samples.get occurrence.position).get occurrence.sheet) perimeters
    occurrence.side

end PerimeterEndpointRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid
