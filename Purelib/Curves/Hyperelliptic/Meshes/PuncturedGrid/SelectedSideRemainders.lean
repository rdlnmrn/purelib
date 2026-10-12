module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedDualSteps
open Purelib.Riemann.Meshes.PuncturedGridFaces

/-! The selected boundary correction reads the original fine-side remainders,
with all physical sides and interfaces to discarded faces still explicit. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.TwoSheetRequest.SelectedSides

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides (value value_sub
  value_zero value_sum transition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition (selectedBoundaryTriangleArea)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_add sumFin_neg sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_zero)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains :
    FaceDomainBank frames faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}
  {mesh : LiftedMesh vertices edges faces}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}
  {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Rational} {floor stage :
    Nat}
  {retained : Matched.CrossingBank request mesh}
  {cache : Numerics domains stage}

/-- Oriented boundary evaluation on physical sides and selected/unselected regular interfaces. Values use the existing
geometric side directions. -/
@[expose] def boundaryEvaluation (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length →
      Data.Gaussian.Basic.Canonical) : Gaussian :=
  (FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (neighbors.entries.get p).right (SelectedSides.value (keep
    p) (values .right p))) -
    FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (neighbors.entries.get p).left (SelectedSides.value (keep
      p) (values .left p))) -
    (FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (neighbors.entries.get p).top (SelectedSides.value (keep
      p) (values .top p))) -
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (neighbors.entries.get p).bottom (SelectedSides.value
        (keep p) (values .bottom p))))) +
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun c =>
    if GridSide.Matches .right (faces.regulars[a.val]'a.isLt).cell.box (faces.regulars[c.val]'c.isLt).cell.box then
      SelectedSides.transition (keep a) (keep c) (values .right a) (values .left c) else 0)) -
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun c =>
    if GridSide.Matches .top (faces.regulars[a.val]'a.isLt).cell.box (faces.regulars[c.val]'c.isLt).cell.box then
      SelectedSides.transition (keep a) (keep c) (values .top a) (values .bottom c) else 0))

/-- Selected boundary evaluation depends only on the pointwise actual side values. -/
theorem boundaryEvaluation_congr (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) {first last : GridLiftedDualSteps.GridSide → Fin faces.regulars.length →
      Data.Gaussian.Basic.Canonical}
    (equal : ∀ side p, first side p = last side p) :
    boundaryEvaluation
      neighbors keep first =
      boundaryEvaluation
      neighbors keep last := by
  unfold
    boundaryEvaluation
  have rightEqual := FiniteSum.Fin.sumFin_congr (fun p =>
    congrArg (fun value => SideNeighbor.physicalValue (neighbors.entries.get p).right
      (SelectedSides.value (keep p) value)) (equal .right p))
  have leftEqual := FiniteSum.Fin.sumFin_congr (fun p =>
    congrArg (fun value => SideNeighbor.physicalValue (neighbors.entries.get p).left
      (SelectedSides.value (keep p) value)) (equal .left p))
  have topEqual := FiniteSum.Fin.sumFin_congr (fun p =>
    congrArg (fun value => SideNeighbor.physicalValue (neighbors.entries.get p).top
      (SelectedSides.value (keep p) value)) (equal .top p))
  have bottomEqual := FiniteSum.Fin.sumFin_congr (fun p =>
    congrArg (fun value => SideNeighbor.physicalValue (neighbors.entries.get p).bottom
      (SelectedSides.value (keep p) value)) (equal .bottom p))
  have rightPairs := FiniteSum.Fin.sumFin_congr (fun a =>
    FiniteSum.Fin.sumFin_congr (fun c =>
      congrArg₂ (fun first last =>
        if GridSide.Matches .right (faces.regulars[a.val]'a.isLt).cell.box
          (faces.regulars[c.val]'c.isLt).cell.box then
            SelectedSides.transition (keep a) (keep c) first last else 0)
        (equal .right a) (equal .left c)))
  have topPairs := FiniteSum.Fin.sumFin_congr (fun a =>
    FiniteSum.Fin.sumFin_congr (fun c =>
      congrArg₂ (fun first last =>
        if GridSide.Matches .top (faces.regulars[a.val]'a.isLt).cell.box
          (faces.regulars[c.val]'c.isLt).cell.box then
            SelectedSides.transition (keep a) (keep c) first last else 0)
        (equal .top a) (equal .bottom c)))
  rw [rightEqual, leftEqual, topEqual, bottomEqual, rightPairs, topPairs]

/-- Physical-side selection preserves subtraction. -/
private theorem physical_sub {face : PuncturedGridFaces.RegularFace bank} {side : GridLiftedDualSteps.GridSide}
    (neighbor : PuncturedFaces.SideNeighbor faces face side) (a b : Data.Gaussian.Basic.Canonical) :
    SideNeighbor.physicalValue neighbor (a - b) = SideNeighbor.physicalValue neighbor a - SideNeighbor.physicalValue
      neighbor b := by
  cases neighbor with
  | neighbor cell member matching location =>
      cases location <;> simp only [SideNeighbor.physicalValue, -eq_self, -iff_self] <;> ring1
  | exterior equal => rfl

/-- Physical-side selection maps zero to zero. -/
private theorem physical_zero {face : PuncturedGridFaces.RegularFace bank} {side : GridLiftedDualSteps.GridSide}
    (neighbor : PuncturedFaces.SideNeighbor faces face side) : SideNeighbor.physicalValue neighbor 0 = 0 := by
  cases neighbor with
  | neighbor cell member matching location => cases location <;> rfl
  | exterior equal => rfl

/-- Physical-side selection commutes with a finite sum. -/
private theorem physical_sum {face : PuncturedGridFaces.RegularFace bank} {side : GridLiftedDualSteps.GridSide}
    (neighbor : PuncturedFaces.SideNeighbor faces face side) {count : Nat} (values : Fin count →
      Data.Gaussian.Basic.Canonical) :
    SideNeighbor.physicalValue neighbor (FiniteSum.Fin.sumFin values) = FiniteSum.Fin.sumFin (fun index =>
      SideNeighbor.physicalValue neighbor (values index)) := by
  cases neighbor with
  | neighbor cell member matching location =>
    cases location <;> simp only [SideNeighbor.physicalValue, FiniteSum.Fin.sumFin_zero, -eq_self, -iff_self] <;> rfl
  | exterior equal => rfl

/-- Selected-side evaluation preserves negation. -/
private theorem value_neg (keep : Bool) (area : Data.Gaussian.Basic.Canonical) : SelectedSides.value keep (-area) =
  -SelectedSides.value keep area := by
  cases keep <;> simp only [SelectedSides.value, if_neg (by decide : ¬ false = true), if_pos (Eq.refl true), -eq_self,
    -iff_self] <;> ring1

/-- Physical-side selection preserves negation. -/
private theorem physical_neg {face : PuncturedGridFaces.RegularFace bank} {side : GridLiftedDualSteps.GridSide}
    (neighbor : PuncturedFaces.SideNeighbor faces face side) (area : Data.Gaussian.Basic.Canonical) :
    SideNeighbor.physicalValue neighbor (-area) = -SideNeighbor.physicalValue neighbor area := by
  have h := physical_sub
    neighbor 0 area
  simpa only [zero_sub,
    physical_zero,
    -eq_self, -iff_self] using h

/-- The selected/unselected interface contribution preserves paired subtraction. -/
private theorem transition_sub (a b : Bool) (x y z w : Data.Gaussian.Basic.Canonical) :
    SelectedSides.transition a b (x - y) (z - w) = SelectedSides.transition a b x z - SelectedSides.transition a b y w
      := by
  simp only [SelectedSides.transition, SelectedSides.value_sub, -eq_self, -iff_self]
  ring1

/-- A decidable zero-extended contribution preserves subtraction. -/
private theorem if_sub (p : Prop) [Decidable p] (a b : Data.Gaussian.Basic.Canonical) :
    (if p then a - b else 0) = (if p then a else 0) - (if p then b else 0) := by
  split
  · rfl
  · ring1

/-- The complete selected boundary evaluation preserves pointwise subtraction. -/
theorem boundaryEvaluation_sub (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (first last : GridLiftedDualSteps.GridSide → Fin faces.regulars.length →
      Data.Gaussian.Basic.Canonical) :
    boundaryEvaluation
      neighbors keep (fun side p => first side p - last side p) =
      boundaryEvaluation
        neighbors keep first -
        boundaryEvaluation
        neighbors keep last := by
  simp only
    [boundaryEvaluation,
    SelectedSides.value_sub,
    physical_sub,
    transition_sub,
    if_sub,
    FiniteSum.Fin.sumFin_sub, -eq_self, -iff_self]
  ring1

/-- A decidable zero-extended contribution commutes with a finite sum. -/
private theorem if_sum (p : Prop) [Decidable p] {count : Nat} (values : Fin count → Data.Gaussian.Basic.Canonical) :
    (if p then FiniteSum.Fin.sumFin values else 0) = FiniteSum.Fin.sumFin (fun i => if p then values i else 0) := by
  split
  · rfl
  · exact FiniteSum.Fin.sumFin_zero.symm

/-- A decidable zero-extended contribution preserves negation. -/
private theorem if_neg (p : Prop) [Decidable p] (area : Data.Gaussian.Basic.Canonical) :
    (if p then -area else 0) = -(if p then area else 0) := by
  split
  · rfl
  · ring1

/-- Evaluating the normalized side chords on the actual selected boundary gives its retained source-triangle area. -/
theorem boundaryEvaluation_chords (neighbors : PuncturedFaces.NeighborBank faces)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (keep : Fin faces.regulars.length → Bool) :
    boundaryEvaluation
      neighbors keep (fun side p => FiniteSum.Fin.sumFin (fun sheet => Numerics.sideChord cache.normalize i j p sheet
      side)) =
      SelectedTrianglePartition.selectedBoundaryTriangleArea neighbors left right keep := by
  simp only
    [boundaryEvaluation,
    Numerics.normalized_bottom_chord cache, Numerics.normalized_left_chord cache,
    TriangleReadings.normalized_right_chord left right, TriangleReadings.normalized_top_chord left right,
    FiniteSum.Fin.sumFin_zero, FiniteSum.Fin.sumFin_neg, SelectedSides.value_zero,
      physical_zero,
    SelectedSides.transition,
      value_neg,
      physical_neg,
      Data.Gaussian.Basic.sub_zero,
      if_neg,
    SelectedSides.value_sum,
      physical_sum,
      if_sum, -eq_self,
      -iff_self]
  rw [FiniteSum.Fin.sumFin_congr (fun a => FiniteSum.Fin.sumFin_swap
    (fun c b => if GridSide.Matches .right (faces.regulars[a.val]'a.isLt).cell.box
      (faces.regulars[c.val]'c.isLt).cell.box then
      SelectedSides.value (keep a && !keep c) (TriangleReadings.bilinearArea left right (mesh.triangleIndex a b false))
        else 0)),
    FiniteSum.Fin.sumFin_congr (fun a => FiniteSum.Fin.sumFin_swap
    (fun c b => if GridSide.Matches .top (faces.regulars[a.val]'a.isLt).cell.box (faces.regulars[c.val]'c.isLt).cell.box
      then
      SelectedSides.value (keep a && !keep c) (TriangleReadings.bilinearArea left right (mesh.triangleIndex a b true))
        else 0))]
  simp only [SelectedTrianglePartition.selectedBoundaryTriangleArea, FiniteSum.Fin.sumFin_add, -eq_self, -iff_self]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.TwoSheetRequest.SelectedSides

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition (selectedBoundaryTriangleArea)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub)

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

/-- Sum the existing fine-side remainders at precisely the selected boundary. Both sheet occurrences are retained before
the physical/interface selection. -/
@[expose] def selectedSideRemainder (perimeters : Matched.FacePerimeters (request := request) cache.normalize i
  j)
    (neighbors : PuncturedFaces.NeighborBank base.faces) (keep : Fin base.faces.regulars.length → Bool) : Gaussian :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.TwoSheetRequest.SelectedSides.boundaryEvaluation
    neighbors keep
    (fun side p => FiniteSum.Fin.sumFin (fun sheet => HoleAreaRemainder.sideAreaRemainder perimeters p sheet side))

/-- The actual selected side remainder is the retained boundary perimeter minus its original source-triangle correction.
-/
theorem selectedSideRemainder_eq (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (neighbors : PuncturedFaces.NeighborBank base.faces)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    (keep : Fin base.faces.regulars.length → Bool) :
    selectedSideRemainder
      perimeters neighbors keep = FacePerimeters.selectedBoundary perimeters neighbors keep -
      SelectedTrianglePartition.selectedBoundaryTriangleArea neighbors left right keep := by
  have equal (side : GridLiftedDualSteps.GridSide) (p : Fin base.faces.regulars.length) :
      FiniteSum.Fin.sumFin (fun sheet => HoleAreaRemainder.sideAreaRemainder perimeters p sheet side) =
        FacePerimeters.sideSum perimeters side p - FiniteSum.Fin.sumFin (fun sheet => Numerics.sideChord cache.normalize
          i j p sheet side) := by
    cases side <;> exact FiniteSum.Fin.sumFin_sub _ _
  unfold SelectedSideRemainders.LiftedPuncturedGrid.selectedSideRemainder
  rw
    [TwoSheetRequest.SelectedSides.boundaryEvaluation_congr
    neighbors keep equal,
    TwoSheetRequest.SelectedSides.boundaryEvaluation_sub,

      TwoSheetRequest.SelectedSides.boundaryEvaluation_chords
      neighbors left right keep]
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid
