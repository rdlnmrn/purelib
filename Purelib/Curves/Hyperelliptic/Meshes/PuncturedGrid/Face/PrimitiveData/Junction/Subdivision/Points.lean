module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction.Subdivision.Payment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Connections.ContinuedPoints
public import Purelib.Data.Vector.Dependent

/-! # Materialized Point/Entry continuations on the actual common coordinate bank

Both original source preparations and old numerical domains remain whole.
Each retained common parameter gets one continuation result; neighboring
children read that same stored position. Child preparations are constructed,
while the original finite numerical payment can still be unpaid.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (CommonChild)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {leftFace rightFace : RegularFace bank}
variable {leftModels : FaceModels frames leftFace} {rightModels : FaceModels frames rightFace}
variable {first last : Canonical}
variable (leftPoint rightPoint : Entry.PointData (curve := curve) first)
variable (leftEntry : Entry leftModels first leftPoint.sample.owner)
variable (rightEntry : Entry rightModels first rightPoint.sample.owner)
variable (sourceJoin : OwnerJoin leftPoint.sample.owner rightPoint.sample.owner)
variable {leftDomain : PeriodDomain leftModels leftEntry.sheet}
variable {rightDomain : PeriodDomain rightModels rightEntry.sheet}
variable {differential : Differential genus} {leftIndex rightIndex : Nat}
variable {leftData : DomainPrimitives leftDomain differential leftIndex}
variable {rightData : DomainPrimitives rightDomain differential rightIndex}
variable {ambient : Box} {source : ClearSegment curve.polynomial ambient first last}
variable {leftSize rightSize : Nat} {leftPoints : Fin leftSize → Canonical} {rightPoints : Fin rightSize → Canonical}
variable {leftOld : PointReadings leftData.anchors leftData.offsets leftPoints}
variable {rightOld : PointReadings rightData.anchors rightData.offsets rightPoints}
variable {leftFirst leftLast : Fin leftSize} {rightFirst rightLast : Fin rightSize}
variable {leftFirst_eq : leftPoints leftFirst = first} {leftLast_eq : leftPoints leftLast = last}
variable {rightFirst_eq : rightPoints rightFirst = first} {rightLast_eq : rightPoints rightLast = last}
variable (retained : Subdivision leftData rightData source leftOld rightOld leftFirst leftLast rightFirst rightLast
  leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq)

namespace Points

/-- The literal original source coordinate at one actual common parameter position. -/
abbrev point (position : Fin retained.common.partition.coordinates.length) : Canonical :=
  source.pointAt (retained.common.partition.coordinates[position.val]'position.isLt)

/-- The original left numerical owner bank proves containment of this actual coordinate in its SAME old face. -/
theorem left_inside (position : Fin retained.common.partition.coordinates.length) :
    leftFace.cell.box.Contains (point leftPoint rightPoint leftEntry rightEntry retained position) :=
  SegmentReadings.source_inside leftData source leftOld leftFirst leftLast leftFirst_eq leftLast_eq
    (retained.common.partition.coordinate_bounds (List.getElem_mem position.isLt))

/-- The independent right old domain proves containment without identifying any owner or reading. -/
theorem right_inside (position : Fin retained.common.partition.coordinates.length) :
    rightFace.cell.box.Contains (point leftPoint rightPoint leftEntry rightEntry retained position) :=
  SegmentReadings.source_inside rightData source rightOld rightFirst rightLast rightFirst_eq rightLast_eq
    (retained.common.partition.coordinate_bounds (List.getElem_mem position.isLt))

end Points

/-- Both original source caches and one actual endpoint vector retain their complete factories. -/
abbrev Points :=
  {value : Subdivision leftData rightData source leftOld rightOld leftFirst leftLast rightFirst rightLast
      leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq // value = retained} ×
  (Σ initial : {value : Entry.JunctionData.Initial
      (firstLeft := SegmentReadings.first_inside leftData leftOld leftFirst leftFirst_eq)
      (firstRight := SegmentReadings.first_inside rightData rightOld rightFirst rightFirst_eq)
      leftPoint rightPoint leftEntry rightEntry sourceJoin //
    value = Entry.JunctionData.Initial.build
      (firstLeft := SegmentReadings.first_inside leftData leftOld leftFirst leftFirst_eq)
      (firstRight := SegmentReadings.first_inside rightData rightOld rightFirst rightFirst_eq)
      leftPoint rightPoint leftEntry rightEntry sourceJoin},
  {value : DependentVector (fun position : Fin retained.common.partition.coordinates.length =>
      Entry.JunctionData.Continuation initial.val.value
        (Points.left_inside leftPoint rightPoint leftEntry rightEntry retained position)
        (Points.right_inside leftPoint rightPoint leftEntry rightEntry retained position) genus) //
    value = DependentVector.ofFn (fun position => initial.val.value.continueAt
      (Points.left_inside leftPoint rightPoint leftEntry rightEntry retained position)
      (Points.right_inside leftPoint rightPoint leftEntry rightEntry retained position) genus)})

namespace Points

/-- Materialize source acquisitions once, then one continuation for each actual common parameter occurrence.

Only new non-source endpoints acquire traces, Points, both face Entries
and their actual owner join. Source-equal targets reuse the complete old
Point/join pair and the once-built initial acquisitions. Both original bare
Entries and their independent old domain owners remain retained.
-/
def build : Points leftPoint rightPoint leftEntry rightEntry sourceJoin retained :=
  let initial := Entry.JunctionData.Initial.build
    (firstLeft := SegmentReadings.first_inside leftData leftOld leftFirst leftFirst_eq)
    (firstRight := SegmentReadings.first_inside rightData rightOld rightFirst rightFirst_eq)
    leftPoint rightPoint leftEntry rightEntry sourceJoin
  let vertices := DependentVector.ofFn fun position => initial.value.continueAt
    (left_inside leftPoint rightPoint leftEntry rightEntry retained position)
    (right_inside leftPoint rightPoint leftEntry rightEntry retained position) genus
  (⟨retained, rfl⟩, ⟨⟨initial, rfl⟩, ⟨vertices, rfl⟩⟩)

variable {leftPoint rightPoint leftEntry rightEntry sourceJoin retained}
variable (cached : Points leftPoint rightPoint leftEntry rightEntry sourceJoin retained)

/-- Read the whole retained original source pair and its actual two acquired Entry caches. -/
abbrev initial : Entry.JunctionData.Initial
    (firstLeft := SegmentReadings.first_inside leftData leftOld leftFirst leftFirst_eq)
    (firstRight := SegmentReadings.first_inside rightData rightOld rightFirst rightFirst_eq)
    leftPoint rightPoint leftEntry rightEntry sourceJoin := cached.2.1.val

/-- Read the complete endpoint vector; no continuation factory executes in lookup. -/
abbrev vertices : DependentVector (fun position : Fin retained.common.partition.coordinates.length =>
    Entry.JunctionData.Continuation cached.initial.value
      (left_inside leftPoint rightPoint leftEntry rightEntry retained position)
      (right_inside leftPoint rightPoint leftEntry rightEntry retained position) genus) := cached.2.2.val

/-- Read the SAME cached continuation at this actual bounded original parameter position. -/
abbrev vertex (position : Fin retained.common.partition.coordinates.length) :
    Entry.JunctionData.Continuation cached.initial.value
      (left_inside leftPoint rightPoint leftEntry rightEntry retained position)
      (right_inside leftPoint rightPoint leftEntry rightEntry retained position) genus := cached.vertices.get position

/-- The initial actual source acquisition keeps its whole original factory. -/
theorem initial_eq : cached.initial = Entry.JunctionData.Initial.build
    (firstLeft := SegmentReadings.first_inside leftData leftOld leftFirst leftFirst_eq)
    (firstRight := SegmentReadings.first_inside rightData rightOld rightFirst rightFirst_eq)
    leftPoint rightPoint leftEntry rightEntry sourceJoin :=
  cached.2.1.property

/-- The entire endpoint vector retains its complete materialization factory. -/
theorem vertices_eq : cached.vertices = DependentVector.ofFn (fun position => cached.initial.value.continueAt
    (left_inside leftPoint rightPoint leftEntry rightEntry retained position)
    (right_inside leftPoint rightPoint leftEntry rightEntry retained position) genus) := cached.2.2.property

variable {child : CommonChild leftDomain.cuts rightDomain.cuts first last retained.common.partition}
variable (cell : Cell retained child)

/-- The retained child's actual first-occurrence position is its literal source lower endpoint. -/
theorem lower_point :
    point leftPoint rightPoint leftEntry rightEntry retained cell.lower.val.index =
      source.pointAt child.1.val.lower :=
  congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) cell.lower)

/-- Construct the original child preparation from one actual stored endpoint continuation.

The whole result crosses only its bounded point-index readback. Both
Points/acquisitions/join are the stored values, with no new classification,
Point, trace, observation or preparation during this child lookup.
-/
def forCell : Cell.LowerData cell :=
  (cached.vertex cell.lower.val.index).value.castPoint (lower_point cell).symm cell.left_inside cell.right_inside

/-- The actual constructed left child Entry has the old domain's derived original source sheet. -/
theorem forCell_left_sheet : (cached.forCell cell).leftAcquired.entry.sheet = leftEntry.sheet := by
  unfold forCell
  exact ((cached.vertex cell.lower.val.index).value.castPoint_left_sheet
    (lower_point cell).symm cell.left_inside cell.right_inside).trans
      ((cached.vertex cell.lower.val.index).left_sheet.trans cached.initial.left_sheet)

/-- The independent right child Entry retains its own original source/domain sheet. -/
theorem forCell_right_sheet :
    (cached.forCell cell).rightAcquired.entry.sheet = rightEntry.sheet := by
  unfold forCell
  exact ((cached.vertex cell.lower.val.index).value.castPoint_right_sheet
    (lower_point cell).symm cell.left_inside cell.right_inside).trans
      ((cached.vertex cell.lower.val.index).right_sheet.trans cached.initial.right_sheet)

/-- Retain the actual constructed child preparation and complete original finite payment attempt. -/
abbrev ChildAttempt (target : Rational) :=
  Σ lower : {value : Cell.LowerData cell // value = cached.forCell cell},
    {value : cell.Attempt (some lower.val) target // value = cell.attempt (some lower.val) target}

/-- Run the real common-child comparison/payment consumer with internally constructed Point/Entry/join caches.

The two selected-sheet facts above are derived from the old source Entries
and same actual trace. The original finite checker still retains its real
payment failure when existing numerical stages are insufficient; no final
accuracy or desired comparison is an input.
-/
def attemptCell (target : Rational) : cached.ChildAttempt cell target :=
  let lower := cached.forCell cell
  let result := cell.attempt (some lower) target
  ⟨⟨lower, rfl⟩, ⟨result, rfl⟩⟩

end Points

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

end
