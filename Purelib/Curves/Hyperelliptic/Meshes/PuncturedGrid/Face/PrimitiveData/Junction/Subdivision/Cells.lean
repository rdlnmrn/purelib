module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction.Subdivision
import Purelib.Data.List.Map
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts

/-! # Actual child-owned observations of both retained domains

The original common child outcomes are consumed directly. Each side keeps
its whole original midpoint piece, while the same cached coordinate
positions read two independent policy banks. Only midpoint-start values
are new; every policy endpoint value is reused.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {leftFace rightFace : RegularFace bank}
variable {leftModels : FaceModels frames leftFace} {rightModels : FaceModels frames rightFace}
variable {leftSheet rightSheet : Fin 2}
variable {leftDomain : PeriodDomain leftModels leftSheet} {rightDomain : PeriodDomain rightModels rightSheet}
variable {differential : Differential genus} {leftIndex rightIndex : Nat}
variable {leftData : DomainPrimitives leftDomain differential leftIndex}
variable {rightData : DomainPrimitives rightDomain differential rightIndex}
variable {ambient : Box} {first last : Canonical} {source : ClearSegment curve.polynomial ambient first last}
variable {leftSize rightSize : Nat} {leftPoints : Fin leftSize → Canonical} {rightPoints : Fin rightSize → Canonical}
variable {leftOld : PointReadings leftData.anchors leftData.offsets leftPoints}
variable {rightOld : PointReadings rightData.anchors rightData.offsets rightPoints}
variable {leftFirst leftLast : Fin leftSize} {rightFirst rightLast : Fin rightSize}
variable {leftFirst_eq : leftPoints leftFirst = first} {leftLast_eq : leftPoints leftLast = last}
variable {rightFirst_eq : rightPoints rightFirst = first} {rightLast_eq : rightPoints rightLast = last}
variable (retained : Subdivision leftData rightData source leftOld rightOld leftFirst leftLast rightFirst rightLast
  leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq)

section GeometricReadback

variable {columns rows : Nat} {geometry : Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
variable (piece : SegmentPiece geometry first last) (interval : Interval)
variable (same : piece.interval = interval)

include same in
/-- The actual first-piece coordinate is the SAME original cleared-source point at the common lower parameter. -/
theorem piece_first_point : piece.firstPoint = source.pointAt interval.lower := by
  have moved : PreparedSegmentCuts.point first last piece.interval.lower =
      PreparedSegmentCuts.point first last interval.lower :=
    congrArg (fun item : Interval => PreparedSegmentCuts.point first last item.lower) same
  have readback : source.pointAt interval.lower = PreparedSegmentCuts.point first last interval.lower :=
    source_point_eq source interval.lower
  exact (piece.first_eq.trans moved).trans readback.symm

include same in
/-- The actual last-piece coordinate is the SAME original cleared-source point at the common upper parameter. -/
theorem piece_last_point : piece.lastPoint = source.pointAt interval.upper := by
  have moved : PreparedSegmentCuts.point first last piece.interval.upper =
      PreparedSegmentCuts.point first last interval.upper :=
    congrArg (fun item : Interval => PreparedSegmentCuts.point first last item.upper) same
  have readback : source.pointAt interval.upper = PreparedSegmentCuts.point first last interval.upper :=
    source_point_eq source interval.upper
  exact (piece.last_eq.trans moved).trans readback.symm

include same in
/-- Original whole-piece containment supplies the actual cleared-source lower endpoint in that exact old cell. -/
theorem piece_first_inside : (geometry.box piece.column piece.row).Contains (source.pointAt interval.lower) :=
  Eq.mp (congrArg (geometry.box piece.column piece.row).Contains
    (piece_first_point (source := source) piece interval same))
    piece.first_inside

include same in
/-- Original whole-piece containment supplies the actual cleared-source upper endpoint in that exact old cell. -/
theorem piece_last_inside : (geometry.box piece.column piece.row).Contains (source.pointAt interval.upper) :=
  Eq.mp (congrArg (geometry.box piece.column piece.row).Contains
    (piece_last_point (source := source) piece interval same))
    piece.last_inside

end GeometricReadback

variable (child : CommonChild leftDomain.cuts rightDomain.cuts first last retained.common.partition)

/-- A child retains its original outcomes, actual pieces, parameter selections and both reading factories. -/
abbrev Cell :=
  {value : CommonChild leftDomain.cuts rightDomain.cuts first last retained.common.partition // value = child} ×
  (Σ left : {value : SegmentPiece leftDomain.geometry first last //
      (match child.2.1 with | Sum.inl ready => some ready.2.val | Sum.inr _ => none) = some value ∧
        value.interval = child.1.val},
  Σ right : {value : SegmentPiece rightDomain.geometry first last //
      (match child.2.2 with | Sum.inl ready => some ready.2.val | Sum.inr _ => none) = some value ∧
        value.interval = child.1.val},
  Σ lower : {value : Position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common
    child.1.val.lower //
      value = position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common child.1.val.lower
        (endpoints_mem (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common child).1},
  Σ upper : {value : Position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common
    child.1.val.upper //
      value = position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common child.1.val.upper
        (endpoints_mem (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common child).2},
  {value : PointReadings leftData.anchors leftData.offsets (childPoints (leftDomain := leftDomain) (rightDomain :=
    rightDomain) source retained.common child) //
      value = mix leftData retained.left.readings (source.pointAt child.1.val.lower)
        (source.pointAt child.1.val.upper) lower.val.val.index upper.val.val.index
        (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) lower.val))
          (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) upper.val))
        left.val.column left.val.row (piece_first_inside (source := source) left.val child.1.val left.property.2)} ×
  {value : PointReadings rightData.anchors rightData.offsets (childPoints (leftDomain := leftDomain) (rightDomain :=
    rightDomain) source retained.common child) //
      value = mix rightData retained.right.readings (source.pointAt child.1.val.lower)
        (source.pointAt child.1.val.upper) lower.val.val.index upper.val.val.index
        (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) lower.val))
          (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) upper.val))
        right.val.column right.val.row (piece_first_inside (source := source) right.val child.1.val right.property.2)})

/-- Materialize both original child observations while consuming the SAME retained common outcomes.

Original endpoint-bank containment rules out negative grid coverage here.
The negative branches are inspected rather than executing assignAttempt
again. Both actual original pieces and all common cache identities survive.
-/
def observeChild : Cell retained child := by
  have within := retained.common.partition.interval_bounds child.1.property
  have middle := PreparedSegmentCuts.midpoint_bounds child.1.val
  have unit := And.intro (within.1.trans middle.1.le) (middle.2.le.trans within.2)
  have leftCovered := leftDomain.covers
    (SegmentReadings.source_inside leftData source leftOld leftFirst leftLast leftFirst_eq leftLast_eq unit)
  have rightCovered := rightDomain.covers
    (SegmentReadings.source_inside rightData source rightOld rightFirst rightLast rightFirst_eq rightLast_eq unit)
  have equal := source_point_eq source ((child.1.val.lower + child.1.val.upper) / 2)
  have leftInside := Eq.mp (congrArg (Geometry.Covers leftDomain.geometry) equal) leftCovered
  have rightInside := Eq.mp (congrArg (Geometry.Covers rightDomain.geometry) equal) rightCovered
  match leftCase : child.2.1 with
  | Sum.inr missing => exact False.elim (missing.property leftInside)
  | Sum.inl left =>
    match rightCase : child.2.2 with
    | Sum.inr missing => exact False.elim (missing.property rightInside)
    | Sum.inl right =>
      let lower := position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common
        child.1.val.lower (endpoints_mem (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common
        child).1
      let upper := position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common
        child.1.val.upper (endpoints_mem (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common
        child).2
      have leftInterval := CommonChild.left_interval (leftCuts := leftDomain.cuts) (rightCuts := rightDomain.cuts)
        (first := first) (last := last) (partition := retained.common.partition) child left.1 left.2
      have rightInterval := CommonChild.right_interval (leftCuts := leftDomain.cuts) (rightCuts := rightDomain.cuts)
        (first := first) (last := last) (partition := retained.common.partition) child right.1 right.2
      let first := mix leftData retained.left.readings (source.pointAt child.1.val.lower)
        (source.pointAt child.1.val.upper) lower.val.index upper.val.index
        (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) lower))
          (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) upper))
        left.2.val.column left.2.val.row (piece_first_inside (source := source) left.2.val child.1.val leftInterval)
      let last := mix rightData retained.right.readings (source.pointAt child.1.val.lower)
        (source.pointAt child.1.val.upper) lower.val.index upper.val.index
        (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) lower))
          (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) upper))
        right.2.val.column right.2.val.row (piece_first_inside (source := source) right.2.val child.1.val rightInterval)
      exact (⟨child, rfl⟩, ⟨⟨left.2.val, by rw [leftCase]; exact ⟨rfl, leftInterval⟩⟩,
        ⟨right.2.val, by rw [rightCase]; exact ⟨rfl, rightInterval⟩⟩,
        ⟨lower, rfl⟩, ⟨upper, rfl⟩, ⟨first, rfl⟩, ⟨last, rfl⟩⟩)

namespace Cell

variable {retained child} (cell : Cell retained child)

/-- Read the complete original left midpoint-selected piece. -/
abbrev left : SegmentPiece leftDomain.geometry first last := cell.2.1.val

/-- Read the complete original right midpoint-selected piece. -/
abbrev right : SegmentPiece rightDomain.geometry first last := cell.2.2.1.val

/-- Read the SAME retained lower coordinate selection. -/
abbrev lower : Position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common child.1.val.lower :=
  cell.2.2.2.1.val

/-- Read the SAME retained upper coordinate selection. -/
abbrev upper : Position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common child.1.val.upper :=
  cell.2.2.2.2.1.val

/-- Read all three distinct actual left reading occurrences. -/
abbrev leftReadings : PointReadings leftData.anchors leftData.offsets (childPoints (leftDomain := leftDomain)
  (rightDomain := rightDomain) source retained.common child) :=
  cell.2.2.2.2.2.1.val

/-- Read all three distinct actual right reading occurrences. -/
abbrev rightReadings : PointReadings rightData.anchors rightData.offsets (childPoints (leftDomain := leftDomain)
  (rightDomain := rightDomain) source retained.common child) :=
  cell.2.2.2.2.2.2.val

/-- The whole left original piece belongs to the SAME common ordinal interval. -/
theorem left_interval : cell.left.interval = child.1.val := cell.2.1.property.2

/-- The whole right original piece belongs to the SAME common ordinal interval. -/
theorem right_interval : cell.right.interval = child.1.val := cell.2.2.1.property.2

/-- The whole left reading factory reuses the actual policy endpoint caches. -/
theorem left_eq : cell.leftReadings = mix leftData retained.left.readings (source.pointAt child.1.val.lower)
    (source.pointAt child.1.val.upper) cell.lower.val.index cell.upper.val.index
    (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) cell.lower))
      (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) cell.upper))
    cell.left.column cell.left.row (piece_first_inside (source := source) cell.left child.1.val cell.left_interval) :=
  cell.2.2.2.2.2.1.property

/-- The whole right reading factory reuses the independently retained right policy endpoint caches. -/
theorem right_eq : cell.rightReadings = mix rightData retained.right.readings (source.pointAt child.1.val.lower)
    (source.pointAt child.1.val.upper) cell.lower.val.index cell.upper.val.index
    (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) cell.lower))
      (congrArg source.pointAt (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) cell.upper))
    cell.right.column cell.right.row
      (piece_first_inside (source := source) cell.right child.1.val cell.right_interval) :=
  cell.2.2.2.2.2.2.property

end Cell

/-- Retain the whole input subdivision and every actual child observation in its original order. -/
abbrev Observed :=
  Σ original : {value : Subdivision leftData rightData source leftOld rightOld leftFirst leftLast rightFirst rightLast
      leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq // value = retained},
  {value : List (Σ child : CommonChild leftDomain.cuts rightDomain.cuts first last original.val.common.partition,
      Cell original.val child) //
    value = original.val.common.children.map (fun child => ⟨child, observeChild original.val child⟩)}

/-- Observe each actual ordered child once, sharing both cached parameter reading banks throughout. -/
def observe : Observed retained :=
  let cells := retained.common.children.map (fun child => ⟨child, observeChild retained child⟩)
  ⟨⟨retained, rfl⟩, ⟨cells, rfl⟩⟩

namespace Observed

variable {retained} (observed : Observed retained)

/-- Read the complete original paired subdivision retained by this ordered observation bank. -/
abbrev original : Subdivision leftData rightData source leftOld rightOld leftFirst leftLast rightFirst rightLast
    leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq := observed.1.val

/-- Read every actual observed child in its retained original order and original partition. -/
abbrev cells : List (Σ child : CommonChild leftDomain.cuts rightDomain.cuts first last
    observed.original.common.partition, Cell observed.original child) := observed.2.val

/-- The ordered bank retains the complete supplied paired subdivision. -/
theorem original_eq : observed.original = retained := observed.1.property

/-- The actual ordered child list retains its complete observation factory. -/
theorem cells_eq : observed.cells = observed.original.common.children.map
    (fun child => ⟨child, observeChild observed.original child⟩) := observed.2.property

end Observed

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

end
