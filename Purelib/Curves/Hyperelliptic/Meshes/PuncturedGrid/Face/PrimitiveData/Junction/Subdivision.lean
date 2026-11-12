module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.SegmentReadings
public import Purelib.Riemann.Paths.RectangularSegmentSplitting.CommonSplit
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Data.List.Search
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
import Purelib.Data.Fin
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Polynomial.Geometry.ClearPath

/-! # Actual paired old-domain readings on one retained common source subdivision

Both original numerical domains and endpoint banks remain distinct. One
shared parameter partition drives two independent reading vectors. Child
midpoint owners and old boundary-tie owners retain separate observations.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction

open Purelib
open Purelib.Data
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.RectangularSegmentSplitting
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {leftFace rightFace : RegularFace bank}
variable {leftModels : FaceModels frames leftFace} {rightModels : FaceModels frames rightFace}
variable {leftSheet rightSheet : Fin 2}
variable {leftDomain : PeriodDomain leftModels leftSheet} {rightDomain : PeriodDomain rightModels rightSheet}
variable {differential : Differential genus} {leftIndex rightIndex : Nat}
variable (leftData : DomainPrimitives leftDomain differential leftIndex)
variable (rightData : DomainPrimitives rightDomain differential rightIndex)
variable {ambient : Box} {first last : Canonical} (source : ClearSegment curve.polynomial ambient first last)
variable {leftSize rightSize : Nat} {leftPoints : Fin leftSize → Canonical} {rightPoints : Fin rightSize → Canonical}
variable (leftOld : PointReadings leftData.anchors leftData.offsets leftPoints)
variable (rightOld : PointReadings rightData.anchors rightData.offsets rightPoints)
variable (leftFirst leftLast : Fin leftSize) (rightFirst rightLast : Fin rightSize)
variable (leftFirst_eq : leftPoints leftFirst = first) (leftLast_eq : leftPoints leftLast = last)
variable (rightFirst_eq : rightPoints rightFirst = first) (rightLast_eq : rightPoints rightLast = last)

namespace Subdivision

/-- Every common retained coordinate is a unit parameter on the SAME original source segment. -/
theorem parameters_inside (common : CommonSplit leftDomain.cuts rightDomain.cuts first last) :
    ∀ parameter ∈ common.partition.coordinates, 0 ≤ parameter ∧ parameter ≤ 1 :=
  fun _ member => common.partition.coordinate_bounds member

include leftData rightData leftOld rightOld leftFirst leftLast rightFirst rightLast
  leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq in
/-- Existing original endpoint observations discharge both domain coverages without a new success premise. -/
theorem no_coverage_requests (common : CommonSplit leftDomain.cuts rightDomain.cuts first last) :
    common.requests = [] :=
  common.requests_nil
    (leftDomain.covers (SegmentReadings.first_inside leftData leftOld leftFirst leftFirst_eq))
    (leftDomain.covers (SegmentReadings.last_inside leftData leftOld leftLast leftLast_eq))
    (rightDomain.covers (SegmentReadings.first_inside rightData rightOld rightFirst rightFirst_eq))
    (rightDomain.covers (SegmentReadings.last_inside rightData rightOld rightLast rightLast_eq))

/-- The original cleared source point is the affine coordinate used by the common grid partition. -/
theorem source_point_eq (parameter : Rational) :
    source.pointAt parameter = PreparedSegmentCuts.point first last parameter :=
  (ClearSegment.pointAt_eq_line source parameter).trans
    (PreparedSegmentCuts.point_eq_line first last parameter).symm

/-- Keep a complete actual first-occurrence scan at a retained partition coordinate. -/
abbrev Position (common : CommonSplit leftDomain.cuts rightDomain.cuts first last) (parameter : Rational) :=
  {selected : Search.Occurrence (fun value : Rational => value = parameter) common.partition.coordinates //
    Search.firstOccurrence (fun value => value = parameter) (fun _ => inferInstance)
      common.partition.coordinates = some selected}

/-- Read an actual coordinate position; its complete original finite selection remains cached. -/
def position (common : CommonSplit leftDomain.cuts rightDomain.cuts first last) (parameter : Rational)
    (member : parameter ∈ common.partition.coordinates) : Position (leftDomain := leftDomain) (rightDomain :=
      rightDomain) common parameter :=
  Search.firstAccepted (fun value => value = parameter) (fun _ => inferInstance)
    common.partition.coordinates ⟨parameter, member, rfl⟩

/-- The cached coordinate selection identifies its actual bounded parameter, without comparing root owners. -/
theorem position_eq {common : CommonSplit leftDomain.cuts rightDomain.cuts first last} {parameter : Rational}
    (selected : Position (leftDomain := leftDomain) (rightDomain := rightDomain) common parameter) :
    common.partition.coordinates[selected.val.index.val]'selected.val.index.isLt = parameter :=
  selected.val.entry_eq.symm.trans selected.val.accepted

/-- Both endpoints of an actual common child occur in the SAME retained coordinate list. -/
theorem endpoints_mem (common : CommonSplit leftDomain.cuts rightDomain.cuts first last)
    (child : CommonChild leftDomain.cuts rightDomain.cuts first last common.partition) :
    child.1.val.lower ∈ common.partition.coordinates ∧ child.1.val.upper ∈ common.partition.coordinates :=
  Purelib.Polynomial.Geometry.Grid.ClearGrid.Interval.endpoints_mem common.partition.coordinates
    common.partition.ordered
    (Eq.mp (congrArg (fun intervals => child.1.val ∈ intervals) common.partition.intervals_eq) child.1.property)

/-- The three literal reading occurrences retain midpoint start, old-policy start and old-policy finish separately. -/
abbrev childPoints (common : CommonSplit leftDomain.cuts rightDomain.cuts first last)
    (child : CommonChild leftDomain.cuts rightDomain.cuts first last common.partition) : Fin 3 → Canonical :=
  Fin.cases (source.pointAt child.1.val.lower)
    (fun index => Fin.cases (source.pointAt child.1.val.lower) (fun _ => source.pointAt child.1.val.upper) index)

end Subdivision

/-- The actual common partition and BOTH independent domain reading caches retain their complete factories. -/
abbrev Subdivision :=
  Σ common : {value : CommonSplit leftDomain.cuts rightDomain.cuts first last //
      value = CommonSplit.build leftDomain.cuts rightDomain.cuts first last},
  {value : SegmentReadings leftData source leftOld leftFirst leftLast leftFirst_eq leftLast_eq
      common.val.partition.coordinates (Subdivision.parameters_inside (leftDomain := leftDomain) (rightDomain :=
        rightDomain) common.val) //
    value = SegmentReadings.build leftData source leftOld leftFirst leftLast leftFirst_eq leftLast_eq
      common.val.partition.coordinates (Subdivision.parameters_inside (leftDomain := leftDomain) (rightDomain :=
        rightDomain) common.val)} ×
  {value : SegmentReadings rightData source rightOld rightFirst rightLast rightFirst_eq rightLast_eq
      common.val.partition.coordinates (Subdivision.parameters_inside (leftDomain := leftDomain) (rightDomain :=
        rightDomain) common.val) //
    value = SegmentReadings.build rightData source rightOld rightFirst rightLast rightFirst_eq rightLast_eq
      common.val.partition.coordinates (Subdivision.parameters_inside (leftDomain := leftDomain) (rightDomain :=
        rightDomain) common.val)}

namespace Subdivision

/-- Build one common geometric cache, then two independent reading vectors on its SAME coordinate positions. -/
def build : Subdivision leftData rightData source leftOld rightOld leftFirst leftLast rightFirst rightLast
    leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq :=
  let common := CommonSplit.build leftDomain.cuts rightDomain.cuts first last
  let left := SegmentReadings.build leftData source leftOld leftFirst leftLast leftFirst_eq leftLast_eq
    common.partition.coordinates (parameters_inside (leftDomain := leftDomain) (rightDomain := rightDomain) common)
  let right := SegmentReadings.build rightData source rightOld rightFirst rightLast rightFirst_eq rightLast_eq
    common.partition.coordinates (parameters_inside (leftDomain := leftDomain) (rightDomain := rightDomain) common)
  ⟨⟨common, rfl⟩, ⟨left, rfl⟩, ⟨right, rfl⟩⟩

variable {leftData rightData source leftOld rightOld leftFirst leftLast rightFirst rightLast}
variable {leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq}
variable (retained : Subdivision leftData rightData source leftOld rightOld leftFirst leftLast rightFirst rightLast
  leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq)

/-- Read the one whole common geometry cache, preserving both original grid outcomes for every child. -/
abbrev common : CommonSplit leftDomain.cuts rightDomain.cuts first last := retained.1.val

/-- Read the original left-domain reading cache with its unchanged endpoint owners, anchors and offsets. -/
abbrev left : SegmentReadings leftData source leftOld leftFirst leftLast leftFirst_eq leftLast_eq
    retained.common.partition.coordinates (parameters_inside (leftDomain := leftDomain) (rightDomain := rightDomain)
      retained.common) := retained.2.1.val

/-- Read the distinct right-domain reading cache with its own endpoint owners, anchors and offsets. -/
abbrev right : SegmentReadings rightData source rightOld rightFirst rightLast rightFirst_eq rightLast_eq
    retained.common.partition.coordinates (parameters_inside (leftDomain := leftDomain) (rightDomain := rightDomain)
      retained.common) := retained.2.2.val

/-- The retained common cache is its complete original factory. -/
theorem common_eq : retained.common = CommonSplit.build leftDomain.cuts rightDomain.cuts first last :=
  retained.1.property

/-- Actual original endpoint owner containment resolves every retained geometric coverage request. -/
theorem requests_nil : retained.common.requests = [] :=
  no_coverage_requests leftData rightData leftOld rightOld leftFirst leftLast rightFirst rightLast
    leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq retained.common

section OneCell

variable {face : RegularFace bank} {models : FaceModels frames face} {sheet : Fin 2}
variable {domain : PeriodDomain models sheet} {index size : Nat} {points : Fin size → Canonical}
variable (data : DomainPrimitives domain differential index)
variable (readings : PointReadings data.anchors data.offsets points)
variable (lower upper : Canonical) (lowerPosition upperPosition : Fin size)
variable (lower_eq : points lowerPosition = lower) (upper_eq : points upperPosition = upper)
variable (column : Fin (domain.steps + 1)) (row : Fin (domain.steps + 1))
variable (lowerInside : (domain.geometry.box column row).Contains lower)

/-- Assemble the three SAME-domain reading occurrences, adding only the actual midpoint-cell start evaluation.

The policy endpoint owners and values are read directly from their retained
bank positions. The midpoint start may have another original cell owner;
its scalar gap is preserved for payment rather than normalized away.
-/
def mix : PointReadings data.anchors data.offsets
    (Fin.cases lower (fun index => Fin.cases lower (fun _ => upper) index) : Fin 3 → Canonical) :=
  let owned : OwnedVertex domain.geometry := ⟨column, row, lower, lowerInside⟩
  let first := data.anchors.alignedValue data.offsets column row lower
  { owners := vectorOfFn (Fin.cases owned (fun index =>
      Fin.cases (readings.owners lowerPosition) (fun _ => readings.owners upperPosition) index))
    point_eq := fun index => Fin.cases_induction (by rewrite [vectorOfFn_apply]; rfl)
      (fun index => Fin.cases_induction
        (by rw [vectorOfFn_apply]; exact (readings.point_eq lowerPosition).trans lower_eq)
        (fun _ => by rw [vectorOfFn_apply]; exact (readings.point_eq upperPosition).trans upper_eq) index) index
    values := vectorOfFn (Fin.cases first (fun index =>
      Fin.cases (readings.values lowerPosition) (fun _ => readings.values upperPosition) index))
    value_eq := fun index => Fin.cases_induction (by rewrite [vectorOfFn_apply, vectorOfFn_apply]; rfl)
      (fun index => Fin.cases_induction
        (by rw [vectorOfFn_apply, vectorOfFn_apply]; exact readings.value_eq lowerPosition)
        (fun _ => by rw [vectorOfFn_apply, vectorOfFn_apply]; exact readings.value_eq upperPosition) index) index }

/-- The selected midpoint-start numerical owner is exactly the supplied original cell and lower coordinate. -/
theorem mix_owner_zero :
    (mix data readings lower upper lowerPosition upperPosition lower_eq upper_eq column row lowerInside).owners 0 =
      ⟨column, row, lower, lowerInside⟩ := by
  unfold mix
  rewrite [vectorOfFn_apply]
  rfl

/-- The first policy endpoint reading is reused as its original cached scalar. -/
theorem mix_value_one :
    (mix data readings lower upper lowerPosition upperPosition lower_eq upper_eq column row lowerInside).values 1 =
      readings.values lowerPosition := by
  unfold mix
  rewrite [vectorOfFn_apply]
  rfl

/-- The final policy endpoint reading is reused as its original cached scalar. -/
theorem mix_value_two :
    (mix data readings lower upper lowerPosition upperPosition lower_eq upper_eq column row lowerInside).values 2 =
      readings.values upperPosition := by
  unfold mix
  rewrite [vectorOfFn_apply]
  rfl

end OneCell

end Subdivision

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction

end
