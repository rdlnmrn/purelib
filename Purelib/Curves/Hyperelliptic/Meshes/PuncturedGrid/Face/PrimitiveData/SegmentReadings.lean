module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Integration.RectangularOwnedTriangulation

/-! # Retained segment readings with exact reuse of both original endpoint observations

The original endpoint owner/value pairs remain literal. Only interior
parameters locate a new numerical owner and evaluate its original aligned
primitive. One materialized vector serves every subsequent child lookup.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply map_apply)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels frames face}
variable {sheet : Fin 2} {domain : PeriodDomain models sheet} {differential : Differential genus} {index : Nat}
variable (data : DomainPrimitives domain differential index)
variable {ambient : Box} {first last : Canonical} (source : ClearSegment curve.polynomial ambient first last)
variable {oldSize : Nat} {oldPoints : Fin oldSize → Canonical}
variable (oldReadings : PointReadings data.anchors data.offsets oldPoints)
variable (oldFirst oldLast : Fin oldSize) (first_eq : oldPoints oldFirst = first) (last_eq : oldPoints oldLast = last)

namespace SegmentReadings

include data oldReadings oldFirst first_eq in
/-- The actual original start reading owner proves source-start containment in the same old face. -/
theorem first_inside : face.cell.box.Contains first :=
  (domain.patch.cell_refines (oldReadings.owners oldFirst).column (oldReadings.owners oldFirst).row).contains
    (Eq.mp (congrArg (domain.geometry.box (oldReadings.owners oldFirst).column
      (oldReadings.owners oldFirst).row).Contains ((oldReadings.point_eq oldFirst).trans first_eq))
      (oldReadings.owners oldFirst).contains)

include data oldReadings oldLast last_eq in
/-- The actual original finish reading owner proves source-finish containment in the same old face. -/
theorem last_inside : face.cell.box.Contains last :=
  (domain.patch.cell_refines (oldReadings.owners oldLast).column (oldReadings.owners oldLast).row).contains
    (Eq.mp (congrArg (domain.geometry.box (oldReadings.owners oldLast).column
      (oldReadings.owners oldLast).row).Contains ((oldReadings.point_eq oldLast).trans last_eq))
      (oldReadings.owners oldLast).contains)

include data oldReadings oldFirst oldLast first_eq last_eq in
/-- Every unit-interval point on this literal original segment lies in the same old face. -/
theorem source_inside {parameter : Rational} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    face.cell.box.Contains (source.pointAt parameter) :=
  Eq.mp (congrArg face.cell.box.Contains (ClearSegment.pointAt_eq_line source parameter).symm)
    (Box.contains_line (first_inside data oldReadings oldFirst first_eq)
      (last_inside data oldReadings oldLast last_eq) inside)

/-- A numerical reading retains its original owner and the actual scalar on unchanged anchors and offsets. -/
abbrev Reading :=
  Σ owner : OwnedVertex domain.geometry,
    {value : Canonical // value = data.anchors.alignedValue data.offsets owner.column owner.row owner.point}

/-- One original segment parameter keeps its complete numerical reading and exact original source incidence. -/
abbrev At (parameter : Rational) :=
  {value : Reading data // value.1.point = source.pointAt parameter}

/-- Reuse the exact original endpoint observations, or locate and evaluate one genuine interior reading.

The supplied original point-bank owners imply the whole source's face
containment. Numerical lookup at an interior parameter is new work; no
Point, Query, root, Entry, primitive polynomial, anchor or offset is built.
-/
def readAt (parameter : Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1) : At data source parameter :=
  if atFirst : parameter = 0 then
    ⟨⟨oldReadings.owners oldFirst, ⟨oldReadings.values oldFirst, oldReadings.value_eq oldFirst⟩⟩,
      ((oldReadings.point_eq oldFirst).trans first_eq).trans
        ((congrArg source.pointAt atFirst).trans source.pointAt_zero).symm⟩
  else if atLast : parameter = 1 then
    ⟨⟨oldReadings.owners oldLast, ⟨oldReadings.values oldLast, oldReadings.value_eq oldLast⟩⟩,
      ((oldReadings.point_eq oldLast).trans last_eq).trans
        ((congrArg source.pointAt atLast).trans source.pointAt_one).symm⟩
  else
    let located := PeriodDomain.locate domain (source.pointAt parameter)
      (source_inside data source oldReadings oldFirst oldLast first_eq last_eq inside)
    let owner : OwnedVertex domain.geometry :=
      ⟨located.column, located.row, source.pointAt parameter, located.inside⟩
    let value := data.anchors.alignedValue data.offsets owner.column owner.row owner.point
    ⟨⟨owner, ⟨value, rfl⟩⟩, rfl⟩

/-- The zero-parameter result keeps the entire old owner/value pair without another primitive evaluation. -/
theorem readAt_zero :
    (readAt data source oldReadings oldFirst oldLast first_eq last_eq 0
      ⟨Basic.le_refl 0, of_decide_eq_true rfl⟩).val =
      ⟨oldReadings.owners oldFirst, ⟨oldReadings.values oldFirst, oldReadings.value_eq oldFirst⟩⟩ := by
  unfold readAt
  rw [dif_pos rfl]

/-- The one-parameter result keeps the entire old owner/value pair without another primitive evaluation. -/
theorem readAt_one :
    (readAt data source oldReadings oldFirst oldLast first_eq last_eq 1
      ⟨of_decide_eq_true rfl, Basic.le_refl 1⟩).val =
      ⟨oldReadings.owners oldLast, ⟨oldReadings.values oldLast, oldReadings.value_eq oldLast⟩⟩ := by
  unfold readAt
  rw [dif_neg (of_decide_eq_true rfl : ¬(1 : Rational) = 0), dif_pos rfl]

variable (parameters : List Rational)
variable (inside : ∀ parameter ∈ parameters, 0 ≤ parameter ∧ parameter ≤ 1)

/-- The actual original segment point at each retained parameter position. -/
abbrev points (position : Fin parameters.length) : Canonical :=
  source.pointAt (parameters[position.val]'position.isLt)

/-- Assemble original PointReadings by mapping the SAME retained owner/value vector, without evaluating a primitive. -/
def ofSamples (samples : Data.Vector (Reading data) parameters.length)
    (same : ∀ position, (samples position).1.point = points source parameters position) :
    PointReadings data.anchors data.offsets (points source parameters) where
  owners := samples.map (fun entry => entry.1)
  point_eq := fun position =>
    (congrArg (fun owner : OwnedVertex domain.geometry => owner.point)
      (map_apply (fun entry : Reading data => entry.1) samples position)).trans (same position)
  values := samples.map (fun entry => entry.2.val)
  value_eq := fun position => by
    rw [map_apply, map_apply]
    exact (samples position).2.property

end SegmentReadings

/-- Retain the finite parameter reading vector, whole original endpoint banks and semantic reading factory. -/
abbrev SegmentReadings (parameters : List Rational)
    (inside : ∀ parameter ∈ parameters, 0 ≤ parameter ∧ parameter ≤ 1) :=
  {value : DomainPrimitives domain differential index × PointReadings data.anchors data.offsets oldPoints ×
      ClearSegment curve.polynomial ambient first last × (Fin oldSize × Fin oldSize) × List Rational //
    value = (data, oldReadings, source, (oldFirst, oldLast), parameters)} ×
  (Σ samples : {value : Data.Vector (SegmentReadings.Reading data) parameters.length //
      value = vectorOfFn (fun position =>
        (SegmentReadings.readAt data source oldReadings oldFirst oldLast first_eq last_eq
          (parameters[position.val]'position.isLt) (inside _ (List.getElem_mem _))).val)},
    {value : PointReadings data.anchors data.offsets (SegmentReadings.points source parameters) //
      value = SegmentReadings.ofSamples data source parameters samples.val (fun position =>
        (congrArg (fun values : Data.Vector (SegmentReadings.Reading data) parameters.length =>
          (values position).1.point) samples.property).trans
          ((congrArg (fun value : SegmentReadings.Reading data => value.1.point)
          (vectorOfFn_apply _ position)).trans
            (SegmentReadings.readAt data source oldReadings oldFirst oldLast first_eq last_eq
              (parameters[position.val]'position.isLt) (inside _ (List.getElem_mem _))).property))})

namespace SegmentReadings

/-- Materialize each retained parameter once, preserving old 0/1 readings and both original cache owners.

The two structural maps forming PointReadings read the stored samples;
they do not call readAt or evaluate the primitive polynomials again.
-/
def build (parameters : List Rational)
    (inside : ∀ parameter ∈ parameters, 0 ≤ parameter ∧ parameter ≤ 1) :
    SegmentReadings data source oldReadings oldFirst oldLast first_eq last_eq parameters inside :=
  let samples := vectorOfFn fun position : Fin parameters.length =>
    (readAt data source oldReadings oldFirst oldLast first_eq last_eq
      (parameters[position.val]'position.isLt) (inside _ (List.getElem_mem _))).val
  let readings := ofSamples data source parameters samples (fun position =>
    (congrArg (fun value : Reading data => value.1.point) (vectorOfFn_apply _ position)).trans
      (readAt data source oldReadings oldFirst oldLast first_eq last_eq
        (parameters[position.val]'position.isLt) (inside _ (List.getElem_mem _))).property)
  (⟨(data, oldReadings, source, (oldFirst, oldLast), parameters), rfl⟩,
    ⟨⟨samples, rfl⟩, ⟨readings, rfl⟩⟩)

variable {data source oldReadings oldFirst oldLast first_eq last_eq parameters inside}
variable (observed : SegmentReadings data source oldReadings oldFirst oldLast first_eq last_eq parameters inside)

/-- Read the one actual cached original-owner/value vector. -/
abbrev samples : Data.Vector (Reading data) parameters.length := observed.2.1.val

/-- Read the original semantic PointReadings assembled from that SAME sample vector. -/
abbrev readings : PointReadings data.anchors data.offsets (points source parameters) := observed.2.2.val

/-- The original complete input caches and parameter list remain retained unchanged. -/
theorem originals_eq : observed.1.val = (data, oldReadings, source, (oldFirst, oldLast), parameters) :=
  observed.1.property

/-- The actual sample vector retains its whole factory on the SAME old endpoint observations. -/
theorem samples_eq : observed.samples = vectorOfFn (fun position : Fin parameters.length =>
    (readAt data source oldReadings oldFirst oldLast first_eq last_eq
      (parameters[position.val]'position.isLt) (inside _ (List.getElem_mem _))).val) := observed.2.1.property

/-- A selected sample has the literal original source point at that retained parameter position. -/
theorem point_eq (position : Fin parameters.length) :
    (observed.samples position).1.point = points source parameters position :=
  (congrArg (fun values : Data.Vector (Reading data) parameters.length =>
    (values position).1.point) observed.samples_eq).trans
    ((congrArg (fun value : Reading data => value.1.point) (vectorOfFn_apply _ position)).trans
      (readAt data source oldReadings oldFirst oldLast first_eq last_eq
        (parameters[position.val]'position.isLt) (inside _ (List.getElem_mem _))).property)

/-- Read one cached scalar using the actual retained owner, unchanged anchors and original offset. -/
theorem value_eq (position : Fin parameters.length) :
    observed.readings.values position =
      data.anchors.alignedValue data.offsets (observed.samples position).1.column
        (observed.samples position).1.row (observed.samples position).1.point := by
  have selected := congrArg
    (fun value : PointReadings data.anchors data.offsets (points source parameters) => value.values position)
    observed.2.2.property
  exact selected.trans ((map_apply (fun entry : Reading data => entry.2.val) observed.samples position).trans
    (observed.samples position).2.property)

/-- Read the scalar of the SAME stored sample, without evaluating its primitive again. -/
theorem sample_value (position : Fin parameters.length) :
    observed.readings.values position = (observed.samples position).2.val :=
  (congrArg
    (fun value : PointReadings data.anchors data.offsets (points source parameters) => value.values position)
    observed.2.2.property).trans
    (map_apply (fun entry : Reading data => entry.2.val) observed.samples position)

/-- An actual zero-parameter position keeps the literal original lower endpoint scalar. -/
theorem value_at_zero (position : Fin parameters.length)
    (same : parameters[position.val]'position.isLt = 0) :
    observed.readings.values position = oldReadings.values oldFirst := by
  have selected := congrArg
    (fun values : Data.Vector (Reading data) parameters.length => (values position).2.val) observed.samples_eq
  rw [vectorOfFn_apply] at selected
  have endpoint :
      (readAt data source oldReadings oldFirst oldLast first_eq last_eq
        (parameters[position.val]'position.isLt) (inside _ (List.getElem_mem position.isLt))).val.2.val =
        oldReadings.values oldFirst := by
    unfold readAt
    rw [dif_pos same]
  exact (observed.sample_value position).trans (selected.trans endpoint)

/-- An actual one-parameter position keeps the distinct original upper endpoint scalar. -/
theorem value_at_one (position : Fin parameters.length)
    (same : parameters[position.val]'position.isLt = 1) :
    observed.readings.values position = oldReadings.values oldLast := by
  have selected := congrArg
    (fun values : Data.Vector (Reading data) parameters.length => (values position).2.val) observed.samples_eq
  rw [vectorOfFn_apply] at selected
  have different : ¬parameters[position.val]'position.isLt = 0 := by
    intro zero
    exact (of_decide_eq_true rfl : ¬(1 : Rational) = 0) (same.symm.trans zero)
  have endpoint :
      (readAt data source oldReadings oldFirst oldLast first_eq last_eq
        (parameters[position.val]'position.isLt) (inside _ (List.getElem_mem position.isLt))).val.2.val =
        oldReadings.values oldLast := by
    unfold readAt
    rw [dif_neg different, dif_pos same]
  exact (observed.sample_value position).trans (selected.trans endpoint)

end SegmentReadings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives

end
