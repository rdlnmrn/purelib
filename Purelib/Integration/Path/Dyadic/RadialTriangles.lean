module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Gaussian.Corners

import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Topology.PreparedSurfacePartitions
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

public section

/-!
# Shared finite parameter partitions for reciprocal radial caps

The cached unit-square partition supplies the indexed incidence and parameter
containment certificates used by the actual inverse-arc radial map. The
geometry and energy consumers share this one executable partition.
-/

namespace Purelib.Integration.Path.Dyadic.RadialTriangles

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Geometry.Rational (Box)

/-- The exact closed rational unit square. -/
@[expose] def unitBox : Box := ⟨0, 1, 0, 1, by decide, by decide⟩

/-- Both coordinate widths of the exact unit square are strictly positive. -/
theorem unitBox_proper : unitBox.Proper := ⟨by decide, by decide⟩

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
/-- All vertices of triangles from the retained refining boxes lie in the original unit square.

The supplied membership-indexed refinement certificates preserve each exact source box and the original triangulation
order. -/
theorem triangles_inside (boxes : List Box) (within : ∀ box ∈ boxes, box.Refines
  Dyadic.RadialTriangles.unitBox) :
    ∀ source ∈ PreparedBoxTriangulation.boxTriangles boxes,
      Dyadic.RadialTriangles.unitBox.Contains source.first ∧ Dyadic.RadialTriangles.unitBox.Contains source.second ∧
        Dyadic.RadialTriangles.unitBox.Contains source.third := by
  induction boxes with
  | nil => intro source member; exact (List.not_mem_nil member).elim
  | cons box boxes ih =>
      intro source member
      have first : box.Contains (Box.Gaussian.Corners.lowerLeft box) := ⟨le_rfl, box.x_valid, le_rfl, box.y_valid⟩
      have second : box.Contains (Box.Gaussian.Corners.lowerRight box) := ⟨box.x_valid, le_rfl, le_rfl, box.y_valid⟩
      have third : box.Contains (Box.Gaussian.Corners.upperRight box) := ⟨box.x_valid, le_rfl, box.y_valid, le_rfl⟩
      have fourth : box.Contains (Box.Gaussian.Corners.upperLeft box) := ⟨le_rfl, box.x_valid, box.y_valid, le_rfl⟩
      have included {point : Basic.Canonical} (inside : box.Contains point) : Dyadic.RadialTriangles.unitBox.Contains
        point :=
        (within box List.mem_cons_self).contains inside
      rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
      · exact ⟨included first, included second, included third⟩
      · rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
        · exact ⟨included first, included third, included fourth⟩
        · exact ih (fun other member => within other (List.mem_cons_of_mem box member)) source member

set_option genInjectivity false in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
/-- A retained depth-indexed triangulated partition whose original parent is exactly the unit square.

The retained mesh carries its exact refinement depth and ordered triangle
incidence. Its parent equality identifies the original rational unit square. -/
structure Parameters (depth : Nat) where
  /-- The retained triangulated partition at the original depth. -/ mesh :
    PreparedBoxTriangulation.TriangulatedPartition depth
  /-- The retained mesh partition's parent is exactly the unit square. -/ parent_eq : mesh.partition.parent =
    Dyadic.RadialTriangles.unitBox

constructive_injectivity Parameters

namespace Parameters

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
open Purelib.Riemann.Topology in
/-- Build the original unit-square box partition and retain its depth-indexed triangulation. -/
@[expose] def build (depth : Nat) : Dyadic.RadialTriangles.Parameters depth :=
  ⟨PreparedBoxTriangulation.TriangulatedPartition.build (PreparedSurfacePartitions.BoxPartition.build
    Dyadic.RadialTriangles.unitBox depth), rfl⟩

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
/-- Every retained leaf box refines the exact original unit square. -/
theorem leaves_inside {depth : Nat} (parameters : Dyadic.RadialTriangles.Parameters depth) :
    ∀ box ∈ parameters.mesh.partition.leaves, box.Refines unitBox := by
  intro box member
  rw [parameters.mesh.partition.leaves_eq] at member
  rw [← parameters.parent_eq]
  exact PreparedBoxPartitions.cells_refine depth parameters.mesh.partition.parent member

end Parameters

end Purelib.Integration.Path.Dyadic.RadialTriangles
