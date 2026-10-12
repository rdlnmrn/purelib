module
import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Riemann.RootContinuation.NewtonObservationPartitions
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Readings.ProtectedObservationRegion
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.ContainedObservationEnergy
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rational.Box.Separation

open Purelib

public section

/-!
# Complete regular-face partitions at protected observation boundaries

The cuts cover each whole regular face, including the complement of the
observation rectangles. Every piece has a certified placement relative to
every observation. Coverage, disjoint interiors and exact total area are
retained in the rectangular partition, rather than inferred from the area
of the observation subregions.
-/

namespace Purelib.Riemann.Topology.NewtonObservationSurfacePartition

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational}

section
open Purelib.Geometry.Rectangle.Partition
/-- The ordered lower-left and upper-right corners of the original protected observation boxes. -/
@[expose] def surfaceCutPoints (observations : ProtectedObservations original) : List Gaussian :=
  (List.ofFn fun site => PreparedRectangleCuts.corner (observations.energy.box site) false false) ++
    (List.ofFn fun site => PreparedRectangleCuts.corner (observations.energy.box site) true true)

/-- Every original observation box's lower corner belongs to the retained surface cut-point list. -/
private theorem lower_mem (observations : ProtectedObservations original) (site : Fin genus) :
    PreparedRectangleCuts.corner (observations.energy.box site) false false ∈ (surfaceCutPoints observations) :=
  List.mem_append_left _ (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨site, rfl⟩)

/-- Every original observation box's upper corner belongs to the retained surface cut-point list. -/
private theorem upper_mem (observations : ProtectedObservations original) (site : Fin genus) :
    PreparedRectangleCuts.corner (observations.energy.box site) true true ∈ (surfaceCutPoints observations) :=
  List.mem_append_right _ (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨site, rfl⟩)

end

section
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle.Partition
/-- A retained vertical cut lies outside the interior of every original partition piece. -/
private theorem x_outside {box small : Box} {points : List Basic.Canonical}
    (cuts : Geometry.Rectangle.CutPartition box points) (member : small ∈ cuts.boxes)
    {point : Basic.Canonical} (present : point ∈ points) :
    point.re ≤ small.xLower ∨ small.xUpper ≤ point.re := by
  rw [cuts.boxes_eq] at member
  obtain ⟨x, xMember, rowMember⟩ := Flatten.mem_flatMap.mp member
  obtain ⟨y, _, rfl⟩ := Map.mem_map.mp rowMember
  exact cuts.x.cut_outside xMember (Map.mem_map.mpr ⟨point, present, rfl⟩)

/-- A retained horizontal cut lies outside the interior of every original partition piece. -/
private theorem y_outside {box small : Box} {points : List Basic.Canonical}
    (cuts : Geometry.Rectangle.CutPartition box points) (member : small ∈ cuts.boxes)
    {point : Basic.Canonical} (present : point ∈ points) :
    point.im ≤ small.yLower ∨ small.yUpper ≤ point.im := by
  rw [cuts.boxes_eq] at member
  obtain ⟨x, _, rowMember⟩ := Flatten.mem_flatMap.mp member
  obtain ⟨y, yMember, rfl⟩ := Map.mem_map.mp rowMember
  exact cuts.y.cut_outside yMember (Map.mem_map.mpr ⟨point, present, rfl⟩)

end

open Purelib.Geometry.Rational in
set_option genInjectivity false in
/-- A certified containment or interior separation of an original piece and observation box.

Both alternatives retain the exact input boxes and their geometric relation; classification does not replace either
owner. -/
inductive Placement (piece observation : Box) where
  /-- The original piece refines the exact retained observation box. -/ | inside : piece.Refines observation → Placement
    piece observation
  /-- The original piece and retained observation box have separated interiors. -/ | outside : piece.InteriorSeparated
    observation → Placement piece observation

constructive_injectivity Placement

section
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle.Partition
/-- Every original surface piece either refines the observation box or has separated interior.

The retained partition cuts include both original observation corners. Its piece
intervals therefore give one of these two certified relations to that same box. -/
theorem placement_exists (observations : ProtectedObservations original) {box small : Box}
    (cuts : Geometry.Rectangle.CutPartition box (surfaceCutPoints observations))
    (member : small ∈ cuts.boxes) (site : Fin genus) :
    small.Refines (observations.energy.box site) ∨ small.InteriorSeparated (observations.energy.box site) := by
  have xl := x_outside cuts member ((lower_mem observations) site)
  have xu := x_outside cuts member ((upper_mem observations) site)
  have yl := y_outside cuts member ((lower_mem observations) site)
  have yu := y_outside cuts member ((upper_mem observations) site)
  rcases xl with xl | xl
  · rcases xu with xu | xu
    · exact Or.inr (Or.inr (Or.inl xu))
    · rcases yl with yl | yl
      · rcases yu with yu | yu
        · exact Or.inr (Or.inr (Or.inr (Or.inr yu)))
        · exact Or.inl ⟨xl, xu, yl, yu⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl yl)))
  · exact Or.inr (Or.inl xl)

/-- Decide containment and retain its original containment or separation certificate.

The existing componentwise rectangle decision selects the same inside/outside
constructor and keeps the selected observation box and partition piece. -/
@[expose] def placement (observations : ProtectedObservations original) {box small : Box}
    (cuts : Geometry.Rectangle.CutPartition box (surfaceCutPoints observations))
    (member : small ∈ cuts.boxes) (site : Fin genus) : Placement small (observations.energy.box site) := by
  letI : Decidable (small.Refines (observations.energy.box site)) :=
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
  exact if inside : small.Refines (observations.energy.box site) then .inside inside
    else .outside (((placement_exists observations) cuts member site).resolve_left inside)

end

open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
set_option genInjectivity false in
/-- An original regular-face partition with cached placement against every observation site.

The cuts use the exact protected-box corners, and the dependent placement bank keeps every original bounded piece and
site index. -/
structure SurfacePartition (observations : ProtectedObservations original)
    (grid : NewtonGrid preparation target radius) (position : Fin grid.faces.regulars.length) where
  /-- The exact regular-face partition at the original protected observation corner list. -/ cuts :
    Geometry.Rectangle.CutPartition (grid.faces.regulars[position.val]'position.isLt).cell.box
    (surfaceCutPoints observations)
  /-- The retained piece-by-site bank of exact containment or interior-separation certificates. -/ placements :
    Vector.DependentVector (fun piece : Fin cuts.boxes.length =>
    Vector.DependentVector (fun site : Fin genus =>
      Placement (cuts.boxes[piece.val]'piece.isLt) (observations.energy.box site)))

constructive_injectivity SurfacePartition

namespace SurfacePartition

open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
/-- Partition one original regular face at all protected observation corners and cache its exact placements. -/
@[expose] def build (observations : ProtectedObservations original) (grid : NewtonGrid preparation target radius)
    (position : Fin grid.faces.regulars.length) : SurfacePartition observations grid position :=
  let face := grid.faces.regulars[position.val]'position.isLt
  let cuts := Geometry.Rectangle.CutPartition.build face.cell.box face.cell.box_proper (surfaceCutPoints observations)
  ⟨cuts, Vector.DependentVector.ofFn fun piece => Vector.DependentVector.ofFn fun site =>
    (placement observations) cuts (List.getElem_mem piece.isLt) site⟩

end SurfacePartition

open Purelib.Data in
/-- Cache the dependent surface partitions at every original regular-face position. -/
@[expose] def surfacePartitions (observations : ProtectedObservations original) (grid : NewtonGrid preparation target
  radius) :
    Vector.DependentVector (fun position : Fin grid.faces.regulars.length => SurfacePartition observations grid
      position) :=
  Vector.DependentVector.ofFn (SurfacePartition.build observations grid)

end Purelib.Riemann.Topology.NewtonObservationSurfacePartition
