module
import Purelib.Algebra.Group.Basic
public import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
public import Purelib.Polynomial.Geometry.Grid.Axis.Partial
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.State.WindingOne.Basic
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Automatic axis grouping of each original source segment

The actual source segment determines the coordinate and traversal direction.
Stationary source segments have no moving pieces. No grouping, orientation
choice or endpoint coverage certificate is required from the caller.
-/

section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.Axis
open Purelib.Polynomial.Geometry.Grid.Axis.Partial
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment (RootedWord)
open Purelib.Riemann.Paths.PreparedSegmentSources (SegmentSource)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords (PathSourceWords TourSourceWords)
open Purelib.Approximation.Gaussian.Name.Basic (Named)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid}
  {domains : FaceDomainBank frames
    base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

namespace SegmentAxisGroups

/-- The same complete interval groups, viewed in the actual axis direction. -/
@[expose] def AxisGroups {Alpha : Type} {key : Alpha → Fraction.Rational}
    (span : RootedWords.LiftedFragment axes domains mesh source count target → ClearGrid.Interval key)
    (first last : RootedWords.LiftedFragment axes domains mesh source count target → Fraction.Rational)
    {intervals : List (ClearGrid.Interval key)} {start finish : Fraction.Rational}
    (walk : AxisWalks.Walk intervals start finish) (pieces : List (RootedWords.LiftedFragment axes domains mesh source
      count target)) : Prop :=
  match walk with
  | .forward whole => PartialWalk.Groups span first last intervals whole.edges pieces
  | .backward whole => PartialWalk.Groups span last first intervals whole.edges pieces.reverse

/-- An original stationary segment has no actual moving fragments retaining its source ancestry. -/
private theorem empty_of_stationary_source {pieces : List (RootedWords.LiftedFragment axes domains mesh source count
  target)}
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (stationary : start = finish) : pieces = [] := by
  cases pieces with
  | nil => rfl
  | cons piece pieces =>
      obtain ⟨factor, positive, movement⟩ := SourceDirection.source_displacement piece
        (original piece List.mem_cons_self) (moving piece List.mem_cons_self)
      have vanished : piece.last - piece.first = 0 := by
        rw [stationary, Data.Gaussian.Basic.sub_self, mul_zero] at movement
        exact movement
      exact (moving piece List.mem_cons_self (Algebra.Group.eq_of_sub_eq_zero vanished)).elim

/-- The actual rooted fragments of a horizontal source form complete groups in its retained grid walk and original
traversal direction. -/
private theorem horizontal_axis_groups {pieces : List (RootedWords.LiftedFragment axes domains mesh source count
  target)}
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    {firstName lastName : Gaussian.Name.Basic.Named} (word : LiftedFragment.RootedWord pieces start firstName finish
      lastName)
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (flat : start.im = finish.im)
    (firstOnGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid start) (lastOnGrid :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid finish)
    (whole : AxisWalks.Walk base.bank.grid.xIntervals start.re finish.re) :
    AxisGroups (fun piece =>
      piece.fragment.located.cell.horizontal) (fun piece => piece.first.re) (fun piece => piece.last.re) whole pieces :=
      by
  by_cases stationary : start = finish
  · have empty := empty_of_stationary_source original moving
      stationary
    subst pieces
    cases whole with
    | forward whole =>
        have walk : Partial.PartialWalk (fun piece : RootedWords.LiftedFragment axes domains mesh source count target =>
          piece.fragment.located.cell.horizontal)
            (fun piece => piece.first.re) (fun piece => piece.last.re) base.bank.grid.xIntervals [] start.re finish.re
              := by
          rw [stationary]; exact .nil _
        exact walk.groups_for_walk base.bank.grid.vertical_ordered firstOnGrid.1 lastOnGrid.1 whole
    | backward whole =>
        have walk : Partial.PartialWalk (fun piece : RootedWords.LiftedFragment axes domains mesh source count target =>
          piece.fragment.located.cell.horizontal)
            (fun piece => piece.last.re) (fun piece => piece.first.re) base.bank.grid.xIntervals [] finish.re start.re
              := by
          rw [stationary]; exact .nil _
        exact walk.groups_for_walk base.bank.grid.vertical_ordered lastOnGrid.1 firstOnGrid.1 whole
  · cases whole with
    | forward whole =>
        exact RootedWord.horizontal_groups word original moving
          (lt_of_le_of_ne whole.ordered (fun same => stationary (Data.Gaussian.Basic.ext same flat))) firstOnGrid
            lastOnGrid whole
    | backward whole =>
        exact RootedWord.horizontal_reverse_groups word original moving
          (lt_of_le_of_ne whole.ordered (fun same => stationary (Data.Gaussian.Basic.ext same.symm flat))) firstOnGrid
            lastOnGrid whole

/-- The actual rooted fragments of a vertical source form complete groups in its retained grid walk and original
traversal direction. -/
private theorem vertical_axis_groups {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    {firstName lastName : Gaussian.Name.Basic.Named} (word : LiftedFragment.RootedWord pieces start firstName finish
      lastName)
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (flat : start.re = finish.re)
    (firstOnGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid start) (lastOnGrid :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid finish)
    (whole : AxisWalks.Walk base.bank.grid.yIntervals start.im finish.im) :
    AxisGroups (fun piece =>
      piece.fragment.located.cell.vertical) (fun piece => piece.first.im) (fun piece => piece.last.im) whole pieces :=
      by
  by_cases stationary : start = finish
  · have empty := empty_of_stationary_source original moving
      stationary
    subst pieces
    cases whole with
    | forward whole =>
        have walk : Partial.PartialWalk (fun piece : RootedWords.LiftedFragment axes domains mesh source count target =>
          piece.fragment.located.cell.vertical)
            (fun piece => piece.first.im) (fun piece => piece.last.im) base.bank.grid.yIntervals [] start.im finish.im
              := by
          rw [stationary]; exact .nil _
        exact walk.groups_for_walk base.bank.grid.horizontal_ordered firstOnGrid.2 lastOnGrid.2 whole
    | backward whole =>
        have walk : Partial.PartialWalk (fun piece : RootedWords.LiftedFragment axes domains mesh source count target =>
          piece.fragment.located.cell.vertical)
            (fun piece => piece.last.im) (fun piece => piece.first.im) base.bank.grid.yIntervals [] finish.im start.im
              := by
          rw [stationary]; exact .nil _
        exact walk.groups_for_walk base.bank.grid.horizontal_ordered lastOnGrid.2 firstOnGrid.2 whole
  · cases whole with
    | forward whole =>
        exact RootedWord.vertical_groups word original moving
          (lt_of_le_of_ne whole.ordered (fun same => stationary (Data.Gaussian.Basic.ext flat same))) firstOnGrid
            lastOnGrid whole
    | backward whole =>
        exact RootedWord.vertical_reverse_groups word original moving
          (lt_of_le_of_ne whole.ordered (fun same => stationary (Data.Gaussian.Basic.ext flat same.symm))) firstOnGrid
            lastOnGrid whole

end SegmentAxisGroups

/-- Use the exact finite axis walk selected by the original grid splitter. -/
@[expose] def SegmentAxisGroups {ambient : Rational.Box} :
    {start finish : Data.Gaussian.Basic.Canonical} → (segment : ClearPath.ClearSegment curve.polynomial ambient start
      finish) →
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid start →
        Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid finish →
      List (RootedWords.LiftedFragment axes domains mesh source count target) → Prop
  | _, _, .horizontal xStart xFinish _ _ _ _ _ _, first, last, pieces =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.AxisGroups (fun piece =>
        piece.fragment.located.cell.horizontal) (fun piece => piece.first.re) (fun piece => piece.last.re)
        (AxisWalks.walk base.bank.grid.vertical base.bank.grid.vertical_ordered xStart xFinish first.1 last.1) pieces
  | _, _, .vertical _ yStart yFinish _ _ _ _ _, first, last, pieces =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.AxisGroups (fun piece =>
        piece.fragment.located.cell.vertical) (fun piece => piece.first.im) (fun piece => piece.last.im)
        (AxisWalks.walk base.bank.grid.horizontal base.bank.grid.horizontal_ordered yStart yFinish first.2 last.2)
          pieces

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.RootedWord

/-- The original source segment and grid endpoint certificates supply the complete retained axis grouping of its actual
moving rooted word. -/
theorem segment_axis_groups {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    {firstName lastName : Gaussian.Name.Basic.Named} (word : LiftedFragment.RootedWord pieces start firstName finish
      lastName)
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent) (moving : ∀ piece ∈ pieces,
      piece.last ≠ piece.first)
    (firstOnGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid start) (lastOnGrid :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid finish) :
    SegmentAxisGroups segment firstOnGrid lastOnGrid pieces
      := by
  cases segment with
  | horizontal =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.horizontal_axis_groups word original moving rfl
      firstOnGrid lastOnGrid _
  | vertical =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.vertical_axis_groups word original moving rfl
      firstOnGrid lastOnGrid _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.RootedWord

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups

/-- Original segments retain both their actual root words and the complete axis grouping. Vertex certificates come from
the original path on the grid. -/
inductive AxisPathWords {ambient : Rational.Box} :
    {start finish : Data.Gaussian.Basic.Canonical} → Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish →
      Gaussian.Name.Basic.Named → Gaussian.Name.Basic.Named →
      List (RootedWords.LiftedFragment axes domains mesh source count target) → Prop
  /-- The empty original source path retains the equivalence of its actual endpoint root names. -/ | nil (point :
    Data.Gaussian.Basic.Canonical) {firstName lastName : Gaussian.Name.Basic.Named}
      (root : Nonempty (Gaussian.Equivalence.NamedEquivalent firstName lastName)) :
        AxisPathWords (.nil point) firstName
        lastName []
  /-- Retain one original rooted source segment with its complete axis grouping and the dependent tail sharing its
    middle root owner. -/ | cons {start middle finish : Data.Gaussian.Basic.Canonical} {segment : ClearPath.ClearSegment
    curve.polynomial ambient start middle}
      {tail : Polynomial.Geometry.ClearPath curve.polynomial ambient middle finish} {firstName middleName lastName :
        Gaussian.Name.Basic.Named}
      {block pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
      (word : LiftedFragment.RootedWord block start firstName middle middleName)
      (original : ∀ piece ∈ block, PreparedSegmentSources.SegmentSource segment piece.parent)
      (firstOnGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid start) (lastOnGrid :
        Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid middle)
      (groups : SegmentAxisGroups segment firstOnGrid
        lastOnGrid block)
      (remaining : AxisPathWords tail middleName
        lastName pieces) :
      AxisPathWords (.cons segment tail) firstName
        lastName (block ++ pieces)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.PathSourceWords

/-- All grouping obligations are discharged on the actual source word. -/
theorem group_axes {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} {firstName lastName :
      Gaussian.Name.Basic.Named}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    (words : SourceWords.PathSourceWords path firstName lastName pieces) (moving : ∀ piece ∈ pieces, piece.last ≠
      piece.first)
    (onGrid : Polynomial.Geometry.Grid.FromStates.ContainsPathVertices base.bank.grid path) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.AxisPathWords path firstName lastName pieces := by
  induction words with
  | nil point root => exact .nil point root
  | @cons start middle finish segment tail firstName middleName lastName block pieces word original remaining ih =>
      have firstOnGrid := onGrid.1
      have lastOnGrid := Polynomial.Geometry.Grid.FromStates.ContainsPathVertices.start base.bank.grid tail onGrid.2
      exact .cons word original firstOnGrid lastOnGrid
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.RootedWord.segment_axis_groups word original (fun
          piece member => moving piece (List.mem_append_left _ member)) firstOnGrid lastOnGrid)
        (ih (fun piece member => moving piece (List.mem_append_right _ member)) onGrid.2)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.PathSourceWords

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups

/-- Complete axis grouping of all four actual source legs, retaining the original root handoffs between the connector
and both branch boundaries. -/
inductive AxisTourWords (tour : PreparedBoundaryClosure.ClosedBoundaryDoublePath curve) (firstName lastName :
  Gaussian.Name.Basic.Named) :
    List (RootedWords.LiftedFragment axes domains mesh source count target) → Prop
  /-- Combine the four actual source-leg groupings with their retained connector and branch-boundary root handoffs. -/ |
    mk {forward right backward left : List (RootedWords.LiftedFragment axes domains mesh source count target)}
      {afterForward afterRight afterBackward : Gaussian.Name.Basic.Named}
      (forwardWords : AxisPathWords
        tour.joined.data.connector firstName afterForward forward)
      (rightWords : AxisPathWords
        tour.joined.data.rightBoundaryPath afterForward afterRight right)
      (backwardWords : AxisPathWords (ClearPath.reverse
        tour.joined.data.connector) afterRight afterBackward backward)
      (leftWords : AxisPathWords
        tour.joined.data.leftBoundaryPath afterBackward lastName left) :
      AxisTourWords tour firstName lastName
        (((forward ++ right) ++ backward) ++ left)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.TourSourceWords

/-- Construct all complete interval groups from the actual retained source words and the original tour's grid-vertex
certificate. -/
theorem group_axes {tour : PreparedBoundaryClosure.ClosedBoundaryDoublePath curve}
    {firstName lastName : Gaussian.Name.Basic.Named} {pieces : List (RootedWords.LiftedFragment axes domains mesh source
      count target)}
    (words : SourceWords.TourSourceWords tour firstName lastName pieces)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first)
    (onGrid : Grid.ContainsTourVertices base.bank.grid tour) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.AxisTourWords tour firstName lastName pieces := by
  cases words with
  | mk forward right backward left =>
      exact .mk
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.PathSourceWords.group_axes forward (fun piece
          member => moving piece
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))) onGrid.1)
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.PathSourceWords.group_axes right (fun piece member
          => moving piece
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member)))) onGrid.2.1)
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.PathSourceWords.group_axes backward (fun piece
          member => moving piece
          (List.mem_append_left _ (List.mem_append_right _ member))) onGrid.2.2.1)
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.PathSourceWords.group_axes left (fun piece member
          => moving piece (List.mem_append_right _ member)) onGrid.2.2.2)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups.TourSourceWords

end
