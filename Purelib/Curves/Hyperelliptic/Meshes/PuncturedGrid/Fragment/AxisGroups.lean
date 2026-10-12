module
import Purelib.Data.List.Reverse
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
public import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Polynomial.Geometry.Grid.Axis.Partial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.StationaryWords
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

public section

/-!
# Complete axis groups of actual moving fragment words

The original segment supplies strict movement in the selected coordinate.
The cached located cells supply the adjacent intervals and endpoint bounds.
Coarsening therefore applies to the actual piece and root word, without an
independently selected subdivision or a caller-provided grouping.
-/

section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.Axis
open Purelib.Polynomial.Geometry.Grid.Axis.Partial
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Riemann.Paths

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment (RootedWord)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval Cell HorizontalLine VerticalLine)
open Purelib.Riemann.Paths.PreparedSegmentSources (SegmentSource)
open Purelib.Approximation.Gaussian.Name.Basic (Named)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {axes :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    base.faces.regulars} {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Purelib.Data.Rat.Fraction.Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups

/-- Every moving retained fragment inherits strict projected movement from its actual original source segment. -/
private theorem projected_movement (coordinate : Data.Gaussian.Basic.Canonical → Fraction.Rational)
    (difference : ∀ a b, coordinate (a - b) = coordinate a - coordinate b)
    (scale : ∀ factor point, coordinate ((⟨factor, 0⟩ : Data.Gaussian.Basic.Canonical) * point) = factor * coordinate
      point)
    (piece : RootedWords.LiftedFragment axes domains mesh source count target)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : PreparedSegmentSources.SegmentSource segment piece.parent) (moving : piece.last ≠ piece.first)
    (forward : coordinate start < coordinate finish) : coordinate piece.first < coordinate piece.last := by
  obtain ⟨factor, positive, displacement⟩ := SourceDirection.source_displacement piece original moving
  have equal := congrArg coordinate displacement
  rw [difference, scale, difference] at equal
  have positiveDifference : 0 < coordinate piece.last - coordinate piece.first := equal.trans_gt
    (Fraction.Order.Arithmetic.mul_pos_direct positive (Fraction.Order.Arithmetic.sub_pos_direct forward))
  have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct positiveDifference (coordinate piece.first)
  have finishEq : coordinate piece.first + (coordinate piece.last - coordinate piece.first) = coordinate piece.last :=
    by ring1
  simpa only [add_zero, finishEq, -eq_self, -iff_self] using shifted

/-- Real-coordinate projection commutes with multiplication by a rational real scalar. -/
private theorem coordinate_re_scale (factor : Fraction.Rational) (point : Data.Gaussian.Basic.Canonical) :
    ((⟨factor, 0⟩ : Data.Gaussian.Basic.Canonical) * point).re = factor * point.re := by
  change factor * point.re - 0 * point.im = _
  ring1

/-- Imaginary-coordinate projection commutes with multiplication by a rational real scalar. -/
private theorem coordinate_im_scale (factor : Fraction.Rational) (point : Data.Gaussian.Basic.Canonical) :
    ((⟨factor, 0⟩ : Data.Gaussian.Basic.Canonical) * point).im = factor * point.im := by
  change factor * point.im + 0 * point.re = _
  ring1

/-- The retained located cell's horizontal and vertical intervals belong to the original grid interval lists. -/
private theorem cell_intervals (piece : RootedWords.LiftedFragment axes domains mesh source count target) :
    piece.fragment.located.cell.horizontal ∈ base.bank.grid.xIntervals ∧
      piece.fragment.located.cell.vertical ∈ base.bank.grid.yIntervals := by
  obtain ⟨horizontal, member, row⟩ := Flatten.mem_flatMap.mp piece.fragment.located.cell_member
  obtain ⟨vertical, present, equal⟩ := Map.mem_map.mp row
  exact ⟨(congrArg ClearGrid.Cell.horizontal equal) ▸ member, (congrArg ClearGrid.Cell.vertical equal) ▸ present⟩

/-- The actual moving rooted fragment word forms a partial increasing walk in its retained projected cell intervals. -/
private theorem projected_walk {Alpha : Type} {key : Alpha → Fraction.Rational}
    (coordinate : Data.Gaussian.Basic.Canonical → Fraction.Rational)
    (difference : ∀ a b, coordinate (a - b) = coordinate a - coordinate b)
    (scale : ∀ factor point, coordinate ((⟨factor, 0⟩ : Data.Gaussian.Basic.Canonical) * point) = factor * coordinate
      point)
    (span : RootedWords.LiftedFragment axes domains mesh source count target → ClearGrid.Interval key) (intervals : List
      (ClearGrid.Interval key))
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (forward : coordinate start < coordinate finish)
    (located : ∀ piece ∈ pieces, span piece ∈ intervals ∧
      key (span piece).lower ≤ coordinate piece.first ∧ coordinate piece.last ≤ key (span piece).upper) :
    Partial.PartialWalk span (fun piece => coordinate piece.first) (fun piece => coordinate piece.last)
      intervals pieces (coordinate first) (coordinate last) := by
  induction word with
  | nil equal root => cases equal; exact .nil _
  | cons piece equal root tail ih =>
      rw [equal]
      exact .cons piece (located piece List.mem_cons_self).1
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.projected_movement coordinate difference scale
          piece (original piece List.mem_cons_self)
          (moving piece List.mem_cons_self) forward)
        (located piece List.mem_cons_self).2
        (ih (fun child member => original child (List.mem_cons_of_mem _ member))
          (fun child member => moving child (List.mem_cons_of_mem _ member))
          (fun child member => located child (List.mem_cons_of_mem _ member)))

/-- Reversing the actual moving fragment order forms an increasing projected walk for a decreasing original source. -/
private theorem projected_reverse_walk {Alpha : Type} {key : Alpha → Fraction.Rational}
    (coordinate : Data.Gaussian.Basic.Canonical → Fraction.Rational)
    (difference : ∀ a b, coordinate (a - b) = coordinate a - coordinate b)
    (scale : ∀ factor point, coordinate ((⟨factor, 0⟩ : Data.Gaussian.Basic.Canonical) * point) = factor * coordinate
      point)
    (span : RootedWords.LiftedFragment axes domains mesh source count target → ClearGrid.Interval key) (intervals : List
      (ClearGrid.Interval key))
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (backward : coordinate finish < coordinate start)
    (located : ∀ piece ∈ pieces, span piece ∈ intervals ∧
      key (span piece).lower ≤ coordinate piece.last ∧ coordinate piece.first ≤ key (span piece).upper) :
    Partial.PartialWalk span (fun piece => coordinate piece.last) (fun piece => coordinate piece.first)
      intervals pieces.reverse (coordinate last) (coordinate first) := by
  induction word with
  | nil equal root => cases equal; exact .nil _
  | cons piece equal root tail ih =>
      have negative := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.projected_movement (fun point =>
        -coordinate point)
        (by intro a b; rw [difference]; ring1) (by intro factor point; rw [scale]; ring1)
        piece (original piece List.mem_cons_self) (moving piece List.mem_cons_self)
        (Fraction.Order.Arithmetic.neg_lt_neg_direct backward)
      have reversed : coordinate piece.last < coordinate piece.first := by
        simpa only [neg_neg, -eq_self, -iff_self] using Fraction.Order.Arithmetic.neg_lt_neg_direct negative
      have head : Partial.PartialWalk span (fun piece => coordinate piece.last) (fun piece => coordinate piece.first)
          intervals [piece] (coordinate piece.last) (coordinate piece.first) :=
        .cons piece (located piece List.mem_cons_self).1 reversed (located piece List.mem_cons_self).2 (.nil _)
      rw [Reverse.reverse_cons, equal]
      exact (ih (fun child member => original child (List.mem_cons_of_mem _ member))
        (fun child member => moving child (List.mem_cons_of_mem _ member))
        (fun child member => located child (List.mem_cons_of_mem _ member))).append head

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.RootedWord

/-- Actual moving fragments of a source with increasing real coordinate form a partial walk through the retained
horizontal cell intervals. -/
theorem horizontal_partial {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (forward : start.re < finish.re) :
    Partial.PartialWalk (fun piece => piece.fragment.located.cell.horizontal)
      (fun piece => piece.first.re) (fun piece => piece.last.re) base.bank.grid.xIntervals pieces first.re last.re :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.projected_walk Data.Gaussian.Basic.re (fun _ _ => rfl)
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.coordinate_re_scale _ _ word original moving forward
    (fun piece _ => ⟨(Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.cell_intervals piece).1,
      piece.fragment.located.first_inside.1, piece.fragment.located.last_inside.2.1⟩)

/-- The same construction uses the imaginary coordinate on vertical legs. -/
theorem vertical_partial {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (forward : start.im < finish.im) :
    Partial.PartialWalk (fun piece => piece.fragment.located.cell.vertical)
      (fun piece => piece.first.im) (fun piece => piece.last.im) base.bank.grid.yIntervals pieces first.im last.im :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.projected_walk Data.Gaussian.Basic.im (fun _ _ => rfl)
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.coordinate_im_scale _ _ word original moving forward
    (fun piece _ => ⟨(Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.cell_intervals piece).2,
      piece.fragment.located.first_inside.2.2.1, piece.fragment.located.last_inside.2.2.2⟩)

/-- The grouping matches any actual complete horizontal axis walk with these endpoints, including the walk retained by
the original grid split. -/
theorem horizontal_groups {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (forward : start.re < finish.re)
    (firstOnGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid first) (lastOnGrid :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid last)
    (whole : AxisWalks.IncreasingWalk base.bank.grid.xIntervals first.re last.re) :
    PartialWalk.Groups (fun piece => piece.fragment.located.cell.horizontal)
      (fun piece => piece.first.re) (fun piece => piece.last.re) base.bank.grid.xIntervals whole.edges pieces :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.RootedWord.horizontal_partial word original moving
    forward).groups_for_walk base.bank.grid.vertical_ordered firstOnGrid.1 lastOnGrid.1 whole

/-- The actual vertically increasing fragment word groups along the supplied original complete vertical axis walk. -/
theorem vertical_groups {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (forward : start.im < finish.im)
    (firstOnGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid first) (lastOnGrid :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid last)
    (whole : AxisWalks.IncreasingWalk base.bank.grid.yIntervals first.im last.im) :
    PartialWalk.Groups (fun piece => piece.fragment.located.cell.vertical)
      (fun piece => piece.first.im) (fun piece => piece.last.im) base.bank.grid.yIntervals whole.edges pieces :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.RootedWord.vertical_partial word original moving
    forward).groups_for_walk base.bank.grid.horizontal_ordered firstOnGrid.2 lastOnGrid.2 whole

/-- Decreasing horizontal traversal keeps the actual pieces in reverse coordinate order for coarsening; no root owner or
fragment is replaced. -/
theorem horizontal_reverse_partial {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (backward : finish.re < start.re) :
    Partial.PartialWalk (fun piece => piece.fragment.located.cell.horizontal)
      (fun piece => piece.last.re) (fun piece => piece.first.re) base.bank.grid.xIntervals pieces.reverse last.re
        first.re :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.projected_reverse_walk Data.Gaussian.Basic.re (fun _ _
    => rfl) Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.coordinate_re_scale _ _ word original moving
    backward
    (fun piece _ => ⟨(Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.cell_intervals piece).1,
      piece.fragment.located.last_inside.1, piece.fragment.located.first_inside.2.1⟩)

/-- The reversed actual horizontally decreasing fragment word groups along the supplied original increasing axis walk.
-/
theorem horizontal_reverse_groups {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (backward : finish.re < start.re)
    (firstOnGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid first) (lastOnGrid :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid last)
    (whole : AxisWalks.IncreasingWalk base.bank.grid.xIntervals last.re first.re) :
    PartialWalk.Groups (fun piece => piece.fragment.located.cell.horizontal)
      (fun piece => piece.last.re) (fun piece => piece.first.re) base.bank.grid.xIntervals whole.edges pieces.reverse :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.RootedWord.horizontal_reverse_partial word original
    moving backward).groups_for_walk base.bank.grid.vertical_ordered lastOnGrid.1 firstOnGrid.1 whole

/-- Decreasing vertical traversal keeps the actual pieces in reverse coordinate order for coarsening; no root owner or
fragment is replaced. -/
theorem vertical_reverse_partial {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (backward : finish.im < start.im) :
    Partial.PartialWalk (fun piece => piece.fragment.located.cell.vertical)
      (fun piece => piece.last.im) (fun piece => piece.first.im) base.bank.grid.yIntervals pieces.reverse last.im
        first.im :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.projected_reverse_walk Data.Gaussian.Basic.im (fun _ _
    => rfl) Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.coordinate_im_scale _ _ word original moving
    backward
    (fun piece _ => ⟨(Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.cell_intervals piece).2,
      piece.fragment.located.last_inside.2.2.1, piece.fragment.located.first_inside.2.2.2⟩)

/-- The reversed actual vertically decreasing fragment word groups along the supplied original increasing axis walk. -/
theorem vertical_reverse_groups {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces first firstName last lastName)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first) (backward : finish.im < start.im)
    (firstOnGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid first) (lastOnGrid :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid last)
    (whole : AxisWalks.IncreasingWalk base.bank.grid.yIntervals last.im first.im) :
    PartialWalk.Groups (fun piece => piece.fragment.located.cell.vertical)
      (fun piece => piece.last.im) (fun piece => piece.first.im) base.bank.grid.yIntervals whole.edges pieces.reverse :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.RootedWord.vertical_reverse_partial word original
    moving backward).groups_for_walk base.bank.grid.horizontal_ordered lastOnGrid.2 firstOnGrid.2 whole

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisGroups.RootedWord

end
