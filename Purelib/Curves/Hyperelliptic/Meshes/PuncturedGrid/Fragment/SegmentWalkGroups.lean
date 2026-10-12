module
import Purelib.Data.List.Reverse
import Purelib.Data.List.Append
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisWalkGroups
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.State.WindingOne.Basic
meta import Mathlib.Tactic.Linter.Lint
public import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence

public section

/-! Construct grouped actual grid walks for original source segments and
paths, using the same axis lookup and endpoint casts as the standard splitter. -/

section

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Polynomial.Geometry.Grid.Walks

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (HorizontalLine VerticalLine)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment (RootedWord)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (walk lookup)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk splitSegment splitPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups (AxisGroups)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment (WalkGroups)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups
  (horizontal_increasing vertical_increasing horizontal_decreasing vertical_decreasing)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords (PathSourceWords TourSourceWords)
open _root_.Purelib.Polynomial.Geometry.Grid.FromStates (ContainsPathVertices)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.Grid (ContainsTourVertices)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Riemann.Paths.PreparedSegmentSources (SegmentSource)

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

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups

open Purelib.Polynomial.Geometry.Grid.AxisWalks in
/-- Transport a grouped walk along endpoint equalities while preserving its root names and fragment list. -/
theorem castEndpoints {first last a b : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk base.bank.grid first last}
    {firstName lastName : Gaussian.Name.Basic.Named} {pieces : List (RootedWords.LiftedFragment axes domains mesh source
      count target)}
    (groups : WalkGroups walk firstName lastName pieces) (firstEq : first = a) (lastEq : last = b) :
    WalkGroups (walk.castEndpoints firstEq lastEq) firstName lastName pieces := by
  cases firstEq
  cases lastEq
  exact groups

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups

variable {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Purelib.Data.Gaussian.Basic.Canonical} {segment : ClearSegment curve.polynomial
  ambient start finish}

/-- Group the retained rooted source fragments along their actual horizontal axis walk in either orientation. -/
theorem horizontal_axis
    (line : ClearGrid.HorizontalLine curve.polynomial (Cuts.Ambient curve)) (onLine : line ∈ base.bank.grid.horizontal)
    {a b : Fraction.Rational} (axis : AxisWalks.Walk base.bank.grid.xIntervals a b)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} {firstName lastName :
      Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces (Components.Basic.point a line.coordinate) firstName
      (Components.Basic.point b line.coordinate) lastName)
    (original : ∀ piece ∈ pieces, SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first)
    (flat : start.im = finish.im) (lineEq : start.im = line.coordinate)
    (groups : SegmentAxisGroups.AxisGroups (fun piece => piece.fragment.located.cell.horizontal)
      (fun piece => piece.first.re) (fun piece => piece.last.re) axis pieces) :
    WalkGroups (Walk.horizontalAxis line onLine axis) firstName lastName pieces := by
  cases axis with
  | forward axis => exact WalkGroups.horizontal_increasing line onLine axis word original moving flat lineEq groups
  | backward axis =>
      have reverseWord : LiftedFragment.RootedWord pieces.reverse.reverse (Components.Basic.point a line.coordinate)
        firstName (Components.Basic.point b line.coordinate) lastName := by
        simpa only [Reverse.reverse_reverse, -eq_self, -iff_self] using word
      have result := WalkGroups.horizontal_decreasing line onLine axis reverseWord
        (fun piece member => original piece ((Reverse.mem_reverse _).mp member))
        (fun piece member => moving piece ((Reverse.mem_reverse _).mp member)) flat lineEq groups
      simpa only [Reverse.reverse_reverse, Walk.horizontalAxis, Walk.verticalAxis, -eq_self, -iff_self] using result

/-- Group the retained rooted source fragments along their actual vertical axis walk in either orientation. -/
theorem vertical_axis
    (line : ClearGrid.VerticalLine curve.polynomial (Cuts.Ambient curve)) (onLine : line ∈ base.bank.grid.vertical)
    {a b : Fraction.Rational} (axis : AxisWalks.Walk base.bank.grid.yIntervals a b)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} {firstName lastName :
      Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces (Components.Basic.point line.coordinate a) firstName
      (Components.Basic.point line.coordinate b) lastName)
    (original : ∀ piece ∈ pieces, SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first)
    (flat : start.re = finish.re) (lineEq : start.re = line.coordinate)
    (groups : SegmentAxisGroups.AxisGroups (fun piece => piece.fragment.located.cell.vertical)
      (fun piece => piece.first.im) (fun piece => piece.last.im) axis pieces) :
    WalkGroups (Walk.verticalAxis line onLine axis) firstName lastName pieces := by
  cases axis with
  | forward axis => exact WalkGroups.vertical_increasing line onLine axis word original moving flat lineEq groups
  | backward axis =>
      have reverseWord : LiftedFragment.RootedWord pieces.reverse.reverse (Components.Basic.point line.coordinate a)
        firstName (Components.Basic.point line.coordinate b) lastName := by
        simpa only [Reverse.reverse_reverse, -eq_self, -iff_self] using word
      have result := WalkGroups.vertical_decreasing line onLine axis reverseWord
        (fun piece member => original piece ((Reverse.mem_reverse _).mp member))
        (fun piece member => moving piece ((Reverse.mem_reverse _).mp member)) flat lineEq groups
      simpa only [Reverse.reverse_reverse, Walk.horizontalAxis, Walk.verticalAxis, -eq_self, -iff_self] using result

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.RootedWord

open Purelib.Polynomial.Geometry.Grid.AxisWalks in
/-- The original source and root word automatically group along the exact walk returned by the existing grid segment
splitter. -/
theorem segment_walk_groups
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} {firstName lastName :
      Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces start firstName finish lastName)
    (original : ∀ piece ∈ pieces, SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first)
    (firstOnGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid start) (lastOnGrid :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid finish) :
    WalkGroups (Walks.splitSegment base.bank.grid segment firstOnGrid lastOnGrid) firstName lastName pieces
      := by
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper clearance =>
      let line := AxisWalks.lookup y base.bank.grid.horizontal firstOnGrid.2
      let axis := walk base.bank.grid.vertical base.bank.grid.vertical_ordered xStart xFinish firstOnGrid.1 lastOnGrid.1
      have firstEq : Components.Basic.point xStart line.entry.coordinate = Components.Basic.point xStart y := congrArg
        (Components.Basic.point xStart) line.coordinate_eq
      have lastEq : Components.Basic.point xFinish line.entry.coordinate = Components.Basic.point xFinish y := congrArg
        (Components.Basic.point xFinish) line.coordinate_eq
      have adjusted := (word.changeStart firstEq ⟨NamedEquivalent.refl _⟩).castFinish lastEq.symm
      have grouped := RootedWord.segment_axis_groups word original moving firstOnGrid lastOnGrid
      exact (WalkGroups.horizontal_axis line.entry
        line.member axis adjusted original moving rfl line.coordinate_eq.symm grouped).castEndpoints firstEq lastEq
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper clearance =>
      let line := AxisWalks.lookup x base.bank.grid.vertical firstOnGrid.1
      let axis := walk base.bank.grid.horizontal base.bank.grid.horizontal_ordered yStart yFinish firstOnGrid.2
        lastOnGrid.2
      have firstEq : Components.Basic.point line.entry.coordinate yStart = Components.Basic.point x yStart := congrArg
        (fun value => Components.Basic.point value yStart) line.coordinate_eq
      have lastEq : Components.Basic.point line.entry.coordinate yFinish = Components.Basic.point x yFinish := congrArg
        (fun value => Components.Basic.point value yFinish) line.coordinate_eq
      have adjusted := (word.changeStart firstEq ⟨NamedEquivalent.refl _⟩).castFinish lastEq.symm
      have grouped := RootedWord.segment_axis_groups word original moving firstOnGrid lastOnGrid
      exact (WalkGroups.vertical_axis line.entry
        line.member axis adjusted original moving rfl line.coordinate_eq.symm grouped).castEndpoints firstEq lastEq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.RootedWord

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.PathSourceWords

/-- Fold all original segment groups with their actual root handoffs. -/
theorem walk_groups {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} {firstName lastName :
      Gaussian.Name.Basic.Named}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    (words : SourceWords.PathSourceWords path firstName lastName pieces)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first)
    (onGrid : Polynomial.Geometry.Grid.FromStates.ContainsPathVertices base.bank.grid path) :
    WalkGroups (Walks.splitPath base.bank.grid path onGrid) firstName lastName pieces := by
  induction words with
  | nil point root => exact .nil root
  | cons word original remaining ih =>
      exact (word.segment_walk_groups original (fun piece member => moving piece (List.mem_append_left _ member))
        onGrid.1 (ContainsPathVertices.start _ _ onGrid.2)).append
          (ih (fun piece member => moving piece (List.mem_append_right _ member)) onGrid.2)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.PathSourceWords

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.TourSourceWords

/-- All four source legs assemble in the exact standard-tour walk, while retaining their actual intermediate root names
and original piece order. -/
theorem walk_groups {tour : ClosedBoundaryDoublePath curve}
    {firstName lastName : Gaussian.Name.Basic.Named} {pieces : List (RootedWords.LiftedFragment axes domains mesh source
      count target)}
    (words : SourceWords.TourSourceWords tour firstName lastName pieces)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first)
    (onGrid : Grid.ContainsTourVertices base.bank.grid tour) :
    WalkGroups (Grid.splitTour base.bank.grid tour onGrid) firstName lastName pieces := by
  cases words with
  | mk forward right backward left =>
      have a := forward.walk_groups (fun piece member => moving piece
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))) onGrid.1
      have b := right.walk_groups (fun piece member => moving piece
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member)))) onGrid.2.1
      have c := backward.walk_groups (fun piece member => moving piece
        (List.mem_append_left _ (List.mem_append_right _ member))) onGrid.2.2.1
      have d := left.walk_groups (fun piece member => moving piece (List.mem_append_right _ member)) onGrid.2.2.2
      simpa only [Append.append_assoc, Grid.splitTour, -eq_self, -iff_self] using a.append (b.append (c.append d))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.TourSourceWords

end
