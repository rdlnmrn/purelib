module
import Purelib.Data.List.Reverse
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ParentGroups
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
public import Purelib.Polynomial.Geometry.Grid.Axis.Partial
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentAxisGroups
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
meta import Mathlib.Tactic.Linter.Lint

public section

/-! Recover complete rooted walk groups from the actual retained adjacent
interval grouping, without replacing any query owner or prepared fragment. -/

section

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.Axis
open Purelib.Polynomial.Geometry.Grid.Axis.Partial
open Purelib.Polynomial.Geometry.Grid.Walks
open Purelib.Riemann.Paths

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval HorizontalLine VerticalLine)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.Axis.Partial (PartialWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment (RootedWord)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry (Presents horizontal_source_queries
  vertical_source_queries horizontal_source_geometry vertical_source_geometry)
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
  {ambient : Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisWalkGroups

/-- An original partial walk with strictly increasing endpoints contains at least one retained piece. -/
private theorem partial_nonempty {Alpha : Type u} {Piece : Type v} {key : Alpha → Fraction.Rational}
    {span : Piece → ClearGrid.Interval key} {first last : Piece → Fraction.Rational} {intervals : List
      (ClearGrid.Interval key)}
    {pieces : List Piece} {a b : Fraction.Rational}
    (path : Partial.PartialWalk span first last intervals pieces a b) (different : a < b) : pieces ≠ [] := by
  intro empty
  subst pieces
  cases path
  exact lt_irrefl _ different

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisWalkGroups

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups

/-- Construct all complete horizontal rooted groups along the actual increasing grid walk from its retained coordinate
grouping. -/
theorem horizontal_increasing
    (line : ClearGrid.HorizontalLine curve.polynomial (Cuts.Ambient curve)) (onLine : line ∈ base.bank.grid.horizontal)
    {a b : Fraction.Rational} (axis : AxisWalks.IncreasingWalk base.bank.grid.xIntervals a b)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} {firstName lastName :
      Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces (Components.Basic.point a line.coordinate) firstName
      (Components.Basic.point b line.coordinate) lastName)
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first)
    (flat : start.im = finish.im) (lineEq : start.im = line.coordinate)
    (groups : PartialWalk.Groups (fun piece => piece.fragment.located.cell.horizontal)
      (fun piece => piece.first.re) (fun piece => piece.last.re) base.bank.grid.xIntervals axis.edges pieces) :
    WalkGroups (Walk.horizontalIncreasing line onLine axis) firstName lastName pieces := by
  induction axis generalizing pieces firstName with
  | nil point =>
      cases groups
      cases word with
      | nil equal root => exact .nil root
  | cons interval member tail ih =>
      cases groups with
      | @cons _ block pieces _ same path remaining =>
          have nonempty := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisWalkGroups.partial_nonempty path
            interval.ordered
          obtain ⟨middle, middleName, blockWord, restWord⟩ := RootedWord.split block word
          have blockOriginal : ∀ piece ∈ block, PreparedSegmentSources.SegmentSource segment piece.parent :=
            fun piece present => original piece (List.mem_append_left _ present)
          have varying := RootedWord.partial_finish Data.Gaussian.Basic.re _ blockWord path rfl
          have fixed := RootedWord.constant_finish Data.Gaussian.Basic.im blockWord rfl
            (fun piece present => ((SourceGeometry.horizontal_source_queries piece (blockOriginal piece present)
              flat).2).trans lineEq)
          have middleEq : middle = (Components.Basic.point interval.upper.coordinate line.coordinate) :=
            Data.Gaussian.Basic.ext varying fixed
          have rest := ih (restWord.changeStart middleEq.symm ⟨NamedEquivalent.refl _⟩)
            (fun piece present => original piece (List.mem_append_right _ present))
            (fun piece present => moving piece (List.mem_append_right _ present)) remaining
          cases block with
          | nil => exact (nonempty rfl).elim
          | cons head block =>
              apply WalkGroups.cons (blockWord.castFinish middleEq) blockOriginal
                (fun piece present => moving piece (List.mem_append_left _ present)) _ rest
              intro piece present
              have geometry := SourceGeometry.horizontal_source_geometry piece (blockOriginal piece present)
                (moving piece (List.mem_append_left _ present)) flat
              rw [same piece present, lineEq] at geometry
              exact geometry

/-- Construct all complete vertical rooted groups along the actual increasing grid walk from its retained coordinate
grouping. -/
theorem vertical_increasing
    (line : ClearGrid.VerticalLine curve.polynomial (Cuts.Ambient curve)) (onLine : line ∈ base.bank.grid.vertical)
    {a b : Fraction.Rational} (axis : AxisWalks.IncreasingWalk base.bank.grid.yIntervals a b)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} {firstName lastName :
      Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces (Components.Basic.point line.coordinate a) firstName
      (Components.Basic.point line.coordinate b) lastName)
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first)
    (flat : start.re = finish.re) (lineEq : start.re = line.coordinate)
    (groups : PartialWalk.Groups (fun piece => piece.fragment.located.cell.vertical)
      (fun piece => piece.first.im) (fun piece => piece.last.im) base.bank.grid.yIntervals axis.edges pieces) :
    WalkGroups (Walk.verticalIncreasing line onLine axis) firstName lastName pieces := by
  induction axis generalizing pieces firstName with
  | nil point =>
      cases groups
      cases word with
      | nil equal root => exact .nil root
  | cons interval member tail ih =>
      cases groups with
      | @cons _ block pieces _ same path remaining =>
          have nonempty := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisWalkGroups.partial_nonempty path
            interval.ordered
          obtain ⟨middle, middleName, blockWord, restWord⟩ := RootedWord.split block word
          have blockOriginal : ∀ piece ∈ block, PreparedSegmentSources.SegmentSource segment piece.parent :=
            fun piece present => original piece (List.mem_append_left _ present)
          have varying := RootedWord.partial_finish Data.Gaussian.Basic.im _ blockWord path rfl
          have fixed := RootedWord.constant_finish Data.Gaussian.Basic.re blockWord rfl
            (fun piece present => ((SourceGeometry.vertical_source_queries piece (blockOriginal piece present)
              flat).2).trans lineEq)
          have middleEq : middle = (Components.Basic.point line.coordinate interval.upper.coordinate) :=
            Data.Gaussian.Basic.ext fixed varying
          have rest := ih (restWord.changeStart middleEq.symm ⟨NamedEquivalent.refl _⟩)
            (fun piece present => original piece (List.mem_append_right _ present))
            (fun piece present => moving piece (List.mem_append_right _ present)) remaining
          cases block with
          | nil => exact (nonempty rfl).elim
          | cons head block =>
              apply WalkGroups.cons (blockWord.castFinish middleEq) blockOriginal
                (fun piece present => moving piece (List.mem_append_left _ present)) _ rest
              intro piece present
              have geometry := SourceGeometry.vertical_source_geometry piece (blockOriginal piece present)
                (moving piece (List.mem_append_left _ present)) flat
              rw [same piece present, lineEq] at geometry
              exact geometry

/-- Reverse coordinate groups are consumed in the original root-word order, matching the actual reversed horizontal grid
walk. -/
theorem horizontal_decreasing
    (line : ClearGrid.HorizontalLine curve.polynomial (Cuts.Ambient curve)) (onLine : line ∈ base.bank.grid.horizontal)
    {a b : Fraction.Rational} (axis : AxisWalks.IncreasingWalk base.bank.grid.xIntervals a b)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} {firstName lastName :
      Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces.reverse (Components.Basic.point b line.coordinate) firstName
      (Components.Basic.point a line.coordinate) lastName)
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first)
    (flat : start.im = finish.im) (lineEq : start.im = line.coordinate)
    (groups : PartialWalk.Groups (fun piece => piece.fragment.located.cell.horizontal)
      (fun piece => piece.last.re) (fun piece => piece.first.re) base.bank.grid.xIntervals axis.edges pieces) :
    WalkGroups (Walk.horizontalIncreasing line onLine axis).reverse firstName lastName pieces.reverse := by
  induction axis generalizing pieces firstName lastName with
  | nil point =>
      cases groups
      cases word with
      | nil equal root => exact .nil root
  | cons interval member tail ih =>
      cases groups with
      | @cons _ block pieces _ same path remaining =>
          have nonempty := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisWalkGroups.partial_nonempty path
            interval.ordered
          rw [Reverse.reverse_append] at word
          obtain ⟨middle, middleName, restWord, blockWord⟩ := RootedWord.split pieces.reverse word
          have blockOriginal : ∀ piece ∈ block.reverse, PreparedSegmentSources.SegmentSource segment piece.parent :=
            fun piece present => original piece (List.mem_append_left _ ((Reverse.mem_reverse _).mp present))
          have blockMoving : ∀ piece ∈ block.reverse, piece.last ≠ piece.first :=
            fun piece present => moving piece (List.mem_append_left _ ((Reverse.mem_reverse _).mp present))
          have reversedPath : Partial.PartialWalk (fun piece => piece.fragment.located.cell.horizontal)
              (fun piece => piece.last.re) (fun piece => piece.first.re) base.bank.grid.xIntervals
              block.reverse.reverse interval.lower.coordinate interval.upper.coordinate := by
            simpa only [Reverse.reverse_reverse, -eq_self, -iff_self] using path
          have varying := RootedWord.reverse_partial_start Data.Gaussian.Basic.re _ blockWord reversedPath rfl
          have fixed := RootedWord.constant_start Data.Gaussian.Basic.im blockWord rfl
            (fun piece present => ((SourceGeometry.horizontal_source_queries piece (blockOriginal piece present)
              flat).1).trans lineEq)
          have middleEq : middle = (Components.Basic.point interval.upper.coordinate line.coordinate) :=
            Data.Gaussian.Basic.ext varying fixed
          have rest := ih (restWord.castFinish middleEq)
            (fun piece present => original piece (List.mem_append_right _ present))
            (fun piece present => moving piece (List.mem_append_right _ present)) remaining
          have lastGroup : WalkGroups (Walk.cons (Edge.reverse (Edge.horizontal interval member line onLine))
            (.nil _))
              middleName lastName block.reverse := by
            have fullWord := blockWord.changeStart middleEq.symm ⟨NamedEquivalent.refl _⟩
            have fullGeometry : ∀ piece ∈ block.reverse,
                SourceGeometry.Presents piece (Components.Basic.point interval.upper.coordinate line.coordinate)
                  (Components.Basic.point interval.lower.coordinate line.coordinate) := by
              intro piece present
              have geometry := SourceGeometry.horizontal_source_geometry piece (blockOriginal piece present)
                (blockMoving piece present) flat
              rw [same piece ((Reverse.mem_reverse _).mp present), lineEq] at geometry
              exact geometry.elim (fun positive => Or.inr ⟨positive.2, positive.1⟩)
                (fun negative => Or.inl ⟨negative.2, negative.1⟩)
            cases equal : block.reverse with
            | nil =>
                have empty := congrArg List.reverse equal
                exact (nonempty (by
                    simpa only [Reverse.reverse_reverse, List.reverse_nil, -eq_self, -iff_self]
                      using empty)).elim
            | cons head tail =>
                rw [equal] at fullWord blockOriginal blockMoving fullGeometry
                simpa only [Append.append_nil, -eq_self, -iff_self] using
                  (WalkGroups.cons (edge := .reverse (.horizontal interval member line onLine))
                    fullWord blockOriginal blockMoving fullGeometry (.nil ⟨NamedEquivalent.refl _⟩))
          change WalkGroups ((Walk.horizontalIncreasing line onLine tail).reverseOnto
            (.cons (.reverse (.horizontal interval member line onLine)) (.nil _))) _ _ _
          rw [Walk.reverseOnto_eq_append, Reverse.reverse_append]
          exact rest.append lastGroup

/-- Reverse coordinate groups are consumed in the original root-word order, matching the actual reversed vertical grid
walk. -/
theorem vertical_decreasing
    (line : ClearGrid.VerticalLine curve.polynomial (Cuts.Ambient curve)) (onLine : line ∈ base.bank.grid.vertical)
    {a b : Fraction.Rational} (axis : AxisWalks.IncreasingWalk base.bank.grid.yIntervals a b)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} {firstName lastName :
      Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces.reverse (Components.Basic.point line.coordinate b) firstName
      (Components.Basic.point line.coordinate a) lastName)
    (original : ∀ piece ∈ pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ pieces, piece.last ≠ piece.first)
    (flat : start.re = finish.re) (lineEq : start.re = line.coordinate)
    (groups : PartialWalk.Groups (fun piece => piece.fragment.located.cell.vertical)
      (fun piece => piece.last.im) (fun piece => piece.first.im) base.bank.grid.yIntervals axis.edges pieces) :
    WalkGroups (Walk.verticalIncreasing line onLine axis).reverse firstName lastName pieces.reverse := by
  induction axis generalizing pieces firstName lastName with
  | nil point =>
      cases groups
      cases word with
      | nil equal root => exact .nil root
  | cons interval member tail ih =>
      cases groups with
      | @cons _ block pieces _ same path remaining =>
          have nonempty := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisWalkGroups.partial_nonempty path
            interval.ordered
          rw [Reverse.reverse_append] at word
          obtain ⟨middle, middleName, restWord, blockWord⟩ := RootedWord.split pieces.reverse word
          have blockOriginal : ∀ piece ∈ block.reverse, PreparedSegmentSources.SegmentSource segment piece.parent :=
            fun piece present => original piece (List.mem_append_left _ ((Reverse.mem_reverse _).mp present))
          have blockMoving : ∀ piece ∈ block.reverse, piece.last ≠ piece.first :=
            fun piece present => moving piece (List.mem_append_left _ ((Reverse.mem_reverse _).mp present))
          have reversedPath : Partial.PartialWalk (fun piece => piece.fragment.located.cell.vertical)
              (fun piece => piece.last.im) (fun piece => piece.first.im) base.bank.grid.yIntervals
              block.reverse.reverse interval.lower.coordinate interval.upper.coordinate := by
            simpa only [Reverse.reverse_reverse, -eq_self, -iff_self] using path
          have varying := RootedWord.reverse_partial_start Data.Gaussian.Basic.im _ blockWord reversedPath rfl
          have fixed := RootedWord.constant_start Data.Gaussian.Basic.re blockWord rfl
            (fun piece present => ((SourceGeometry.vertical_source_queries piece (blockOriginal piece present)
              flat).1).trans lineEq)
          have middleEq : middle = (Components.Basic.point line.coordinate interval.upper.coordinate) :=
            Data.Gaussian.Basic.ext fixed varying
          have rest := ih (restWord.castFinish middleEq)
            (fun piece present => original piece (List.mem_append_right _ present))
            (fun piece present => moving piece (List.mem_append_right _ present)) remaining
          have lastGroup : WalkGroups (Walk.cons (Edge.reverse (Edge.vertical interval member line onLine))
            (.nil _))
              middleName lastName block.reverse := by
            have fullWord := blockWord.changeStart middleEq.symm ⟨NamedEquivalent.refl _⟩
            have fullGeometry : ∀ piece ∈ block.reverse,
                SourceGeometry.Presents piece (Components.Basic.point line.coordinate interval.upper.coordinate)
                  (Components.Basic.point line.coordinate interval.lower.coordinate) := by
              intro piece present
              have geometry := SourceGeometry.vertical_source_geometry piece (blockOriginal piece present) (blockMoving
                piece present) flat
              rw [same piece ((Reverse.mem_reverse _).mp present), lineEq] at geometry
              exact geometry.elim (fun positive => Or.inr ⟨positive.2, positive.1⟩)
                (fun negative => Or.inl ⟨negative.2, negative.1⟩)
            cases equal : block.reverse with
            | nil =>
                have empty := congrArg List.reverse equal
                exact (nonempty (by
                    simpa only [Reverse.reverse_reverse, List.reverse_nil, -eq_self, -iff_self]
                      using empty)).elim
            | cons head tail =>
                rw [equal] at fullWord blockOriginal blockMoving fullGeometry
                simpa only [Append.append_nil, -eq_self, -iff_self] using
                  (WalkGroups.cons (edge := .reverse (.vertical interval member line onLine))
                    fullWord blockOriginal blockMoving fullGeometry (.nil ⟨NamedEquivalent.refl _⟩))
          change WalkGroups ((Walk.verticalIncreasing line onLine tail).reverseOnto
            (.cons (.reverse (.vertical interval member line onLine)) (.nil _))) _ _ _
          rw [Walk.reverseOnto_eq_append, Reverse.reverse_append]
          exact rest.append lastGroup

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups

end
