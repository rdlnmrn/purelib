module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Reverse
import Purelib.Data.Gaussian.Basic

open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk Lookup)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (HorizontalLine Interval VerticalLine)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

@[expose] public section

/-! Subdivision of an original increasing axis walk is the unique
increasing spine on the enlarged grid, with retained line ownership. -/

namespace Purelib.Polynomial.Geometry.Grid.Extension

open Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
  (horizontalWalk_increasing verticalWalk_increasing)
open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {original grid :
  ClearGrid polynomial ambient}

/-- The original horizontal window walk of an empty increasing axis is the empty coordinate walk. -/
private theorem horizontal_nil {x y : Fraction.Rational}
    (line : Lookup (key := HorizontalLine.coordinate) grid.horizontal y)
      :
    Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal (.nil x) line = Walk.nil
      (Gaussian.Components.Basic.point x y) := by
  rcases line with ⟨entry, member, rfl⟩
  rfl

/-- Joining increasing horizontal axes joins their original retained horizontal window walks. -/
private theorem horizontal_append {first middle last y : Fraction.Rational}
    (a : IncreasingWalk grid.xIntervals first middle) (b :
      IncreasingWalk grid.xIntervals middle last)
    (line : Lookup (key := HorizontalLine.coordinate) grid.horizontal y)
      :
    Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal (a.append b) line =
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal a line).append
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal b line) := by
  rcases line with ⟨entry, member, rfl⟩
  exact AxisChainCoherence.Walk.horizontalIncreasing_append entry member a b

/-- Joining increasing vertical axes joins their original retained vertical window walks. -/
private theorem vertical_append {first middle last x : Fraction.Rational}
    (a : IncreasingWalk grid.yIntervals first middle) (b :
      IncreasingWalk grid.yIntervals middle last)
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical x) :
    Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical line (a.append b) =
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical line a).append
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical line b) := by
  rcases line with ⟨entry, member, rfl⟩
  exact AxisChainCoherence.Walk.verticalIncreasing_append entry member a b

namespace CoordinateInclusion

variable (included : Geometry.Grid.Extension.CoordinateInclusion original grid)

/-- Resplitting an original increasing horizontal walk gives the retained finer-grid horizontal axis walk. -/
theorem resplit_horizontalIncreasing
    (oldLine : HorizontalLine polynomial ambient) (oldMember : oldLine ∈ original.horizontal)
    {first last : Fraction.Rational} (oldAxis : IncreasingWalk original.xIntervals first last)
    (lastMember : last ∈ original.vertical.map VerticalLine.coordinate)
    (axis : IncreasingWalk grid.xIntervals first last)
    (line : Lookup (key := HorizontalLine.coordinate) grid.horizontal
      oldLine.coordinate) :
    included.resplit (Walk.horizontalIncreasing oldLine oldMember oldAxis)
      ⟨lastMember, Data.List.Map.mem_map_of_mem oldMember⟩ = Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal
        axis line := by
  induction oldAxis with
  | nil point =>
      have equal := Geometry.Grid.AxisChainCoherence.IncreasingWalk.unique
        (Interval.adjacent_pairwise grid.vertical grid.vertical_ordered) axis (.nil point)
      rw [equal]
      exact (Geometry.Grid.Extension.horizontal_nil line).symm
  | @cons interval member finish tail ih =>
      have ends := Interval.endpoints_mem _ original.vertical_ordered member
      let headAxis := Geometry.Grid.AxisWalks.increasing interval.lower.coordinate interval.upper.coordinate
        grid.vertical grid.vertical_ordered
        (included.vertical _ (Data.List.Map.mem_map_of_mem ends.1))
        (included.vertical _ (Data.List.Map.mem_map_of_mem ends.2)) interval.ordered.le
      let tailAxis := Geometry.Grid.AxisWalks.increasing interval.upper.coordinate finish grid.vertical
        grid.vertical_ordered
        (included.vertical _ (Data.List.Map.mem_map_of_mem ends.2)) (included.vertical _ lastMember) tail.ordered
      have equal := Geometry.Grid.AxisChainCoherence.IncreasingWalk.unique
        (Interval.adjacent_pairwise grid.vertical grid.vertical_ordered)
        axis (headAxis.append tailAxis)
      rw [equal]
      erw [Geometry.Grid.Extension.horizontal_append]
      change (Geometry.Grid.Walks.horizontalWalk grid interval.lower.coordinate interval.upper.coordinate
        oldLine.coordinate _ _ _).append
        (included.resplit (Walk.horizontalIncreasing oldLine oldMember tail)
          ⟨lastMember, Data.List.Map.mem_map_of_mem oldMember⟩) = _
      rw [AxisChainCoherence.horizontalWalk_increasing headAxis line]
      exact congrArg (fun rest => (Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal headAxis line).append
        rest) (ih lastMember tailAxis)

/-- Resplitting an original increasing vertical walk gives the retained finer-grid vertical axis walk. -/
theorem resplit_verticalIncreasing
    (oldLine : VerticalLine polynomial ambient) (oldMember : oldLine ∈ original.vertical)
    {first last : Fraction.Rational} (oldAxis : IncreasingWalk original.yIntervals first last)
    (lastMember : last ∈ original.horizontal.map HorizontalLine.coordinate)
    (axis : IncreasingWalk grid.yIntervals first last)
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical
      oldLine.coordinate) :
    included.resplit (Walk.verticalIncreasing oldLine oldMember oldAxis)
      ⟨Data.List.Map.mem_map_of_mem oldMember, lastMember⟩ = Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical
        line axis := by
  induction oldAxis with
  | nil point =>
      have equal := Geometry.Grid.AxisChainCoherence.IncreasingWalk.unique
        (Interval.adjacent_pairwise grid.horizontal grid.horizontal_ordered) axis (.nil point)
      rw [equal]
      exact (AxisChainCoherence.WindowCircuits.vertical_nil_eq line).symm
  | @cons interval member finish tail ih =>
      have ends := Interval.endpoints_mem _ original.horizontal_ordered member
      let headAxis := Geometry.Grid.AxisWalks.increasing interval.lower.coordinate interval.upper.coordinate
        grid.horizontal grid.horizontal_ordered
        (included.horizontal _ (Data.List.Map.mem_map_of_mem ends.1))
        (included.horizontal _ (Data.List.Map.mem_map_of_mem ends.2)) interval.ordered.le
      let tailAxis := Geometry.Grid.AxisWalks.increasing interval.upper.coordinate finish grid.horizontal
        grid.horizontal_ordered
        (included.horizontal _ (Data.List.Map.mem_map_of_mem ends.2)) (included.horizontal _ lastMember) tail.ordered
      have equal := Geometry.Grid.AxisChainCoherence.IncreasingWalk.unique
        (Interval.adjacent_pairwise grid.horizontal grid.horizontal_ordered)
        axis (headAxis.append tailAxis)
      rw [equal]
      erw [Geometry.Grid.Extension.vertical_append]
      change (Geometry.Grid.Walks.verticalWalk grid oldLine.coordinate interval.lower.coordinate
        interval.upper.coordinate _ _ _).append
        (included.resplit (Walk.verticalIncreasing oldLine oldMember tail)
          ⟨Data.List.Map.mem_map_of_mem oldMember, lastMember⟩) = _
      rw [AxisChainCoherence.verticalWalk_increasing headAxis line]
      exact congrArg (fun rest => (Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical line headAxis).append rest)
        (ih lastMember tailAxis)

end CoordinateInclusion
end Purelib.Polynomial.Geometry.Grid.Extension
