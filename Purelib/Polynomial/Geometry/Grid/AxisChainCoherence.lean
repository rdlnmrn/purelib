module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowAxes
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport

open Purelib.Polynomial.Geometry.Grid.AxisWalks (Lookup)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (HorizontalLine Interval VerticalLine)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

@[expose] public section

/-!
# Actual adjacent-axis paths and their reversed connectors

Monotone walks through the retained separated interval bank have a unique
literal spine. The lifted comparisons below account for reversal on both
initial sheets, including the double reversals in common-root connectors.
-/

namespace Purelib.Polynomial.Geometry.Grid

section IncreasingWalk

variable {Alpha : Type} {key : Alpha → Fraction.Rational} {intervals : List (Interval key)}

namespace AxisWalks.IncreasingWalk

/-- Append consecutive increasing axis walks, retaining their original interval occurrences. -/
def append : {first middle last : Fraction.Rational} →
  Geometry.Grid.AxisWalks.IncreasingWalk intervals first middle →
    Geometry.Grid.AxisWalks.IncreasingWalk intervals middle last → Geometry.Grid.AxisWalks.IncreasingWalk intervals
      first last
  | _, _, _, .nil _, last => last
  | _, _, _, .cons interval member tail, last => .cons interval member (tail.append last)

end AxisWalks.IncreasingWalk

namespace AxisChainCoherence.IncreasingWalk

/-- Increasing walks with equal endpoint coordinates and edge lists are heterogeneously equal. -/
private theorem heq_of_edges : {first last : Fraction.Rational} → (a : Geometry.Grid.AxisWalks.IncreasingWalk intervals
  first last) →
    {otherFirst otherLast : Fraction.Rational} → (b : Geometry.Grid.AxisWalks.IncreasingWalk intervals otherFirst
      otherLast) →
    first = otherFirst → last = otherLast → a.edges = b.edges → HEq a b
  | _, _, .nil _, _, _, .nil _, firstEq, _, _ => by cases firstEq; rfl
  | _, _, .nil _, _, _, .cons _ _ _, _, _, same => by
    simp only [Geometry.Grid.AxisWalks.IncreasingWalk.edges] at same; cases same
  | _, _, .cons _ _ _, _, _, .nil _, _, _, same => by
    simp only [Geometry.Grid.AxisWalks.IncreasingWalk.edges] at same; cases same
  | _, _, .cons interval member tail, _, _, .cons other otherMember rest, _, lastEq, same => by
      have heads := (List.cons.inj same).1
      cases heads
      cases lastEq
      have tails := eq_of_heq (heq_of_edges tail rest
        rfl rfl (List.cons.inj same).2)
      cases tails
      rfl

end AxisChainCoherence.IncreasingWalk

namespace AxisChainCoherence.IncreasingWalk

/-- The literal edge list determines an increasing walk with fixed endpoints. -/
theorem eq_of_edges {first last : Fraction.Rational} (a b : Geometry.Grid.AxisWalks.IncreasingWalk intervals first last)
    (same : a.edges = b.edges) : a = b := eq_of_heq (heq_of_edges a b
      rfl rfl same)

end AxisChainCoherence.IncreasingWalk

namespace AxisChainCoherence.IncreasingWalk

/-- A separated interval bank has a unique increasing walk between fixed endpoints.

Both walks select the same bounded sublist of the original interval bank. -/
theorem unique (separated : intervals.Pairwise Interval.Before) {first last : Fraction.Rational}
    (a b : Geometry.Grid.AxisWalks.IncreasingWalk intervals first last) : a = b :=
  eq_of_edges a b
    ((Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter separated a).trans
    (Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter separated b).symm)

end AxisChainCoherence.IncreasingWalk

end IncreasingWalk

section Grid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}

namespace AxisChainCoherence.Walk

/-- Lifting consecutive horizontal axis walks commutes with appending them. -/
theorem horizontalIncreasing_append (line : HorizontalLine polynomial ambient) (member : line ∈
  grid.horizontal) :
    {first middle last : Fraction.Rational} → (a : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals first middle)
      →
    (b : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals middle last) →
    Geometry.Grid.Walks.Walk.horizontalIncreasing line member (a.append b) =
      (Geometry.Grid.Walks.Walk.horizontalIncreasing line member a).append
      (Geometry.Grid.Walks.Walk.horizontalIncreasing line member b)
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons interval adjacent tail, b =>
      congrArg (Geometry.Grid.Walks.Walk.cons (.horizontal interval adjacent line member))
        (horizontalIncreasing_append line member tail b)

/-- Lifting consecutive vertical axis walks commutes with appending them. -/
theorem verticalIncreasing_append (line : VerticalLine polynomial ambient) (member : line ∈
  grid.vertical) :
    {first middle last : Fraction.Rational} → (a : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals first middle)
      →
    (b : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals middle last) →
    Geometry.Grid.Walks.Walk.verticalIncreasing line member (a.append b) = (Geometry.Grid.Walks.Walk.verticalIncreasing
      line member a).append (Geometry.Grid.Walks.Walk.verticalIncreasing line member b)
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons interval adjacent tail, b =>
      congrArg (Geometry.Grid.Walks.Walk.cons (.vertical interval adjacent line member))
        (verticalIncreasing_append line member tail b)

/-- Transporting the endpoints of an appended walk agrees with transporting its two parts. -/
theorem castEndpoints_append {first middle last a b c : Gaussian.Basic.Canonical} (left : Geometry.Grid.Walks.Walk grid
  first middle) (right : Geometry.Grid.Walks.Walk grid middle last)
    (firstEq : first = a) (middleEq : middle = b) (lastEq : last = c) :
    (left.append right).castEndpoints firstEq lastEq =
      (left.castEndpoints firstEq middleEq).append (right.castEndpoints middleEq lastEq) := by
  cases firstEq
  cases middleEq
  cases lastEq
  rfl

/-- Endpoint transport commutes with walk reversal, exchanging the endpoint equalities. -/
theorem castEndpoints_reverse {first last a b : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid first
  last)
    (firstEq : first = a) (lastEq : last = b) :
    (walk.castEndpoints firstEq lastEq).reverse = walk.reverse.castEndpoints lastEq firstEq := by
  cases firstEq
  cases lastEq
  rfl

end AxisChainCoherence.Walk

namespace AxisChainCoherence.WindowCircuits

open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits (vertical side)

/-- The vertical lift of an empty axis walk is stationary. -/
theorem vertical_nil_eq {x y : Fraction.Rational}
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical x) :
    Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical line (.nil y) = Geometry.Grid.Walks.Walk.nil
      (Gaussian.Components.Basic.point x y) := by
  rcases line with ⟨entry, member, rfl⟩
  rfl

/-- The vertical lift of a retained axis step prepends its actual band-side edge. -/
theorem vertical_cons_eq {x finish : Fraction.Rational}
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical x)
    (band : Interval (HorizontalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (member : band ∈ grid.yIntervals) (tail : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals
      band.upper.coordinate finish) :
    Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical line (.cons band member tail) = .cons
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.side band member line)
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical line tail) := by
  rcases line with ⟨entry, member, rfl⟩
  rfl

end AxisChainCoherence.WindowCircuits

namespace AxisChainCoherence

/-- The searched horizontal grid walk equals the retained increasing axis lift between the same endpoints. -/
theorem horizontalWalk_increasing {first last y : Fraction.Rational}
    (axis : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals first last)
    (line : Lookup (key := HorizontalLine.coordinate) grid.horizontal y)
    (firstMember : first ∈ grid.vertical.map VerticalLine.coordinate)
    (lastMember : last ∈ grid.vertical.map VerticalLine.coordinate)
    (lineMember : y ∈ grid.horizontal.map HorizontalLine.coordinate) :
    Geometry.Grid.Walks.horizontalWalk grid first last y firstMember lastMember lineMember =
      Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal axis line := by
  simp only [Geometry.Grid.Walks.horizontalWalk, Geometry.Grid.AxisWalks.walk, dif_pos axis.ordered,
    Geometry.Grid.Walks.Walk.horizontalAxis]
  exact congrArg₂ (fun path fixed => Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal path fixed)
    (Geometry.Grid.AxisChainCoherence.IncreasingWalk.unique (Interval.adjacent_pairwise
      grid.vertical grid.vertical_ordered)
      (Geometry.Grid.AxisWalks.increasing first last grid.vertical grid.vertical_ordered firstMember lastMember
        axis.ordered) axis)
    (Geometry.Grid.WindowCircuitOrder.WindowCircuits.lookup_unique grid.horizontal_ordered
      (Geometry.Grid.AxisWalks.lookup y grid.horizontal lineMember) line)

end AxisChainCoherence

namespace AxisChainCoherence

/-- The searched vertical grid walk equals the retained increasing axis lift between the same endpoints. -/
theorem verticalWalk_increasing {first last x : Fraction.Rational}
    (axis : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals first last)
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical x)
    (lineMember : x ∈ grid.vertical.map VerticalLine.coordinate)
    (firstMember : first ∈ grid.horizontal.map HorizontalLine.coordinate)
    (lastMember : last ∈ grid.horizontal.map HorizontalLine.coordinate) :
    Geometry.Grid.Walks.verticalWalk grid x first last lineMember firstMember lastMember =
      Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical line axis := by
  simp only [Geometry.Grid.Walks.verticalWalk, Geometry.Grid.AxisWalks.walk, dif_pos axis.ordered,
    Geometry.Grid.Walks.Walk.verticalAxis]
  exact congrArg₂ (fun fixed path => Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical fixed path)
    (Geometry.Grid.WindowCircuitOrder.WindowCircuits.lookup_unique grid.vertical_ordered (Geometry.Grid.AxisWalks.lookup
      x grid.vertical lineMember) line)
    (Geometry.Grid.AxisChainCoherence.IncreasingWalk.unique (Interval.adjacent_pairwise
      grid.horizontal grid.horizontal_ordered)
      (Geometry.Grid.AxisWalks.increasing first last grid.horizontal grid.horizontal_ordered firstMember lastMember
        axis.ordered) axis)

end AxisChainCoherence

namespace AxisChainCoherence

/-- The searched horizontal grid walk in the opposite direction equals the reversal of the retained increasing axis
lift. -/
theorem horizontalWalk_decreasing {first last y : Fraction.Rational}
    (axis : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals first last)
    (line : Lookup (key := HorizontalLine.coordinate) grid.horizontal y)
    (firstMember : first ∈ grid.vertical.map VerticalLine.coordinate)
    (lastMember : last ∈ grid.vertical.map VerticalLine.coordinate)
    (lineMember : y ∈ grid.horizontal.map HorizontalLine.coordinate) :
    Geometry.Grid.Walks.horizontalWalk grid last first y lastMember firstMember lineMember =
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal axis line).reverse := by
  by_cases ordered : last ≤ first
  · have equal := le_antisymm axis.ordered ordered
    subst last
    rw [horizontalWalk_increasing axis line,
      Geometry.Grid.AxisChainCoherence.IncreasingWalk.unique
      (Interval.adjacent_pairwise grid.vertical grid.vertical_ordered) axis (.nil first)]
    rcases line with ⟨entry, member, rfl⟩
    rfl
  · simp only [Geometry.Grid.Walks.horizontalWalk, Geometry.Grid.AxisWalks.walk, dif_neg ordered,
      Geometry.Grid.Walks.Walk.horizontalAxis]
    have actual := congrArg₂ (fun path fixed => (Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal path
      fixed).reverse)
      (Geometry.Grid.AxisChainCoherence.IncreasingWalk.unique (Interval.adjacent_pairwise
        grid.vertical grid.vertical_ordered)
        (Geometry.Grid.AxisWalks.increasing first last grid.vertical grid.vertical_ordered firstMember lastMember
          (le_of_not_ge ordered)) axis)
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.lookup_unique grid.horizontal_ordered
        (Geometry.Grid.AxisWalks.lookup y grid.horizontal lineMember) line)
    exact (Walk.castEndpoints_reverse _ _ _).symm.trans actual

end AxisChainCoherence

namespace AxisChainCoherence

/-- The searched vertical grid walk in the opposite direction equals the reversal of the retained increasing axis lift.
-/
theorem verticalWalk_decreasing {first last x : Fraction.Rational}
    (axis : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals first last)
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical x)
    (lineMember : x ∈ grid.vertical.map VerticalLine.coordinate)
    (firstMember : first ∈ grid.horizontal.map HorizontalLine.coordinate)
    (lastMember : last ∈ grid.horizontal.map HorizontalLine.coordinate) :
    Geometry.Grid.Walks.verticalWalk grid x last first lineMember lastMember firstMember =
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical line axis).reverse := by
  by_cases ordered : last ≤ first
  · have equal := le_antisymm axis.ordered ordered
    subst last
    rw [verticalWalk_increasing axis line,
      Geometry.Grid.AxisChainCoherence.IncreasingWalk.unique
      (Interval.adjacent_pairwise grid.horizontal grid.horizontal_ordered) axis (.nil first)]
    rcases line with ⟨entry, member, rfl⟩
    rfl
  · simp only [Geometry.Grid.Walks.verticalWalk, Geometry.Grid.AxisWalks.walk, dif_neg ordered,
      Geometry.Grid.Walks.Walk.verticalAxis]
    have actual := congrArg₂ (fun fixed path => (Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical fixed
      path).reverse)
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.lookup_unique grid.vertical_ordered
        (Geometry.Grid.AxisWalks.lookup x grid.vertical lineMember) line)
      (Geometry.Grid.AxisChainCoherence.IncreasingWalk.unique (Interval.adjacent_pairwise
        grid.horizontal grid.horizontal_ordered)
        (Geometry.Grid.AxisWalks.increasing first last grid.horizontal grid.horizontal_ordered firstMember lastMember
          (le_of_not_ge ordered)) axis)
    exact (Walk.castEndpoints_reverse _ _ _).symm.trans actual

end AxisChainCoherence

namespace AxisChainCoherence.RootEdgeBank.ChainComparison

variable {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {vertices :
  RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid} {edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

section ChainComparison

/-- Reverse a lifted chain comparison while preserving both sheet targets and reversed indexed words. -/
theorem reverse (reference : ∀ point, FromStates.ContainsVertex grid point →
  WindingOneLoop polynomial point)
    {first last : Gaussian.Basic.Canonical} {a b : Geometry.Grid.Walks.Walk grid first last} (same :
      RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices a b) :
    RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices a.reverse b.reverse
      := by
  have targets (sheet : Fin 2) : RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges a.reverse sheet =
    RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges b.reverse sheet := by
    apply edges.target_injective reference b
    rw [← same.targets, edges.target_reverse_right reference, edges.target_reverse_right reference]
  refine ⟨targets, ?_⟩
  intro sheet
  have first := edges.indexedEdges_reverse vertices reference a
    (RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges a.reverse sheet)
  have last := edges.indexedEdges_reverse vertices reference b
    (RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges b.reverse sheet)
  rw [edges.target_reverse_right reference] at first last
  rw [first, last, targets]
  exact (same.words _).reverse

/-- Double reversal agrees with the original walk on the retained lifted edge bank. -/
theorem reverse_reverse (reference : ∀ point, FromStates.ContainsVertex grid point →
  WindingOneLoop polynomial point)
    {first last : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid first last) :
    RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices walk.reverse.reverse
      walk where
  targets := fun sheet => by
    apply edges.target_injective reference walk.reverse
    exact (edges.target_reverse_right reference walk.reverse sheet).trans (edges.target_reverse reference walk
      sheet).symm
  words := fun sheet => by
    have reversed := edges.indexedEdges_reverse vertices reference walk.reverse
      (RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges walk sheet)
    rw [edges.target_reverse reference] at reversed
    rw [reversed, edges.indexedEdges_reverse vertices reference]
    exact Topology.Mesh.RetracingWords.Retracing.of_eq
      (Topology.Mesh.RetracingWords.CutPath.reverse_reverse _)

/-- Transporting endpoint identities preserves the lifted chain comparison. -/
theorem castEndpoints
    {first last a b : Gaussian.Basic.Canonical} {left right : Geometry.Grid.Walks.Walk grid first last} (same :
      RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices left right)
    (firstEq : first = a) (lastEq : last = b) :
    RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (left.castEndpoints
      firstEq lastEq) (right.castEndpoints firstEq lastEq) := by
  cases firstEq
  cases lastEq
  exact same

/-- Replacing a connector by a compared connector preserves the based loop's lifted chain comparison.

The comparison uses the forward connector, original loop and reversed connector on their actual arriving sheets. -/
theorem based_stem (reference : ∀ point, FromStates.ContainsVertex grid point →
  WindingOneLoop polynomial point)
    {first last : Gaussian.Basic.Canonical} {a b : Geometry.Grid.Walks.Walk grid first last} (same :
      RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices a b)
    (loop : Geometry.Grid.Walks.Walk grid last last) :
      RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (a.based loop)
      (b.based loop) :=
  same.append ((RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison.refl loop).append
    (reverse reference same))

end ChainComparison
end AxisChainCoherence.RootEdgeBank.ChainComparison

section Window

variable {box : Box}

namespace WindowBoundary.Window

/-- Follow the retained left side and then the top side from the southwest to northeast corner. -/
def northEast (window :
  Window grid box) : Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point
  box.xLower box.yLower) (Gaussian.Components.Basic.point box.xUpper box.yUpper) :=
  (window.vertical window.left).append (window.horizontal window.top)

end WindowBoundary.Window

namespace AxisChainCoherence.Window

/-- The reversed opposite connector is exactly the positive left/top route
on the lifted edge bank, including independently prepared monotone spines. -/
theorem reverse_connect_comparison {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {vertices :
  RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid} {edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
    (window : WindowBoundary.Window grid box)
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      WindingOneLoop polynomial point)
    (first : FromStates.ContainsVertex grid (Gaussian.Components.Basic.point box.xLower box.yLower))
    (last : FromStates.ContainsVertex grid (Gaussian.Components.Basic.point box.xUpper box.yUpper)) :
    RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid.connect grid _ _ last first).reverse
      window.northEast := by
  change RootIsolation.SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
    ((Geometry.Grid.Walks.horizontalWalk grid box.xUpper box.xLower box.yUpper last.1 first.1 last.2).append
      (Geometry.Grid.Walks.verticalWalk grid box.xLower box.yUpper box.yLower first.1 last.2 first.2)).reverse _
  rw [horizontalWalk_decreasing window.x window.top,
    verticalWalk_decreasing window.y window.left,
    Polynomial.Geometry.Grid.Walks.Walk.reverse_append]
  exact (RootEdgeBank.ChainComparison.reverse_reverse reference _).append
    (RootEdgeBank.ChainComparison.reverse_reverse reference _)

end AxisChainCoherence.Window

end Window
end Grid
end Purelib.Polynomial.Geometry.Grid
