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

open Purelib.RootIsolation.SquareRoot.Grid

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

open Purelib.Data.Gaussian

section IncreasingWalk

variable {Alpha : Type} {key : Alpha → Fraction.Rational} {intervals : List (Interval key)}

namespace AxisWalks.IncreasingWalk

/-- Append consecutive increasing axis walks, retaining their original interval occurrences. -/
def append : {first middle last : Fraction.Rational} →
  IncreasingWalk intervals first middle →
    IncreasingWalk intervals middle last → IncreasingWalk intervals
      first last
  | _, _, _, .nil _, last => last
  | _, _, _, .cons interval member tail, last => .cons interval member (tail.append last)

end AxisWalks.IncreasingWalk

namespace AxisChainCoherence.IncreasingWalk

/-- Increasing walks with equal endpoint coordinates and edge lists are heterogeneously equal. -/
private theorem heq_of_edges : {first last : Fraction.Rational} → (a : AxisWalks.IncreasingWalk intervals
  first last) →
    {otherFirst otherLast : Fraction.Rational} → (b : AxisWalks.IncreasingWalk intervals otherFirst
      otherLast) →
    first = otherFirst → last = otherLast → a.edges = b.edges → HEq a b
  | _, _, .nil _, _, _, .nil _, firstEq, _, _ => by cases firstEq; rfl
  | _, _, .nil _, _, _, .cons _ _ _, _, _, same => by
    simp only [AxisWalks.IncreasingWalk.edges] at same; cases same
  | _, _, .cons _ _ _, _, _, .nil _, _, _, same => by
    simp only [AxisWalks.IncreasingWalk.edges] at same; cases same
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
theorem eq_of_edges {first last : Fraction.Rational} (a b : AxisWalks.IncreasingWalk intervals first last)
    (same : a.edges = b.edges) : a = b := eq_of_heq (heq_of_edges a b
      rfl rfl same)

end AxisChainCoherence.IncreasingWalk

namespace AxisChainCoherence.IncreasingWalk

/-- A separated interval bank has a unique increasing walk between fixed endpoints.

Both walks select the same bounded sublist of the original interval bank. -/
theorem unique (separated : intervals.Pairwise Interval.Before) {first last : Fraction.Rational}
    (a b : AxisWalks.IncreasingWalk intervals first last) : a = b :=
  eq_of_edges a b
    ((WindowAxes.IncreasingWalk.edges_eq_filter separated a).trans
    (WindowAxes.IncreasingWalk.edges_eq_filter separated b).symm)

end AxisChainCoherence.IncreasingWalk

end IncreasingWalk

section Grid

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}

namespace AxisChainCoherence.Walk

/-- Lifting consecutive horizontal axis walks commutes with appending them. -/
theorem horizontalIncreasing_append (line : HorizontalLine polynomial ambient) (member : line ∈
  grid.horizontal) :
    {first middle last : Fraction.Rational} → (a : AxisWalks.IncreasingWalk grid.xIntervals first middle)
      →
    (b : AxisWalks.IncreasingWalk grid.xIntervals middle last) →
    Walks.Walk.horizontalIncreasing line member (a.append b) =
      (Walks.Walk.horizontalIncreasing line member a).append
      (Walks.Walk.horizontalIncreasing line member b)
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons interval adjacent tail, b =>
      congrArg (Walks.Walk.cons (.horizontal interval adjacent line member))
        (horizontalIncreasing_append line member tail b)

/-- Lifting consecutive vertical axis walks commutes with appending them. -/
theorem verticalIncreasing_append (line : VerticalLine polynomial ambient) (member : line ∈
  grid.vertical) :
    {first middle last : Fraction.Rational} → (a : AxisWalks.IncreasingWalk grid.yIntervals first middle)
      →
    (b : AxisWalks.IncreasingWalk grid.yIntervals middle last) →
    Walks.Walk.verticalIncreasing line member (a.append b) = (Walks.Walk.verticalIncreasing
      line member a).append (Walks.Walk.verticalIncreasing line member b)
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons interval adjacent tail, b =>
      congrArg (Walks.Walk.cons (.vertical interval adjacent line member))
        (verticalIncreasing_append line member tail b)

/-- Transporting the endpoints of an appended walk agrees with transporting its two parts. -/
theorem castEndpoints_append {first middle last a b c : Gaussian.Basic.Canonical} (left : Walks.Walk grid
  first middle) (right : Walks.Walk grid middle last)
    (firstEq : first = a) (middleEq : middle = b) (lastEq : last = c) :
    (left.append right).castEndpoints firstEq lastEq =
      (left.castEndpoints firstEq middleEq).append (right.castEndpoints middleEq lastEq) := by
  cases firstEq
  cases middleEq
  cases lastEq
  rfl

/-- Endpoint transport commutes with walk reversal, exchanging the endpoint equalities. -/
theorem castEndpoints_reverse {first last a b : Gaussian.Basic.Canonical} (walk : Walks.Walk grid first
  last)
    (firstEq : first = a) (lastEq : last = b) :
    (walk.castEndpoints firstEq lastEq).reverse = walk.reverse.castEndpoints lastEq firstEq := by
  cases firstEq
  cases lastEq
  rfl

end AxisChainCoherence.Walk

namespace AxisChainCoherence.WindowCircuits

open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits (horizontal vertical side)

/-- The vertical lift of an empty axis walk is stationary. -/
theorem vertical_nil_eq {x y : Fraction.Rational}
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical x) :
    vertical line (.nil y) = Walks.Walk.nil
      (Components.Basic.point x y) := by
  rcases line with ⟨entry, member, rfl⟩
  rfl

/-- The vertical lift of a retained axis step prepends its actual band-side edge. -/
theorem vertical_cons_eq {x finish : Fraction.Rational}
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical x)
    (band : Interval (HorizontalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (member : band ∈ grid.yIntervals) (tail : AxisWalks.IncreasingWalk grid.yIntervals
      band.upper.coordinate finish) :
    vertical line (.cons band member tail) = .cons
      (side band member line)
      (vertical line tail) := by
  rcases line with ⟨entry, member, rfl⟩
  rfl

/-- Joining increasing horizontal axes joins their original retained horizontal window walks. -/
theorem horizontal_append {first middle last y : Fraction.Rational}
    (a : AxisWalks.IncreasingWalk grid.xIntervals first middle) (b :
      AxisWalks.IncreasingWalk grid.xIntervals middle last)
    (line : Lookup (key := HorizontalLine.coordinate) grid.horizontal y)
      :
    horizontal (a.append b) line =
      (horizontal a line).append
      (horizontal b line) := by
  rcases line with ⟨entry, member, rfl⟩
  exact AxisChainCoherence.Walk.horizontalIncreasing_append entry member a b

/-- Joining increasing vertical axes joins their original retained vertical window walks. -/
theorem vertical_append {first middle last x : Fraction.Rational}
    (a : AxisWalks.IncreasingWalk grid.yIntervals first middle) (b :
      AxisWalks.IncreasingWalk grid.yIntervals middle last)
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical x) :
    vertical line (a.append b) =
      (vertical line a).append
      (vertical line b) := by
  rcases line with ⟨entry, member, rfl⟩
  exact AxisChainCoherence.Walk.verticalIncreasing_append entry member a b

end AxisChainCoherence.WindowCircuits

namespace AxisChainCoherence

/-- The searched horizontal grid walk equals the retained increasing axis lift between the same endpoints. -/
theorem horizontalWalk_increasing {first last y : Fraction.Rational}
    (axis : AxisWalks.IncreasingWalk grid.xIntervals first last)
    (line : Lookup (key := HorizontalLine.coordinate) grid.horizontal y)
    (firstMember : first ∈ grid.vertical.map VerticalLine.coordinate)
    (lastMember : last ∈ grid.vertical.map VerticalLine.coordinate)
    (lineMember : y ∈ grid.horizontal.map HorizontalLine.coordinate) :
    Walks.horizontalWalk grid first last y firstMember lastMember lineMember =
      WindowCircuitOrder.WindowCircuits.horizontal axis line := by
  simp only [Walks.horizontalWalk, AxisWalks.walk, dif_pos axis.ordered,
    Walks.Walk.horizontalAxis]
  exact congrArg₂ (fun path fixed => WindowCircuitOrder.WindowCircuits.horizontal path fixed)
    (IncreasingWalk.unique (Interval.adjacent_pairwise
      grid.vertical grid.vertical_ordered)
      (AxisWalks.increasing first last grid.vertical grid.vertical_ordered firstMember lastMember
        axis.ordered) axis)
    (WindowCircuitOrder.WindowCircuits.lookup_unique grid.horizontal_ordered
      (AxisWalks.lookup y grid.horizontal lineMember) line)

end AxisChainCoherence

namespace AxisChainCoherence

/-- The searched vertical grid walk equals the retained increasing axis lift between the same endpoints. -/
theorem verticalWalk_increasing {first last x : Fraction.Rational}
    (axis : AxisWalks.IncreasingWalk grid.yIntervals first last)
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical x)
    (lineMember : x ∈ grid.vertical.map VerticalLine.coordinate)
    (firstMember : first ∈ grid.horizontal.map HorizontalLine.coordinate)
    (lastMember : last ∈ grid.horizontal.map HorizontalLine.coordinate) :
    Walks.verticalWalk grid x first last lineMember firstMember lastMember =
      WindowCircuitOrder.WindowCircuits.vertical line axis := by
  simp only [Walks.verticalWalk, AxisWalks.walk, dif_pos axis.ordered,
    Walks.Walk.verticalAxis]
  exact congrArg₂ (fun fixed path => WindowCircuitOrder.WindowCircuits.vertical fixed path)
    (WindowCircuitOrder.WindowCircuits.lookup_unique grid.vertical_ordered (AxisWalks.lookup
      x grid.vertical lineMember) line)
    (IncreasingWalk.unique (Interval.adjacent_pairwise
      grid.horizontal grid.horizontal_ordered)
      (AxisWalks.increasing first last grid.horizontal grid.horizontal_ordered firstMember lastMember
        axis.ordered) axis)

end AxisChainCoherence

namespace AxisChainCoherence

/-- The searched horizontal grid walk in the opposite direction equals the reversal of the retained increasing axis
lift. -/
theorem horizontalWalk_decreasing {first last y : Fraction.Rational}
    (axis : AxisWalks.IncreasingWalk grid.xIntervals first last)
    (line : Lookup (key := HorizontalLine.coordinate) grid.horizontal y)
    (firstMember : first ∈ grid.vertical.map VerticalLine.coordinate)
    (lastMember : last ∈ grid.vertical.map VerticalLine.coordinate)
    (lineMember : y ∈ grid.horizontal.map HorizontalLine.coordinate) :
    Walks.horizontalWalk grid last first y lastMember firstMember lineMember =
      (WindowCircuitOrder.WindowCircuits.horizontal axis line).reverse := by
  by_cases ordered : last ≤ first
  · have equal := le_antisymm axis.ordered ordered
    subst last
    rw [horizontalWalk_increasing axis line,
      IncreasingWalk.unique
      (Interval.adjacent_pairwise grid.vertical grid.vertical_ordered) axis (.nil first)]
    rcases line with ⟨entry, member, rfl⟩
    rfl
  · simp only [Walks.horizontalWalk, AxisWalks.walk, dif_neg ordered,
      Walks.Walk.horizontalAxis]
    have actual := congrArg₂ (fun path fixed => (WindowCircuitOrder.WindowCircuits.horizontal path
      fixed).reverse)
      (IncreasingWalk.unique (Interval.adjacent_pairwise
        grid.vertical grid.vertical_ordered)
        (AxisWalks.increasing first last grid.vertical grid.vertical_ordered firstMember lastMember
          (le_of_not_ge ordered)) axis)
      (WindowCircuitOrder.WindowCircuits.lookup_unique grid.horizontal_ordered
        (AxisWalks.lookup y grid.horizontal lineMember) line)
    exact (Walk.castEndpoints_reverse _ _ _).symm.trans actual

end AxisChainCoherence

namespace AxisChainCoherence

/-- The searched vertical grid walk in the opposite direction equals the reversal of the retained increasing axis lift.
-/
theorem verticalWalk_decreasing {first last x : Fraction.Rational}
    (axis : AxisWalks.IncreasingWalk grid.yIntervals first last)
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical x)
    (lineMember : x ∈ grid.vertical.map VerticalLine.coordinate)
    (firstMember : first ∈ grid.horizontal.map HorizontalLine.coordinate)
    (lastMember : last ∈ grid.horizontal.map HorizontalLine.coordinate) :
    Walks.verticalWalk grid x last first lineMember lastMember firstMember =
      (WindowCircuitOrder.WindowCircuits.vertical line axis).reverse := by
  by_cases ordered : last ≤ first
  · have equal := le_antisymm axis.ordered ordered
    subst last
    rw [verticalWalk_increasing axis line,
      IncreasingWalk.unique
      (Interval.adjacent_pairwise grid.horizontal grid.horizontal_ordered) axis (.nil first)]
    rcases line with ⟨entry, member, rfl⟩
    rfl
  · simp only [Walks.verticalWalk, AxisWalks.walk, dif_neg ordered,
      Walks.Walk.verticalAxis]
    have actual := congrArg₂ (fun fixed path => (WindowCircuitOrder.WindowCircuits.vertical fixed
      path).reverse)
      (WindowCircuitOrder.WindowCircuits.lookup_unique grid.vertical_ordered
        (AxisWalks.lookup x grid.vertical lineMember) line)
      (IncreasingWalk.unique (Interval.adjacent_pairwise
        grid.horizontal grid.horizontal_ordered)
        (AxisWalks.increasing first last grid.horizontal grid.horizontal_ordered firstMember lastMember
          (le_of_not_ge ordered)) axis)
    exact (Walk.castEndpoints_reverse _ _ _).symm.trans actual

end AxisChainCoherence

namespace AxisChainCoherence.RootEdgeBank.ChainComparison

variable {frames : RootFrames grid} {vertices :
  LiftedVertices.VertexBank grid} {edges :
  RootEdgeBank frames}

section ChainComparison

/-- Reverse a lifted chain comparison while preserving both sheet targets and reversed indexed words. -/
theorem reverse_anchored {anchor : Gaussian.Basic.Canonical} (reference : WindingOneLoop polynomial anchor)
    (anchorMember : FromStates.ContainsVertex grid anchor)
    {first last : Gaussian.Basic.Canonical} {a b : Walks.Walk grid first last} (same :
      RootEdgeBank.ChainComparison edges vertices a b) :
    RootEdgeBank.ChainComparison edges vertices a.reverse b.reverse
      := by
  have targets (sheet : Fin 2) : EdgeBank.RootEdgeBank.target edges a.reverse sheet =
    EdgeBank.RootEdgeBank.target edges b.reverse sheet := by
    apply EdgeBank.RootEdgeBank.target_injective_anchored edges reference anchorMember b
    rw [← same.targets,
      EdgeBank.RootEdgeBank.target_reverse_right_anchored edges reference anchorMember,
      EdgeBank.RootEdgeBank.target_reverse_right_anchored edges reference anchorMember]
  refine ⟨targets, ?_⟩
  intro sheet
  have first := edges.indexedEdges_reverse_anchored vertices reference anchorMember a
    (EdgeBank.RootEdgeBank.target edges a.reverse sheet)
  have last := edges.indexedEdges_reverse_anchored vertices reference anchorMember b
    (EdgeBank.RootEdgeBank.target edges b.reverse sheet)
  rw [EdgeBank.RootEdgeBank.target_reverse_right_anchored edges reference anchorMember] at first last
  rw [first, last, targets]
  exact (same.words _).reverse

/-- Reverse a lifted chain comparison while preserving both sheet targets and reversed indexed words. -/
theorem reverse (reference : ∀ point, FromStates.ContainsVertex grid point →
  WindingOneLoop polynomial point)
    {first last : Gaussian.Basic.Canonical} {a b : Walks.Walk grid first last} (same :
      RootEdgeBank.ChainComparison edges vertices a b) :
    RootEdgeBank.ChainComparison edges vertices a.reverse b.reverse
      := by
  cases a with
  | nil =>
      cases b with
      | nil => exact RootEdgeBank.ChainComparison.refl _
      | cons edge tail =>
          exact reverse_anchored (reference _ edge.vertices.1) edge.vertices.1 same
  | cons edge tail =>
      exact reverse_anchored (reference _ edge.vertices.1) edge.vertices.1 same

/-- Double reversal agrees with the original walk on the retained lifted edge bank. -/
theorem reverse_reverse_anchored {anchor : Gaussian.Basic.Canonical} (reference : WindingOneLoop polynomial anchor)
    (anchorMember : FromStates.ContainsVertex grid anchor)
    {first last : Gaussian.Basic.Canonical} (walk : Walks.Walk grid first last) :
    RootEdgeBank.ChainComparison edges vertices walk.reverse.reverse
      walk where
  targets := fun sheet => by
    apply EdgeBank.RootEdgeBank.target_injective_anchored edges reference anchorMember walk.reverse
    exact (EdgeBank.RootEdgeBank.target_reverse_right_anchored edges reference anchorMember walk.reverse sheet).trans
      (EdgeBank.RootEdgeBank.target_reverse_anchored edges reference anchorMember walk sheet).symm
  words := fun sheet => by
    have reversed := edges.indexedEdges_reverse_anchored vertices reference anchorMember walk.reverse
      (EdgeBank.RootEdgeBank.target edges walk sheet)
    rw [EdgeBank.RootEdgeBank.target_reverse_anchored edges reference anchorMember] at reversed
    rw [reversed, edges.indexedEdges_reverse_anchored vertices reference anchorMember]
    exact Topology.Mesh.RetracingWords.Retracing.of_eq
      (Topology.Mesh.RetracingWords.CutPath.reverse_reverse _)

/-- Double reversal agrees with the original walk on the retained lifted edge bank. -/
theorem reverse_reverse (reference : ∀ point, FromStates.ContainsVertex grid point →
  WindingOneLoop polynomial point)
    {first last : Gaussian.Basic.Canonical} (walk : Walks.Walk grid first last) :
    RootEdgeBank.ChainComparison edges vertices walk.reverse.reverse
      walk := by
  cases walk with
  | nil => exact RootEdgeBank.ChainComparison.refl _
  | cons edge tail =>
      exact reverse_reverse_anchored (reference _ edge.vertices.1) edge.vertices.1 (.cons edge tail)

/-- Transporting endpoint identities preserves the lifted chain comparison. -/
theorem castEndpoints
    {first last a b : Gaussian.Basic.Canonical} {left right : Walks.Walk grid first last} (same :
      RootEdgeBank.ChainComparison edges vertices left right)
    (firstEq : first = a) (lastEq : last = b) :
    RootEdgeBank.ChainComparison edges vertices (left.castEndpoints
      firstEq lastEq) (right.castEndpoints firstEq lastEq) := by
  cases firstEq
  cases lastEq
  exact same

/-- Replacing a connector by a compared connector preserves the based loop's lifted chain comparison.

The comparison uses the forward connector, original loop and reversed connector on their actual arriving sheets. -/
theorem based_stem (reference : ∀ point, FromStates.ContainsVertex grid point →
  WindingOneLoop polynomial point)
    {first last : Gaussian.Basic.Canonical} {a b : Walks.Walk grid first last} (same :
      RootEdgeBank.ChainComparison edges vertices a b)
    (loop : Walks.Walk grid last last) :
      RootEdgeBank.ChainComparison edges vertices (a.based loop)
      (b.based loop) :=
  same.append ((RootEdgeBank.ChainComparison.refl loop).append
    (reverse reference same))

end ChainComparison
end AxisChainCoherence.RootEdgeBank.ChainComparison

section Window

variable {box : Box}

namespace WindowBoundary.Window

/-- Follow the retained left side and then the top side from the southwest to northeast corner. -/
def northEast (window :
  Window grid box) : Walks.Walk grid (Components.Basic.point
  box.xLower box.yLower) (Components.Basic.point box.xUpper box.yUpper) :=
  (window.vertical window.left).append (window.horizontal window.top)

end WindowBoundary.Window

namespace AxisChainCoherence.Window

/-- The reversed opposite connector is exactly the positive left/top route
on the lifted edge bank, including independently prepared monotone spines. -/
theorem reverse_connect_comparison_anchored {frames : RootFrames grid} {vertices :
  LiftedVertices.VertexBank grid} {edges :
  RootEdgeBank frames}
    (window : WindowBoundary.Window grid box)
    {anchor : Gaussian.Basic.Canonical} (reference : WindingOneLoop polynomial anchor)
    (anchorMember : FromStates.ContainsVertex grid anchor)
    (first : FromStates.ContainsVertex grid (Components.Basic.point box.xLower box.yLower))
    (last : FromStates.ContainsVertex grid (Components.Basic.point box.xUpper box.yUpper)) :
    RootEdgeBank.ChainComparison edges vertices
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid.connect grid _ _ last first).reverse
      window.northEast := by
  change RootEdgeBank.ChainComparison edges vertices
    ((Walks.horizontalWalk grid box.xUpper box.xLower box.yUpper last.1 first.1 last.2).append
      (Walks.verticalWalk grid box.xLower box.yUpper box.yLower first.1 last.2 first.2)).reverse _
  rw [horizontalWalk_decreasing window.x window.top,
    verticalWalk_decreasing window.y window.left,
    Walks.Walk.reverse_append]
  exact (RootEdgeBank.ChainComparison.reverse_reverse_anchored reference anchorMember _).append
    (RootEdgeBank.ChainComparison.reverse_reverse_anchored reference anchorMember _)

/-- The reversed opposite connector is exactly the positive left/top route
on the lifted edge bank, including independently prepared monotone spines. -/
theorem reverse_connect_comparison {frames : RootFrames grid} {vertices :
  LiftedVertices.VertexBank grid} {edges :
  RootEdgeBank frames}
    (window : WindowBoundary.Window grid box)
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      WindingOneLoop polynomial point)
    (first : FromStates.ContainsVertex grid (Components.Basic.point box.xLower box.yLower))
    (last : FromStates.ContainsVertex grid (Components.Basic.point box.xUpper box.yUpper)) :
    RootEdgeBank.ChainComparison edges vertices
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid.connect grid _ _ last first).reverse
      window.northEast :=
  reverse_connect_comparison_anchored window (reference _ first) first first last

end AxisChainCoherence.Window

end Window
end Grid
end Purelib.Polynomial.Geometry.Grid
