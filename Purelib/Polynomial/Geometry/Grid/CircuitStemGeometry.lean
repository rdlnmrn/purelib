module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk Lookup)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell HorizontalLine Interval VerticalLine)
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder (CellCircuits)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank (ChainComparison)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

@[expose] public section

/-!
# Every retained cell connector follows the left-then-top route

The finite expression carries a proof for each original stem. Horizontal
prefixes extend its displayed x-axis; vertical prefixes extend its y-axis.
This identifies the actual window expression with the canonical reversed
connectors used by the common-root branch programs.
-/

namespace Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {vertices :
    VertexBank grid} {edges :
    RootEdgeBank frames}

namespace RowCircuitOrder.CellCircuits

/-- Certificates comparing each retained row-circuit connector with its increasing horizontal route.

Every cell keeps its original membership, axis witness and lifted chain comparison on the given edge bank. -/
inductive HorizontalStems (edges :
  RootEdgeBank frames) (vertices :
  VertexBank grid)
    (band : Interval (HorizontalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (member : band ∈ grid.yIntervals) {start : Fraction.Rational} : CellCircuits grid
      (Gaussian.Components.Basic.point start band.lower.coordinate) → Prop
  /-- The empty circuit tree has no connector obligations. -/ | nil : HorizontalStems edges vertices band member (.nil
    _)
  /-- The retained cell connector agrees with the displayed increasing horizontal axis route. -/ | cell (interval :
    Interval (VerticalLine.coordinate (polynomial := polynomial)
    (ambient := ambient)))
      (cellMember : Cell.mk interval band ∈ grid.cells)
      (stem : Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point start band.lower.coordinate)
        (Gaussian.Components.Basic.point interval.lower.coordinate band.lower.coordinate))
      (axis : IncreasingWalk grid.xIntervals start interval.lower.coordinate)
      (same : ChainComparison edges vertices stem
        (Geometry.Grid.RowCircuitOrder.RowCircuits.bottom band member axis)) :
      HorizontalStems edges vertices band member (.cell (Cell.mk interval band) cellMember stem)
  /-- Both retained subtrees have certified horizontal connectors. -/ | append {first last :
    CellCircuits grid (Gaussian.Components.Basic.point start band.lower.coordinate)}
      (firstStems : HorizontalStems edges vertices band member first) (lastStems : HorizontalStems edges vertices band
        member last) :
      HorizontalStems edges vertices band member (.append first last)

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.CellCircuits (HorizontalStems)

namespace HorizontalStems

variable {band : Interval (HorizontalLine.coordinate (polynomial :=
  polynomial) (ambient := ambient))}
  {member : band ∈ grid.yIntervals}

/-- Prepend an original horizontal grid edge to every certified connector in the circuit tree. -/
theorem prepend (interval :
  Interval (VerticalLine.coordinate (polynomial := polynomial) (ambient
  := ambient)))
    (adjacent : interval ∈ grid.xIntervals)
    {tree : CellCircuits grid (Gaussian.Components.Basic.point interval.upper.coordinate
      band.lower.coordinate)}
    (stems : HorizontalStems edges vertices band member tree) :
    HorizontalStems edges vertices band member
      (tree.based (.cons (.horizontal interval adjacent band.lower (Interval.endpoints_mem _
        grid.horizontal_ordered member).1) (.nil _))) := by
  induction stems with
  | nil => exact .nil
  | cell target targetMember stem axis same =>
      exact .cell target targetMember _ (.cons interval adjacent axis)
        ((ChainComparison.refl (.cons (.horizontal
          interval adjacent band.lower
          (Interval.endpoints_mem _ grid.horizontal_ordered member).1) (.nil _))).append same)
  | append first last ihFirst ihLast => exact .append ihFirst ihLast

end HorizontalStems

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits in
/-- Both axis witnesses are finite parts of the original grid. Their
comparison preserves all lifted values, not only coordinate endpoints. -/
inductive AscendingStems (edges :
  RootEdgeBank frames) (vertices :
  VertexBank grid) {base : Gaussian.Basic.Canonical} :
    CellCircuits grid base → Prop
  /-- The empty circuit tree has no ascending connector obligations. -/ | nil : AscendingStems edges vertices (.nil
    base)
  /-- The retained connector agrees with its original vertical-then-horizontal axis walks. -/ | cell (cell :
    Geometry.Grid.ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) (stem : Geometry.Grid.Walks.Walk grid
    base cell.box.anchor)
      (x : IncreasingWalk grid.xIntervals base.re cell.box.xLower)
      (y : IncreasingWalk grid.yIntervals base.im cell.box.yLower)
      (left : Lookup (key := VerticalLine.coordinate) grid.vertical
        base.re)
      (top : Lookup (key := HorizontalLine.coordinate) grid.horizontal
        cell.box.yLower)
      (same : ChainComparison edges vertices stem
        ((Geometry.Grid.WindowCircuitOrder.WindowCircuits.vertical left y).append
        (Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal x top))) :
      AscendingStems edges vertices (.cell cell member stem)
  /-- Both retained subtrees have certified ascending connectors. -/ | append {first last :
    CellCircuits grid base} (firstStems : AscendingStems edges vertices first)
      (lastStems : AscendingStems edges vertices last) : AscendingStems edges vertices (.append first last)

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.CellCircuits (AscendingStems)

namespace HorizontalStems

/-- View horizontal row connectors as left-then-top routes with stationary vertical parts. -/
theorem ascending
    {band : Interval (HorizontalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient))}
    {member : band ∈ grid.yIntervals} {start : Fraction.Rational}
    {tree : CellCircuits grid (Gaussian.Components.Basic.point start
      band.lower.coordinate)}
    (stems : HorizontalStems edges vertices band member tree)
    (left : Lookup (key := VerticalLine.coordinate) grid.vertical start)
      : AscendingStems edges vertices tree := by
  induction stems with
  | nil => exact .nil
  | cell interval cellMember stem axis same =>
      apply Geometry.Grid.RowCircuitOrder.CellCircuits.AscendingStems.cell (Cell.mk interval
        band) cellMember stem axis (.nil band.lower.coordinate) left
        ⟨band.lower, (Interval.endpoints_mem _ grid.horizontal_ordered member).1, rfl⟩
      exact same.trans (ChainComparison.of_eq (congrArg
        (fun prefixPath => prefixPath.append (Geometry.Grid.RowCircuitOrder.RowCircuits.bottom band member axis))
        (AxisChainCoherence.WindowCircuits.vertical_nil_eq (y := band.lower.coordinate) left)).symm)
  | append first last ihFirst ihLast => exact .append ihFirst ihLast

end HorizontalStems

namespace AscendingStems

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits in
/-- Prepend a retained vertical band edge to every certified ascending connector. -/
theorem prepend_vertical
    (band : Interval (HorizontalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (member : band ∈ grid.yIntervals) {left : Fraction.Rational}
    (line : Lookup (key := VerticalLine.coordinate) grid.vertical left)
    {tree : CellCircuits grid (Gaussian.Components.Basic.point left
      band.upper.coordinate)}
    (stems : AscendingStems edges vertices tree) :
    AscendingStems edges vertices (tree.based (.cons
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.side band member line) (.nil _))) := by
  induction stems with
  | nil => exact .nil
  | cell cell cellMember stem x y actual top same =>
      apply Geometry.Grid.RowCircuitOrder.CellCircuits.AscendingStems.cell (base := Gaussian.Components.Basic.point left
        band.lower.coordinate) cell cellMember _ x (.cons band member y) actual top
      have compared := (ChainComparison.refl (edges :=
        edges) (vertices := vertices)
        (.cons (Geometry.Grid.WindowCircuitOrder.WindowCircuits.side band member line) (.nil _))).append same
      apply compared.trans (ChainComparison.of_eq ?_)
      rw [Geometry.Grid.WindowCircuitOrder.WindowCircuits.lookup_unique grid.vertical_ordered line actual]
      exact (congrArg (fun prefixPath => prefixPath.append (Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal x
        top))
        (AxisChainCoherence.WindowCircuits.vertical_cons_eq actual band member y)).symm
  | append first last ihFirst ihLast => exact .append ihFirst ihLast

end AscendingStems

/-- Replace each cell connector by the reversed canonical grid connector to the common base.

The circuit tree retains its original cells, membership witnesses and append order. -/
def canonicalize {base : Gaussian.Basic.Canonical}
  (first : FromStates.ContainsVertex grid base) : CellCircuits grid
  base → CellCircuits grid base
  | .nil _ => .nil base
  | .cell face member _ => .cell face member (Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid.connect grid
    face.box.anchor base (face.anchor_mem member) first).reverse
  | .append initial final => .append (canonicalize first initial) (canonicalize first final)
termination_by structural tree => tree

namespace AscendingStems

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits in
/-- Canonicalizing certified ascending connectors preserves the lifted circuit product.

The comparison retains arriving sheets and finite indexed-edge word relations for the original edge bank. -/
theorem canonicalize_comparison
  {base : Gaussian.Basic.Canonical} {tree : CellCircuits grid base}
    (stems : AscendingStems edges vertices tree)
    (reference : ∀ point, FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    (first : FromStates.ContainsVertex grid base) :
      ChainComparison edges vertices tree.product
      (tree.canonicalize first).product := by
  induction stems with
  | nil => exact ChainComparison.refl _
  | cell cell member stem x y left top same =>
      let box : Box := ⟨base.re, cell.box.xLower, base.im, cell.box.yLower, x.ordered, y.ordered⟩
      let window : WindowBoundary.Window grid box :=
        ⟨x, y, left, Geometry.Grid.AxisWalks.lookup _ grid.vertical (cell.anchor_mem member).1,
          Geometry.Grid.AxisWalks.lookup _ grid.horizontal first.2, top,
          grid.cells.filter (fun cell => decide (cell.box.Refines box)), rfl⟩
      have canonical := AxisChainCoherence.Window.reverse_connect_comparison window (edges := edges)
        (vertices := vertices)
        reference first (cell.anchor_mem member)
      exact AxisChainCoherence.RootEdgeBank.ChainComparison.based_stem
        reference (same.trans canonical.symm) (Geometry.Grid.CellBoundary.Cell.boundaryWalk cell member)
  | append initial final ihInitial ihFinal => exact ihInitial.append ihFinal

end AscendingStems

end RowCircuitOrder.CellCircuits

namespace RowCircuitOrder.RowCircuits

variable (band : Interval (HorizontalLine.coordinate (polynomial :=
  polynomial) (ambient := ambient)))
  (member : band ∈ grid.yIntervals)

/-- The constructed row circuit tree has certified increasing horizontal connectors. -/
theorem horizontal_stems : {start finish :
  Fraction.Rational} → (walk : IncreasingWalk grid.xIntervals start finish) →
    Geometry.Grid.RowCircuitOrder.CellCircuits.HorizontalStems edges vertices band member (ofWalk band member walk)
  | _, _, .nil _ => .nil
  | _, _, .cons interval adjacent tail => by
      refine .append (Geometry.Grid.RowCircuitOrder.CellCircuits.HorizontalStems.prepend interval adjacent
        (horizontal_stems tail)) ?_
      exact .cell interval _ (.nil _) (.nil _)
        (ChainComparison.refl _)

end RowCircuitOrder.RowCircuits

namespace WindowCircuitOrder.WindowCircuits

variable {left right : Fraction.Rational} (x : IncreasingWalk grid.xIntervals left right)
  (line : Lookup (key := VerticalLine.coordinate) grid.vertical left)

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits in
/-- The constructed window circuit tree has certified left-then-top connectors. -/
theorem ascending_stems : {bottom top :
  Fraction.Rational} → (y : IncreasingWalk grid.yIntervals bottom top) →
    Geometry.Grid.RowCircuitOrder.CellCircuits.AscendingStems edges vertices (ofWalk x line y)
  | _, _, .nil _ => .nil
  | _, _, .cons band member tail =>
      .append (Geometry.Grid.RowCircuitOrder.CellCircuits.HorizontalStems.ascending
        (Geometry.Grid.RowCircuitOrder.RowCircuits.horizontal_stems band member x) line)
        (Geometry.Grid.RowCircuitOrder.CellCircuits.AscendingStems.prepend_vertical
          band member line (ascending_stems tail))

end WindowCircuitOrder.WindowCircuits

namespace WindowBoundary.Window

/-- Every connector in the retained window circuit tree has an ascending axis-route certificate. -/
theorem ascending_stems {box : Box}
  (window : Window grid box) :
    Geometry.Grid.RowCircuitOrder.CellCircuits.AscendingStems edges vertices window.circuits :=
  Geometry.Grid.WindowCircuitOrder.WindowCircuits.ascending_stems window.x window.left window.y

end WindowBoundary.Window

end Purelib.Polynomial.Geometry.Grid

namespace Purelib.Polynomial.Geometry.Grid.CircuitStemGeometry.CircuitPartition

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {faces : Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid}
  {edges : RootEdgeBank frames} {base : Gaussian.Basic.Canonical}

/-- The retained part of a circuit partition inherits the original ascending connector certificates. -/
theorem kept_stems {tree : CellCircuits bank.grid base} (partition :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition faces tree)
    (stems : Geometry.Grid.RowCircuitOrder.CellCircuits.AscendingStems edges vertices tree) :
    Geometry.Grid.RowCircuitOrder.CellCircuits.AscendingStems edges vertices partition.kept := by
  induction partition with
  | nil => exact .nil
  | regular => exact .nil
  | hole => exact stems
  | append first last ihFirst ihLast =>
      cases stems with
      | append firstStems lastStems => exact .append (ihFirst firstStems) (ihLast lastStems)

end Purelib.Polynomial.Geometry.Grid.CircuitStemGeometry.CircuitPartition
