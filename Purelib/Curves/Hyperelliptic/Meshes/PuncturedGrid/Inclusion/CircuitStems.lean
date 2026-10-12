module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
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
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Connectors
public import Purelib.Polynomial.Geometry.Grid.CircuitStemGeometry
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Reverse

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.AxisChainCoherence

open Purelib.Polynomial.Geometry.Grid.AxisChainCoherence.RootEdgeBank

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Polynomial.Geometry.Grid.Walks

open Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.Riemann.Paths

open Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Connectors

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

@[expose] public section

/-! The original ordered connectors canonicalize on the new root bank.
The old finite axis witnesses are reused; no old/new sheet identification
or replacement branch order is assumed. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid

open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval Cell HorizontalLine VerticalLine)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk Lookup)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.Walks (Edge)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder (CellCircuits)
open _root_.Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)
open _root_.Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
open _root_.Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}
  {original grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} (included :
    CoordinateInclusion original grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
    RootEdgeBank frames) (vertices :
    VertexBank grid)

namespace CellCircuits

/-- The original row circuit stems retain their horizontal axis comparisons after grid subdivision.

Each cell occurrence carries its original interval, stem and finite axis witness together with a chain comparison on the
new root bank. -/
inductive ResplitHorizontalStems
    (band : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
    (member : band ∈ original.yIntervals) {start : Fraction.Rational} : RowCircuitOrder.CellCircuits original
      (Components.Basic.point start band.lower.coordinate) → Prop
  /-- The empty original circuit tree has no stem-comparison obligations. -/ | nil :
    ResplitHorizontalStems
    band member (.nil _)
  /-- Retain the original cell and stem with its finite axis witnesses and actual resplit chain comparison. -/ | cell
    (interval : ClearGrid.Interval (VerticalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
      (cellMember : ClearGrid.Cell.mk interval band ∈ original.cells)
      (stem : Walks.Walk original (Components.Basic.point start band.lower.coordinate) (Components.Basic.point
        interval.lower.coordinate band.lower.coordinate))
      (axis : AxisWalks.IncreasingWalk original.xIntervals start interval.lower.coordinate)
      (same : RootEdgeBank.ChainComparison edges vertices (included.resplit stem ((ClearGrid.Cell.mk interval
        band).anchor_mem cellMember))
        (included.resplit (RowCircuits.bottom band member axis) ((ClearGrid.Cell.mk interval band).anchor_mem
          cellMember))) :
      ResplitHorizontalStems
        band member (.cell (ClearGrid.Cell.mk interval band) cellMember stem)
  /-- Combine the retained stem comparisons of the two original circuit subtrees. -/ | append {first last :
    RowCircuitOrder.CellCircuits original (Components.Basic.point start band.lower.coordinate)}
      (firstStems :
        ResplitHorizontalStems
        band member first) (lastStems :
        ResplitHorizontalStems
        band member last) :
      ResplitHorizontalStems
        band member (.append first last)

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits in
/-- The original circuit stems retain vertical-then-horizontal axis comparisons after subdivision.

The construction preserves the original cell occurrences and both finite axis witnesses while comparing their actual
subdivided walks. -/
inductive ResplitAscendingStems {base : Data.Gaussian.Basic.Canonical} : RowCircuitOrder.CellCircuits original base →
  Prop
  /-- The empty original circuit tree has no stem-comparison obligations. -/ | nil :
    ResplitAscendingStems
    (.nil base)
  /-- Retain the original cell and stem with its finite axis witnesses and actual resplit chain comparison. -/ | cell
    (cell : ClearGrid.Cell polynomial ambient) (member : cell ∈ original.cells) (stem : Walks.Walk original base
    cell.box.anchor)
      (x : AxisWalks.IncreasingWalk original.xIntervals base.re cell.box.xLower)
      (y : AxisWalks.IncreasingWalk original.yIntervals base.im cell.box.yLower)
      (left : AxisWalks.Lookup (key := VerticalLine.coordinate) original.vertical base.re)
      (top : AxisWalks.Lookup (key := HorizontalLine.coordinate) original.horizontal cell.box.yLower)
      (same : RootEdgeBank.ChainComparison edges vertices (included.resplit stem (cell.anchor_mem member))
        (included.resplit ((WindowCircuits.vertical left y).append (WindowCircuits.horizontal x top)) (cell.anchor_mem
          member))) :
      ResplitAscendingStems
        (.cell cell member stem)
  /-- Combine the retained stem comparisons of the two original circuit subtrees. -/ | append {first last :
    RowCircuitOrder.CellCircuits original base}
      (firstStems :
        ResplitAscendingStems
        first) (lastStems :
        ResplitAscendingStems
        last) :
      ResplitAscendingStems
        (.append first last)

variable {included edges vertices}

/-- Prepending the original horizontal interval preserves every retained resplit row-stem comparison. -/
theorem ResplitHorizontalStems.prepend
    {band : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := polynomial) (ambient := ambient))}
    {member : band ∈ original.yIntervals}
    (interval : ClearGrid.Interval (VerticalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
    (adjacent : interval ∈ original.xIntervals)
    {tree : RowCircuitOrder.CellCircuits original (Components.Basic.point interval.upper.coordinate
      band.lower.coordinate)}
    (stems : ResplitHorizontalStems
      included edges vertices band member tree) :
    ResplitHorizontalStems included
      edges vertices band member
      (tree.based (.cons (.horizontal interval adjacent band.lower (Interval.endpoints_mem _ original.horizontal_ordered
        member).1) (.nil _))) := by
  induction stems with
  | nil => exact .nil
  | cell target targetMember stem axis same =>
      apply
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid.CellCircuits.ResplitHorizontalStems.cell
        target targetMember _ (.cons interval adjacent axis)
      let edge := Edge.horizontal interval adjacent band.lower (Interval.endpoints_mem _ original.horizontal_ordered
        member).1
      have compared := (ChainComparison.refl (edges := edges) (vertices := vertices)
        (included.resplit (.cons edge (.nil _)) edge.vertices.2)).append same
      erw [← included.resplit_append _ _ edge.vertices.2 ((ClearGrid.Cell.mk target band).anchor_mem targetMember),
        ← included.resplit_append _ _ edge.vertices.2 ((ClearGrid.Cell.mk target band).anchor_mem targetMember)]
          at compared
      exact compared
  | append first last ihFirst ihLast => exact .append ihFirst ihLast

/-- A retained horizontal row-stem comparison yields an ascending comparison using the same original vertical lookup. -/
theorem ResplitHorizontalStems.ascending
    {band : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := polynomial) (ambient := ambient))}
    {member : band ∈ original.yIntervals} {start : Fraction.Rational}
    {tree : RowCircuitOrder.CellCircuits original (Components.Basic.point start band.lower.coordinate)}
    (stems : ResplitHorizontalStems
      included edges vertices band member tree)
    (left : AxisWalks.Lookup (key := VerticalLine.coordinate) original.vertical start) :
    ResplitAscendingStems included
      edges vertices tree := by
  induction stems with
  | nil => exact .nil
  | cell interval cellMember stem axis same =>
      apply
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid.CellCircuits.ResplitAscendingStems.cell
        (ClearGrid.Cell.mk interval band) cellMember stem axis (.nil band.lower.coordinate) left
        ⟨band.lower, (Interval.endpoints_mem _ original.horizontal_ordered member).1, rfl⟩
      erw [Polynomial.Geometry.Grid.AxisChainCoherence.WindowCircuits.vertical_nil_eq, Walk.append]
      exact same
  | append first last ihFirst ihLast => exact .append ihFirst ihLast

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits
/-- Prepending the original vertical side preserves all retained ascending stem comparisons. -/
theorem ResplitAscendingStems.prepend_vertical
    (band : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
    (member : band ∈ original.yIntervals) {left : Fraction.Rational}
    (line : AxisWalks.Lookup (key := VerticalLine.coordinate) original.vertical left)
    {tree : RowCircuitOrder.CellCircuits original (Components.Basic.point left band.upper.coordinate)}
    (stems : ResplitAscendingStems
      included edges vertices tree) :
    ResplitAscendingStems included
      edges vertices (tree.based (.cons (WindowCircuits.side band member line) (.nil _))) := by
  induction stems with
  | nil => exact .nil
  | cell cell cellMember stem x y actual top same =>
      apply
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid.CellCircuits.ResplitAscendingStems.cell
        (base := Components.Basic.point left band.lower.coordinate) cell cellMember _ x (.cons band member y) actual top
      let edge := WindowCircuits.side band member line
      have compared := (ChainComparison.refl (edges := edges) (vertices := vertices)
        (included.resplit (.cons edge (.nil _)) edge.vertices.2)).append same
      rw [← included.resplit_append _ _ edge.vertices.2 (cell.anchor_mem cellMember),
        ← included.resplit_append _ _ edge.vertices.2 (cell.anchor_mem cellMember)] at compared
      refine compared.trans (ChainComparison.of_eq ?_)
      apply congrArg (fun walk => included.resplit walk (cell.anchor_mem cellMember))
      dsimp only [edge]
      rw [WindowCircuits.lookup_unique original.vertical_ordered line actual]
      exact (congrArg (fun initialWalk => initialWalk.append (WindowCircuits.horizontal x top))
        (Polynomial.Geometry.Grid.AxisChainCoherence.WindowCircuits.vertical_cons_eq actual band member y)).symm
  | append first last ihFirst ihLast => exact .append ihFirst ihLast

/-- A circuit with retained ascending stem comparisons has the same subdivided chain as its original canonicalization.
-/
theorem ResplitAscendingStems.canonicalize_comparison {base : Data.Gaussian.Basic.Canonical} {tree :
  RowCircuitOrder.CellCircuits original base}
    (stems : ResplitAscendingStems
      included edges vertices tree)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop polynomial point)
    (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex original base) :
    RootEdgeBank.ChainComparison edges vertices (included.resplit tree.product first)
      (included.resplit (tree.canonicalize first).product first) := by
  induction stems with
  | nil => exact ChainComparison.refl _
  | cell cell member stem x y left top same =>
      let box : Rational.Box := ⟨base.re, cell.box.xLower, base.im, cell.box.yLower, x.ordered,
        y.ordered⟩
      let window : Window original box :=
        ⟨x, y, left, AxisWalks.lookup _ original.vertical (cell.anchor_mem member).1,
          AxisWalks.lookup _ original.horizontal first.2, top,
          original.cells.filter (fun cell => decide (cell.box.Refines box)), rfl⟩
      have canonical := Window.resplit_reverse_connect_comparison
        included edges vertices reference window first (cell.anchor_mem member)
      have based := Polynomial.Geometry.Grid.AxisChainCoherence.RootEdgeBank.ChainComparison.based_stem
        reference (same.trans canonical.symm) (included.resplit (CellBoundary.Cell.boundaryWalk cell member)
          (cell.anchor_mem member))
      exact (included.resplit_based edges vertices reference stem (CellBoundary.Cell.boundaryWalk cell member) first
        (cell.anchor_mem member)).trans
        (based.trans (included.resplit_based edges vertices reference
          (Grid.connect original _ _ (cell.anchor_mem member) first).reverse (CellBoundary.Cell.boundaryWalk cell
            member) first (cell.anchor_mem member)).symm)
  | @append firstTree lastTree initial final ihInitial ihFinal =>
      change RootEdgeBank.ChainComparison edges vertices (included.resplit (firstTree.product.append lastTree.product)
        first)
        (included.resplit ((firstTree.canonicalize first).product.append (lastTree.canonicalize first).product) first)
      rw [included.resplit_append _ _ first first, included.resplit_append _ _ first first]
      exact ihInitial.append ihFinal

end CellCircuits

/-- The original ordered row-circuit compiler retains horizontal stem comparisons after subdivision. -/
theorem RowCircuits.resplit_horizontal_stems
    (band : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
    (member : band ∈ original.yIntervals) :
    {start finish : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk original.xIntervals start finish) →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid.CellCircuits.ResplitHorizontalStems included
      edges vertices band member (RowCircuits.ofWalk band member walk)
  | _, _, .nil _ => .nil
  | _, _, .cons interval adjacent tail =>
      .append ((resplit_horizontal_stems band member tail).prepend interval adjacent)
        (.cell interval _ (.nil _) (.nil _) (ChainComparison.refl _))

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.RowCircuits in
/-- The original ordered window compiler retains ascending stem comparisons after subdivision. -/
theorem WindowCircuits.resplit_ascending_stems {left right : Fraction.Rational}
    (x : AxisWalks.IncreasingWalk original.xIntervals left right)
    (line : AxisWalks.Lookup (key := VerticalLine.coordinate) original.vertical left) :
    {bottom top : Fraction.Rational} → (y : AxisWalks.IncreasingWalk original.yIntervals bottom top) →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid.CellCircuits.ResplitAscendingStems included
      edges vertices (WindowCircuits.ofWalk x line y)
  | _, _, .nil _ => .nil
  | _, _, .cons band member tail =>
      .append
        ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid.RowCircuits.resplit_horizontal_stems
        included edges vertices band member x).ascending line)
        ((resplit_ascending_stems x line tail).prepend_vertical band member line)

/-- The original ordered window compiler retains ascending stem comparisons after subdivision. -/
theorem Window.resplit_ascending_stems {box : Rational.Box} (window : Window original box) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid.CellCircuits.ResplitAscendingStems included
      edges vertices window.circuits :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid.WindowCircuits.resplit_ascending_stems included
    edges vertices window.x window.left window.y

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.CircuitPartition

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {grid :
    Polynomial.Geometry.Grid.ClearGrid curve.polynomial (Ambient
    curve)}
  {included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion bank.grid grid}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid} {base : Purelib.Data.Gaussian.Basic.Canonical}

/-- Selecting the retained branch circuits preserves their original ascending stem comparisons. -/
theorem resplit_kept_stems {tree : RowCircuitOrder.CellCircuits bank.grid base} (partition :
  BranchCellBank.CircuitPartition faces tree)
    (stems : Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid.CellCircuits.ResplitAscendingStems
      included edges vertices tree) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.Grid.CellCircuits.ResplitAscendingStems included
      edges vertices partition.kept := by
  induction partition with
  | nil => exact .nil
  | regular => exact .nil
  | hole => exact stems
  | append first last ihFirst ihLast =>
      cases stems with
      | append firstStems lastStems => exact .append (ihFirst firstStems) (ihLast lastStems)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitStems.CircuitPartition
