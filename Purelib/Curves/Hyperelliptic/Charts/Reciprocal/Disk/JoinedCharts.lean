module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Mathlib.Tactic.Ring.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

/-!
# Chart replacements for the complete retained joined parent

The original order, entry corrections and final corrections are retained.
Each block has exactly the same total, so all inter-block area terms agree.
Only the explicitly cached internal area differences remain to be summed.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count index depth readingIndex floor minimum pairFloor : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {collar :
    Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {target tolerance : Normalization.InverseRootPolynomial.Coordinate}

/-- Replace each original corrected cell by its complete retained chart path and exact entry/exit corrections in order.
-/
@[expose] def replacementPaths : {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} → {bank :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} → {owners :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} → (plans :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests) →
    (cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) →
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells →
    (pairs : Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners) →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests.EvaluationData (readingIndex := readingIndex)
      pairs cells → Normalization.InverseRootPolynomial.Gaussian → List (List
      Normalization.InverseRootPolynomial.Gaussian)
  | _, _, _, _, .nil, .nil, _, .nil, _, _ => []
  | _, _, _, _, .cons _ tail, .cons cell cells, evaluated, .cons _ rest, readings, previous =>
      let old := Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell.build cell readings.1
        (readings.1.firstValue - previous)
      let restored := Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells.Restored.build evaluated.1
      (old.first :: ((restored.first :: (evaluated.1.vertices.path.chartPath ++ [restored.last])) ++ [old.last])) ::
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.replacementPaths tail cells evaluated.2 rest
          readings.2 readings.1.lastValue

set_option genInjectivity false in
/-- The original joined parent and its retained chart replacement with unchanged total and per-cell area errors. -/
structure Replacement {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {bank :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} {owners :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank}
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} (plans :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests)
    (cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) (evaluated :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells)
    (pairs : Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners)
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests.EvaluationData (readingIndex :=
      readingIndex) pairs cells) (previous : Normalization.InverseRootPolynomial.Gaussian) where
  /-- The retained ordered list of complete corrected chart paths. -/ paths : List (List
    Normalization.InverseRootPolynomial.Gaussian)
  /-- The retained paths are exactly the original recursive chart replacements. -/ paths_eq : paths =
    Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.replacementPaths plans cells evaluated pairs readings previous
  /-- The finite summary of the exact original corrected parent paths. -/ original : Path.IncrementArea.Summary
    ((JoinedCells.correctedPairs pairs cells readings previous).map
    Prod.fst).flatten
  /-- The finite summary of the exact retained chart replacement paths. -/ summary : Path.IncrementArea.Summary
    paths.flatten
  /-- The retained replacement and original summaries have exactly the same total. -/ total_eq : summary.total =
    original.total
  /-- The retained ordered list of original per-cell area differences. -/ errors : List
    Normalization.InverseRootPolynomial.Gaussian
  /-- The number of retained area errors equals the original parent edge count. -/ length_eq : errors.length =
    edges.length
  /-- The full area difference is exactly the finite Gaussian sum of the retained local errors. -/ area_eq :
    summary.area - original.area = Data.Gaussian.Norm.Sum.Basic.gaussianSum errors
  /-- Every retained local area error satisfies the original paid cell bound. -/ bounded : ∀ error ∈ errors,
    Data.Gaussian.Norm.Basic.normSq error ≤ 2 * (target + target / 4)

constructive_injectivity Replacement

namespace Replacement

/-- Recursively combine the original corrected cells and cached chart replacements, preserving totals and every local
area error. -/
@[expose] def build : {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} → {bank :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} → {owners :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} → (plans :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests) →
    (cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) → (evaluated :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells) →
    (pairs : Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners) →
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests.EvaluationData (readingIndex :=
      readingIndex) pairs cells) → (previous : Normalization.InverseRootPolynomial.Gaussian) →
    Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.Replacement plans cells evaluated pairs readings previous
  | _, _, _, _, .nil, .nil, _, .nil, _, _ =>
      ⟨[], rfl, Path.IncrementArea.Summary.build [], Path.IncrementArea.Summary.build [], rfl, [], rfl, by
        change 0 - 0 = (0 : Normalization.InverseRootPolynomial.Gaussian);
        ring1,
        fun _ member => False.elim (List.not_mem_nil member)⟩
  | _, _, _, _, .cons _ tail, .cons cell cells, evaluated, .cons _ rest, readings, previous => by
      let old := Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell.build cell readings.1
        (readings.1.firstValue - previous)
      let restored := Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells.Restored.build evaluated.1
      let head := restored.correct old
      let tail := Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.Replacement.build tail cells
        evaluated.2 rest readings.2 readings.1.lastValue
      let path := old.first :: ((restored.first :: (evaluated.1.vertices.path.chartPath ++ [restored.last])) ++
        [old.last])
      refine ⟨path :: tail.paths, ?_, old.summary.append tail.original, head.summary.append tail.summary,
        ?_, (head.summary.area - old.summary.area) :: tail.errors, congrArg Nat.succ tail.length_eq, ?_, ?_⟩
      · change path :: tail.paths = path :: _
        rw [tail.paths_eq]
      · change head.summary.total + tail.summary.total = old.summary.total + tail.original.total
        rw [head.total_eq, tail.total_eq]
      · change head.summary.area + tail.summary.area + Path.BoundaryRibbon.area head.summary.total tail.summary.total -
          (old.summary.area + tail.original.area + Path.BoundaryRibbon.area old.summary.total tail.original.total) =
            (head.summary.area - old.summary.area) + Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.errors
        rw [head.total_eq, tail.total_eq, ← tail.area_eq]
        ring1
      · intro error member
        rcases Data.List.Membership.mem_cons.mp member with same | member
        · subst error
          rw [show head.summary.area - old.summary.area = -(old.summary.area - head.summary.area) by ring1,
            Gaussian.Norm.Basic.normSq_neg]
          exact head.area_error.le
        · exact tail.bounded error member

variable {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {bank :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} {owners :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank}
  {requests : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} {plans :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests}
  {cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank} {evaluated :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells}
  {pairs : Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners}
  {readings : Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests.EvaluationData (readingIndex :=
    readingIndex) pairs cells} {previous : Normalization.InverseRootPolynomial.Gaussian} {bound :
    Normalization.InverseRootPolynomial.Coordinate}

/-- The retained original summary total equals the total of the actual joined parent. -/
theorem original_total (replacement : Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.Replacement plans cells
  evaluated pairs readings previous)
    (joined : JoinedCells pairs cells readings previous bound) :
      replacement.original.total = joined.summary.total := by
  rw [replacement.original.total_eq, joined.summary.total_eq, joined.pairs_eq]

/-- The retained original summary area equals the area of the actual joined parent. -/
theorem original_area (replacement : Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.Replacement plans cells evaluated
  pairs readings previous)
    (joined : JoinedCells pairs cells readings previous bound) :
      replacement.original.area = joined.summary.area := by
  rw [replacement.original.area_eq, joined.summary.area_eq, joined.pairs_eq]

/-- The full retained chart replacement preserves the exact original joined-parent total. -/
theorem total_preserved (replacement : Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.Replacement plans cells
  evaluated pairs readings previous)
    (joined : JoinedCells pairs cells readings previous bound) :
      replacement.summary.total = joined.summary.total :=
  replacement.total_eq.trans (replacement.original_total joined)

/-- The full chart-replacement area error is bounded by the original edge count squared times the retained per-cell
bound. -/
theorem area_error (replacement : Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.Replacement plans cells evaluated
  pairs readings previous)
    (joined : JoinedCells pairs cells readings previous bound) :
    Data.Gaussian.Norm.Basic.normSq (replacement.summary.area - joined.summary.area) ≤ (edges.length :
      Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (2 * (target + target / 4)) := by
  rw [← replacement.original_area joined, replacement.area_eq]
  have estimate := Gaussian.Norm.Sum.Bounds.normSq_sum_le replacement.errors _ replacement.bounded
  rw [replacement.length_eq] at estimate
  exact estimate.trans_eq (by ring1)

end Replacement
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts
