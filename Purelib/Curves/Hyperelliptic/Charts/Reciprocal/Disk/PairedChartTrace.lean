module
import Purelib.Algebra.NatCast
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAdjacency
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedBlockComparison
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedClosedBoundary
public import Purelib.Integration.Path.JoinedTraceIncrements
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Actual retained chart traces, including every joining edge. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace

open Purelib
open Purelib.Algebra
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path.JoinedTrace
open Purelib.Integration.Path.JoinedTraceIncrements
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank (ChartRequest junctionLeft junctionRight)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries (BoundaryBankRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure (leftParent rightParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary (BoundaryRequest chartInsertionScale
  chartInsertionScale_nonnegative joinedBlockScale)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add)

/-- Concatenate the complete original trace family with every joining edge, using a single zero vertex for an empty
family. -/
@[expose] def familyTrace {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint) :
  JoinedTrace.VertexTrace PrimitivePoint :=
  match n, traces with
  | 0, _ => ⟨PrimitivePoint.zero, []⟩
  | _ + 1, traces => VertexTrace.concatenate traces

/-- A nonempty original trace family begins at its actual first trace's initial vertex. -/
private theorem familyTrace_first {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint) (positive :
  0 < n) :
    (familyTrace traces).first = (traces ⟨0,
      positive⟩).first := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ n => exact VertexTrace.glue_first _ _

/-- A nonempty original trace family ends at its actual last trace's final vertex. -/
private theorem familyTrace_last {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint) (positive :
  0 < n) :
    (familyTrace traces).last = (traces ⟨n - 1, by
      omega0⟩).last := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ n => exact VertexTrace.concatenate_last traces

/-- The complete retained family area is the sum of original trace areas and every actual intervening joining edge. -/
private theorem familyTrace_area {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint) :
    (familyTrace traces).area id = FiniteSum.Fin.sumFin
      (fun i => (traces i).area id) +
      FiniteSum.Fin.sumFin (fun i : Fin (n - 1) => Stokes.edgeArea (traces ⟨i.val, by omega0⟩).last
        (traces ⟨i.val + 1, by omega0⟩).first) := by
  cases n with
  | zero => change (0 : Data.Gaussian.Basic.Canonical) = 0 + 0; ring1
  | succ n =>
      rw [familyTrace, VertexTrace.concatenate_area,
        VertexTrace.joiningArea_ofFn]
      rfl

/-- The original trace-increment blocks paired with themselves, interleaved with the actual connector insertions. -/
private def insertionPairs : {n : Nat} → (Fin (n + 1) → JoinedTrace.VertexTrace Stokes.PrimitivePoint) →
    List (List Stokes.PrimitivePoint × List Stokes.PrimitivePoint)
  | 0, traces => [((VertexTrace.increments (traces 0) id), (VertexTrace.increments (traces 0) id))]
  | _ + 1, traces => ((VertexTrace.increments (traces 0) id), (VertexTrace.increments (traces 0) id)) ::
      ([], [(traces 1).first.sub (traces 0).last]) ::
        insertionPairs (fun i => traces i.succ)

/-- The first block projection flattens to exactly the original trace increment lists. -/
private theorem insertionPairs_left {n : Nat} (traces : Fin (n + 1) → JoinedTrace.VertexTrace Stokes.PrimitivePoint) :
    ((insertionPairs traces).map Prod.fst).flatten =
      (List.ofFn (fun i => (VertexTrace.increments (traces i) id))).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [OfFn.Basic.ofFn_succ, List.flatten_cons,
        insertionPairs, List.map_cons, List.map_cons,
        List.flatten_cons, List.flatten_cons, List.nil_append, ih]

/-- The second block projection flattens to the actual concatenated trace increments including every connector. -/
private theorem insertionPairs_right {n : Nat} (traces : Fin (n + 1) → JoinedTrace.VertexTrace Stokes.PrimitivePoint) :
    ((insertionPairs traces).map Prod.snd).flatten =
      (VertexTrace.increments (Purelib.Integration.Path.JoinedTrace.VertexTrace.concatenate traces) id) := by
  induction n with
  | zero => exact Data.List.Append.append_nil _
  | succ n ih =>
      rw [insertionPairs, List.map_cons, List.map_cons,
        List.flatten_cons, List.flatten_cons, ih]
      unfold VertexTrace.concatenate
      rw [OfFn.Basic.ofFn_succ, VertexTrace.glue, VertexTrace.join_increments, VertexTrace.glue_first]
      rfl

/-- The retained insertion comparison has two blocks per junction plus one original trace block. -/
private theorem insertionPairs_length {n : Nat} (traces : Fin (n + 1) → JoinedTrace.VertexTrace Stokes.PrimitivePoint) :
    (insertionPairs traces).length = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (insertionPairs (fun i => traces
        i.succ)).length + 1 + 1 = _
      rw [ih]
      omega0

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

/-- Original trace-total and junction-gap bounds supply all area, total-error and magnitude certificates for the
retained insertion blocks. -/
private theorem insertionPairs_valid {n : Nat} (traces : Fin (n + 1) → JoinedTrace.VertexTrace Stokes.PrimitivePoint)
    {error magnitude : InverseRootPolynomial.Coordinate} (errorNonnegative : 0 ≤ error) (magnitudeNonnegative : 0 ≤
      magnitude)
    (small : error ≤ magnitude)
    (totals : ∀ i, (PrimitivePoint.Bounded (PairedIncrementArea.total ((VertexTrace.increments (traces i) id))))
      magnitude)
    (gaps : ∀ i : Fin n, (PrimitivePoint.Bounded ((traces i.succ).first.sub (traces i.castSucc).last)) error) :
    ∀ pair ∈ insertionPairs traces,
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area pair.1 - PairedIncrementArea.area pair.2) ≤ 0 ∧
      (PrimitivePoint.Bounded ((PairedIncrementArea.total pair.1).sub (PairedIncrementArea.total pair.2))) error ∧
      (PrimitivePoint.Bounded (PairedIncrementArea.total pair.1)) magnitude ∧
      (PrimitivePoint.Bounded (PairedIncrementArea.total pair.2)) magnitude := by
  have diagonal (values : List Stokes.PrimitivePoint) (bounded : (PrimitivePoint.Bounded (PairedIncrementArea.total
    values)) magnitude) :
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area values - PairedIncrementArea.area values) ≤ 0 ∧
      (PrimitivePoint.Bounded ((PairedIncrementArea.total values).sub (PairedIncrementArea.total values))) error ∧
      (PrimitivePoint.Bounded (PairedIncrementArea.total values)) magnitude ∧ (PrimitivePoint.Bounded
        (PairedIncrementArea.total values)) magnitude := by
    refine ⟨?_, ?_, bounded, bounded⟩
    · rw [sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    · constructor <;> change Data.Gaussian.Basic.Canonical.normSq (_ - _) ≤ error <;>
        rw [sub_self, Data.Gaussian.Basic.Canonical.normSq_zero] <;> exact errorNonnegative
  have connector (gap : Stokes.PrimitivePoint) (bounded : (PrimitivePoint.Bounded gap) error) :
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area [] - PairedIncrementArea.area [gap]) ≤ 0 ∧
      (PrimitivePoint.Bounded ((PairedIncrementArea.total []).sub (PairedIncrementArea.total [gap]))) error ∧
      (PrimitivePoint.Bounded (PairedIncrementArea.total [])) magnitude ∧ (PrimitivePoint.Bounded
        (PairedIncrementArea.total [gap])) magnitude := by
    have total : PairedIncrementArea.total [gap] = gap := by
      apply congrArg₂ PrimitivePoint.mk <;> change _ + 0 = _ <;> exact add_zero _
    have area : PairedIncrementArea.area [gap] = 0 := by
      change Stokes.edgeArea gap PrimitivePoint.zero + 0 = 0
      unfold Stokes.edgeArea PrimitivePoint.zero
      ring1
    rw [total, area]
    refine ⟨?_, ?_, ?_, bounded.1.trans small, bounded.2.trans small⟩
    · change Data.Gaussian.Norm.Basic.normSq (0 - 0) ≤ 0
      rw [sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    · constructor
      · change Data.Gaussian.Basic.Canonical.normSq (0 - gap.left) ≤ error
        rw [zero_sub, Data.Gaussian.Basic.Canonical.normSq_neg]
        exact bounded.1
      · change Data.Gaussian.Basic.Canonical.normSq (0 - gap.right) ≤ error
        rw [zero_sub, Data.Gaussian.Basic.Canonical.normSq_neg]
        exact bounded.2
    · exact ⟨Data.Gaussian.Basic.Canonical.normSq_zero.trans_le magnitudeNonnegative,
        Data.Gaussian.Basic.Canonical.normSq_zero.trans_le magnitudeNonnegative⟩
  induction n with
  | zero =>
      intro pair member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact diagonal _ (totals 0)
      · cases member
  | succ n ih =>
      intro pair member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact diagonal _ (totals 0)
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact connector _ (gaps 0)
      · exact ih (fun i => traces i.succ) (fun i => totals i.succ) (fun i => gaps i.succ) pair member

/-- Inserting all actual joining edges changes the complete original increment area by the retained fourth-power count
error bound. -/
theorem concatenate_area_insertion
    {n : Nat} (traces : Fin (n + 1) → JoinedTrace.VertexTrace Stokes.PrimitivePoint)
    {error magnitude : InverseRootPolynomial.Coordinate} (errorNonnegative : 0 ≤ error) (magnitudeNonnegative : 0 ≤
      magnitude)
    (small : error ≤ magnitude)
    (totals : ∀ i, (PrimitivePoint.Bounded (PairedIncrementArea.total ((VertexTrace.increments (traces i) id))))
      magnitude)
    (gaps : ∀ i : Fin n, (PrimitivePoint.Bounded ((traces i.succ).first.sub (traces i.castSucc).last)) error) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (List.ofFn (fun i => (VertexTrace.increments
      (traces i) id))).flatten -
      PairedIncrementArea.area ((VertexTrace.increments (VertexTrace.concatenate traces) id))) ≤
      32 * ((2 * n + 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * error * magnitude := by
  have valid := insertionPairs_valid traces
    errorNonnegative magnitudeNonnegative small totals gaps
  have bound := PairedBlockComparison.blocks_area_difference_bound
    (insertionPairs traces)
    errorNonnegative magnitudeNonnegative (fun pair member => (valid pair member).1)
    (fun pair member => (valid pair member).2.1) (fun pair member => (valid pair member).2.2.1)
    (fun pair member => (valid pair member).2.2.2)
  rw [insertionPairs_left,
    insertionPairs_right,
    insertionPairs_length] at bound
  exact bound.trans_eq (by ring1)

/-- Each original insertion pair has its total discrepancy bounded by the retained connector error. -/
private theorem insertionPairs_total_valid {n : Nat} (traces : Fin (n + 1) → JoinedTrace.VertexTrace
  Stokes.PrimitivePoint)
    {error : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ error)
    (gaps : ∀ i : Fin n, (PrimitivePoint.Bounded ((traces i.succ).first.sub (traces i.castSucc).last)) error) :
    ∀ pair ∈ insertionPairs traces,
      (PrimitivePoint.Bounded ((PairedIncrementArea.total pair.1).sub (PairedIncrementArea.total pair.2))) error := by
  have diagonal (values : List Stokes.PrimitivePoint) :
      (PrimitivePoint.Bounded ((PairedIncrementArea.total values).sub (PairedIncrementArea.total values))) error := by
    constructor <;> change Data.Gaussian.Basic.Canonical.normSq (_ - _) ≤ error <;>
      rw [sub_self, Data.Gaussian.Basic.Canonical.normSq_zero] <;> exact nonnegative
  have connector (gap : Stokes.PrimitivePoint) (bounded : (PrimitivePoint.Bounded gap) error) :
      (PrimitivePoint.Bounded ((PairedIncrementArea.total []).sub (PairedIncrementArea.total [gap]))) error := by
    constructor
    · change Data.Gaussian.Basic.Canonical.normSq (0 - (gap.left + 0)) ≤ error
      rw [add_zero, zero_sub, Data.Gaussian.Basic.Canonical.normSq_neg]
      exact bounded.1
    · change Data.Gaussian.Basic.Canonical.normSq (0 - (gap.right + 0)) ≤ error
      rw [add_zero, zero_sub, Data.Gaussian.Basic.Canonical.normSq_neg]
      exact bounded.2
  induction n with
  | zero =>
      intro pair member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact diagonal _
      · cases member
  | succ n ih =>
      intro pair member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact diagonal _
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact connector _ (gaps 0)
      · exact ih (fun i => traces i.succ) (fun i => gaps i.succ) pair member

/-- Inserting the joining edges changes the total only by their increments. No bound on the parent totals is needed. -/
theorem concatenate_total_insertion
    {n : Nat} (traces : Fin (n + 1) → JoinedTrace.VertexTrace Stokes.PrimitivePoint)
    {error : InverseRootPolynomial.Coordinate} (errorNonnegative : 0 ≤ error)
    (gaps : ∀ i : Fin n, (PrimitivePoint.Bounded ((traces i.succ).first.sub (traces i.castSucc).last)) error) :
    (PrimitivePoint.Bounded ((PairedIncrementArea.total (List.ofFn (fun i => (VertexTrace.increments (traces i)
      id))).flatten).sub
      (PairedIncrementArea.total ((VertexTrace.increments (VertexTrace.concatenate traces) id)))))
      (((2 * n + 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * error) := by
  let pairs := (insertionPairs traces).map (fun pair =>
    (PairedIncrementArea.total pair.1, PairedIncrementArea.total pair.2))
  have valid := insertionPairs_total_valid traces
    errorNonnegative gaps
  have bounded : ∀ value ∈ pairs.map (fun pair => pair.1.sub pair.2), (PrimitivePoint.Bounded value) error := by
    intro value member
    obtain ⟨pointPair, inPairs, rfl⟩ := Map.mem_map.mp member
    change pointPair ∈ (insertionPairs traces).map (fun
      pair =>
      (PairedIncrementArea.total pair.1, PairedIncrementArea.total pair.2)) at inPairs
    obtain ⟨pair, inOriginal, rfl⟩ := Map.mem_map.mp inPairs
    exact valid pair inOriginal
  have bound := PairedIncrementArea.total_bound errorNonnegative bounded (count := 2 * n + 1)
    (by rw [Data.List.Map.length_map, Data.List.Map.length_map,
      insertionPairs_length])
  rw [PairedIncrementComparison.total_differences] at bound
  have left : pairs.map Prod.fst = ((insertionPairs
    traces).map Prod.fst).map PairedIncrementArea.total := by
    rw [Data.List.Map.map_map, Data.List.Map.map_map]; rfl
  have right : pairs.map Prod.snd = ((insertionPairs
    traces).map Prod.snd).map PairedIncrementArea.total := by
    rw [Data.List.Map.map_map, Data.List.Map.map_map]; rfl
  rw [left, right, ← PairedAreaBlocks.total_flatten, ← PairedAreaBlocks.total_flatten,
    insertionPairs_left,
      insertionPairs_right] at bound
  exact bound

/-- The complete original trace family satisfies both area and total insertion bounds, including the empty case. -/
private theorem family_insertion {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint)
    {error magnitude : InverseRootPolynomial.Coordinate}
    (errorNonnegative : 0 ≤ error) (magnitudeNonnegative : 0 ≤ magnitude) (small : error ≤ magnitude)
    (totals : ∀ i, (PrimitivePoint.Bounded (PairedIncrementArea.total ((VertexTrace.increments (traces i) id))))
      magnitude)
    (gaps : ∀ i : Fin (n - 1), (PrimitivePoint.Bounded ((traces ⟨i.val + 1, by omega0⟩).first.sub
      (traces ⟨i.val, by omega0⟩).last)) error) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (List.ofFn (fun i => (VertexTrace.increments
      (traces i) id))).flatten -
      PairedIncrementArea.area ((VertexTrace.increments
        (familyTrace traces) id))) ≤
      32 * ((2 * n - 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * error * magnitude ∧
    (PrimitivePoint.Bounded ((PairedIncrementArea.total (List.ofFn (fun i => (VertexTrace.increments (traces i)
      id))).flatten).sub
      (PairedIncrementArea.total ((VertexTrace.increments
        (familyTrace traces) id)))))
      (((2 * n - 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * error) := by
  cases n with
  | zero =>
      change Data.Gaussian.Norm.Basic.normSq (0 - 0) ≤ 32 * (0 : InverseRootPolynomial.Coordinate)^4 * error *
        magnitude ∧
        (PrimitivePoint.Bounded (PrimitivePoint.zero.sub PrimitivePoint.zero)) ((0 : InverseRootPolynomial.Coordinate)^2
          * error)
      constructor
      · rw [sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
        simp only [zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul, -eq_self, -iff_self]
        exact le_rfl
      · constructor <;> change Data.Gaussian.Norm.Basic.normSq (0 - 0) ≤ (0 :
          InverseRootPolynomial.Coordinate)^2 * error <;>
          rw [sub_self, Data.Gaussian.Norm.Basic.normSq_zero] <;>
          simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, -eq_self, -iff_self] <;> exact le_rfl
  | succ n =>
      rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega0]
      exact ⟨concatenate_area_insertion traces errorNonnegative magnitudeNonnegative small totals gaps,
        concatenate_total_insertion traces errorNonnegative
          gaps⟩

/-- The actual increments of a trace built from indexed values equal the original centered increment list. -/
private theorem ofIndexed_increments {n : Nat} (values : Fin (n + 1) → Stokes.PrimitivePoint) :
    (Purelib.Integration.Path.JoinedTraceIncrements.VertexTrace.increments
      (Purelib.Integration.Path.JoinedTrace.VertexTrace.ofIndexed values) id) = CenteredPathIncrements.increments values
      := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold VertexTrace.ofIndexed VertexTrace.increments
      rw [OfFn.Basic.ofFn_succ, VertexTrace.incrementsFrom,
        CenteredPathIncrements.increments, OfFn.Basic.ofFn_succ]
      exact congrArg (List.cons ((values 1).sub (values 0))) (ih (fun i => values i.succ))

/-- The complete actual trace increment total is its retained last vertex minus its first. -/
private theorem trace_increment_total (trace : JoinedTrace.VertexTrace Stokes.PrimitivePoint) :
    PairedIncrementArea.total ((VertexTrace.increments trace id)) = trace.last.sub trace.first := by
  have total := CenteredPathIncrements.increments_total (fun vertex => id (trace.indexed vertex))
  rw [(VertexTrace.indexed_increments trace id)] at total
  change PairedIncrementArea.total ((VertexTrace.increments trace id)) =
    (DyadicTrace.indexed trace.first trace.rest (Fin.last trace.rest.length)).sub trace.first at total
  rw [DyadicTrace.indexed_last] at total
  exact total

/-- The original trace area is its actual increment area plus the retained initial-point endpoint term. -/
private theorem trace_increment_area (trace : JoinedTrace.VertexTrace Stokes.PrimitivePoint) :
    trace.area id = PairedIncrementArea.area ((VertexTrace.increments trace id)) + Stokes.edgeArea trace.first
      (trace.last.sub trace.first) := by
  have traced := CenteredPathIncrements.increments_trace (fun vertex => id (trace.indexed vertex))
  rw [(VertexTrace.indexed_increments trace id), PairedIncrementArea.traceArea_eq,
    trace_increment_total] at traced
  exact (traced.trans (trace.indexed_area id)).symm

namespace Evaluation
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus count otherCount depth floor index : Nat} {curve : HyperellipticCurve
  genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {cover : Cover data} {otherCover :
    Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    CommonCover cover otherCover}
  {target : Coordinate} {request :
    ChartRequest regular common depth target floor}
  (evaluated : ChartRequest.Evaluation request
    index)

/-- The actual retained chart readings of one original common interval as an owned trace. -/
@[expose] def intervalTrace (i : Fin common.intervals.length) : JoinedTrace.VertexTrace PrimitivePoint :=
  VertexTrace.ofIndexed (fun vertex =>
    ((evaluated.entries.get i).evaluated.chart.retained.area.evaluated.readings.get vertex).chartPoint)

/-- The original interval trace begins at its retained first chart point. -/
theorem intervalTrace_first (i : Fin common.intervals.length) :
    ((intervalTrace evaluated) i).first =
      (Evaluation.firstChartPoint evaluated) i := rfl

/-- The original interval trace ends at its retained last chart point. -/
theorem intervalTrace_last (i : Fin common.intervals.length) :
    ((intervalTrace evaluated) i).last =
      (Evaluation.lastChartPoint evaluated) i := VertexTrace.ofIndexed_last _

/-- The actual interval trace area equals the original acquired chart area cache. -/
theorem intervalTrace_area (i : Fin common.intervals.length) :
    ((intervalTrace evaluated) i).area id =
      (evaluated.entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea :=
  (VertexTrace.ofIndexed_area _ id).trans
    (evaluated.entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea_eq.symm

/-- The actual interval trace increments equal the original retained chart block. -/
theorem intervalTrace_increments (i : Fin common.intervals.length) :
    (VertexTrace.increments ((intervalTrace
      evaluated) i) id) = (CommonChartBlockComparison.ChartBlock evaluated) i :=
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.ofIndexed_increments _).trans
    (CenteredPathIncrements.Sample.increments_raw (evaluated.entries.get
    i).evaluated.chart.retained.area.evaluated.chart).symm

/-- The complete actual chart trace formed from the original common-interval readings with every joining edge. -/
@[expose] def chartTrace : JoinedTrace.VertexTrace PrimitivePoint :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace
  (intervalTrace evaluated)

/-- The complete original common-interval trace begins at the actual first retained chart point. -/
theorem chartTrace_first : (chartTrace
  evaluated).first = (Evaluation.firstChartPoint evaluated) ⟨0, (CommonCover.nonempty common)⟩ :=
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace_first
    (intervalTrace evaluated)
    (CommonCover.nonempty common)).trans
    (intervalTrace_first evaluated _)

/-- The complete original common-interval trace ends at the actual last retained chart point. -/
theorem chartTrace_last : (chartTrace
  evaluated).last =
    (Evaluation.lastChartPoint evaluated) ⟨common.intervals.length - 1, by
      have := (CommonCover.nonempty common);
      omega0⟩ :=
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace_last
    (intervalTrace evaluated)
    (CommonCover.nonempty common)).trans
    (intervalTrace_last evaluated _)

/-- The complete original chart trace area is the cached interval area plus all actual retained common-interval
connectors. -/
theorem chartTrace_area : (chartTrace
  evaluated).area id = evaluated.chartArea +
    FiniteSum.Fin.sumFin (FanBankRequest.ConnectorArea (evaluated := evaluated)) := by
  rw [chartTrace,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace_area, evaluated.chartArea_eq]
  apply congrArg₂ (· + ·)
  · exact FiniteSum.Fin.sumFin_congr
      (intervalTrace_area evaluated)
  · exact FiniteSum.Fin.sumFin_congr (fun i => congrArg₂ Stokes.edgeArea
      (intervalTrace_last evaluated _)
        (intervalTrace_first evaluated _))

/-- The exact last-minus-first endpoint pair of the complete original common-interval chart trace. -/
@[expose] def chartTraceTotal : PrimitivePoint :=
  ((Evaluation.lastChartPoint evaluated) (CommonCover.lastIndex common)).sub ((Evaluation.firstChartPoint evaluated)
    (CommonCover.firstIndex common))

/-- The actual complete chart increment total equals the retained endpoint difference. -/
theorem chartTrace_total : PairedIncrementArea.total ((VertexTrace.increments
  (chartTrace evaluated) id)) =
  (chartTraceTotal evaluated) := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.trace_increment_total,
    chartTrace_first evaluated,
    chartTrace_last evaluated]
  rfl

/-- Read the cached interval areas and endpoint values; do not sum the fine increment path again merely to construct its
summary. -/
@[expose] def chartTraceSummary : PairedIncrementArea.Summary ((VertexTrace.increments
  (chartTrace evaluated) id)) :=
  let area := evaluated.chartArea + FiniteSum.Fin.sumFin (FanBankRequest.ConnectorArea (evaluated := evaluated)) -
    Stokes.edgeArea ((Evaluation.firstChartPoint evaluated) (CommonCover.firstIndex common))
      (chartTraceTotal evaluated)
  have areaEq : area = PairedIncrementArea.area ((VertexTrace.increments
    (chartTrace evaluated) id)) := by
    have traced := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.trace_increment_area
      (chartTrace evaluated)
    rw [chartTrace_area evaluated,
      chartTrace_first evaluated,
      chartTrace_last evaluated] at traced
    change _ = _ + Stokes.edgeArea ((Evaluation.firstChartPoint evaluated) (CommonCover.firstIndex common))
      (chartTraceTotal evaluated) at traced
    dsimp only [area, -eq_self, -iff_self]
    rw [traced]
    ring1
  ⟨(chartTraceTotal evaluated),
    (chartTrace_total evaluated).symm, area,
    areaEq⟩

/-- The original chart block cache and actual joined chart trace satisfy retained area and total insertion bounds. -/
theorem BlockBank.chartTrace_insertion (bank : (CommonChartBlockComparison.BlockBank evaluated)) (small :
  request.allowance ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (bank.chart.areaValue - PairedIncrementArea.area ((VertexTrace.increments
      (chartTrace evaluated) id))) ≤
      32 * ((2 * common.intervals.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * request.allowance *
        (2 * (data.sourceSlope + otherData.sourceSlope + 4)) ∧
    (PrimitivePoint.Bounded (bank.chart.totalValue.sub (PairedIncrementArea.total ((VertexTrace.increments
      (chartTrace evaluated) id)))))
      (((2 * common.intervals.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * request.allowance) := by
  have slopes := add_nonneg (UniformReciprocalModels.Data.sourceSlope_nonnegative data)
    (UniformReciprocalModels.Data.sourceSlope_nonnegative otherData)
  have larger : request.allowance ≤ 2 * (data.sourceSlope + otherData.sourceSlope + 4) := by
    have four : (4 : InverseRootPolynomial.Coordinate) ≤ data.sourceSlope + otherData.sourceSlope + 4 :=
      le_add_of_nonneg_left slopes
    have eight := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct four (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
    exact small.trans ((by decide +kernel : (1 : InverseRootPolynomial.Coordinate) ≤ 2 * 4).trans eight)
  have nonnegative : 0 ≤ 2 * (data.sourceSlope + otherData.sourceSlope + 4) := request.positive.le.trans larger
  have totals (i : Fin common.intervals.length) :
      (PrimitivePoint.Bounded (PairedIncrementArea.total ((VertexTrace.increments
        ((intervalTrace evaluated) i) id))))
        (2 * (data.sourceSlope + otherData.sourceSlope + 4)) := by
    rw [intervalTrace_increments evaluated, ←
      (bank.entries.get i).chart.total_eq]
    have prepared := (bank.entries.get i).magnitude_prepared evaluated
    exact ⟨(bank.entries.get i).chart_bounded.1.trans prepared, (bank.entries.get i).chart_bounded.2.trans prepared⟩
  have gaps (i : Fin (common.intervals.length - 1)) :
      (PrimitivePoint.Bounded (((intervalTrace
        evaluated) (CommonChartBank.junctionRight common i)).first.sub
        ((intervalTrace evaluated)
          (CommonChartBank.junctionLeft common i)).last)) request.allowance := by
    rw [intervalTrace_first evaluated,
      intervalTrace_last evaluated]
    exact Evaluation.junction_bounded evaluated i
  have bound := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.family_insertion
    (intervalTrace evaluated)
    request.positive.le nonnegative larger totals gaps
  have paths : List.ofFn (fun i => (VertexTrace.increments
    ((intervalTrace evaluated) i) id)) =
    (CommonChartBlockComparison.ChartBlocks evaluated) :=
    OfFn.Basic.ofFn_congr
      (intervalTrace_increments evaluated)
  rw [paths, ← bank.chart.area_eq, ← bank.chart.total_eq] at bound
  exact bound

open Purelib.Data.Rat.Fraction.Compatibility

/-- The retained positive common-interval allowance is at most the original complete target. -/
private theorem allowance_le_target : request.allowance ≤ target := by
  have count : (1 : InverseRootPolynomial.Coordinate) ≤ (common.intervals.length : InverseRootPolynomial.Coordinate) :=
    Fraction.Cast.Order.natCast_le_direct (CommonCover.nonempty common)
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
    count 2
  rw [show (1 : InverseRootPolynomial.Coordinate)^2 = 1 by decide] at square
  have smaller := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct square request.positive.le
  rw [Fraction.Field.one_mul] at smaller
  have paid : (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * request.allowance < target :=
    (by ring1 : (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * request.allowance =
      (common.intervals.length : InverseRootPolynomial.Coordinate) * ((common.intervals.length :
        InverseRootPolynomial.Coordinate) * request.allowance)).trans_lt request.paid
  exact smaller.trans paid.le

/-- The original cached source total and actual joined chart total satisfy the complete retained componentwise target
bound. -/
theorem BlockBank.joined_total_accurate (bank : (CommonChartBlockComparison.BlockBank evaluated)) (small : target ≤ 1) :
    (PrimitivePoint.Bounded (bank.source.totalValue.sub (PairedIncrementArea.total ((VertexTrace.increments
      (chartTrace evaluated) id))))) (16 *
      target) := by
  have inserted :=
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.BlockBank.chartTrace_insertion evaluated
    bank (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.allowance_le_target.trans small)).2
  have count := Fraction.Cast.Order.natCast_le_direct (Nat.sub_le (2 * common.intervals.length) 1)
  rw [Purelib.Algebra.NatCast.mul] at count
  change (((2 * common.intervals.length - 1 : Nat) : InverseRootPolynomial.Coordinate)) ≤ 2 * (common.intervals.length :
    InverseRootPolynomial.Coordinate) at count
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (2 *
    common.intervals.length - 1))) count 2
  have counted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct square request.positive.le
  have paid : ((2 * common.intervals.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * request.allowance < 4 *
    target := by
    exact counted.trans_lt ((by ring1 : (2 * (common.intervals.length : InverseRootPolynomial.Coordinate))^2 *
      request.allowance =
      4 * ((common.intervals.length : InverseRootPolynomial.Coordinate) * ((common.intervals.length :
        InverseRootPolynomial.Coordinate) * request.allowance))).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide) request.paid))
  have source := bank.total_accurate evaluated
  have leftSource := source.1
  have rightSource := source.2
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at leftSource rightSource
  have scalar (a b c : Data.Gaussian.Basic.Canonical) (first : Data.Gaussian.Basic.Canonical.normSq (a - b) < 4 *
    target)
      (last : Data.Gaussian.Basic.Canonical.normSq (b - c) < 4 * target) : Data.Gaussian.Basic.Canonical.normSq (a - c)
        ≤ 16 * target := by
    have via := Data.Gaussian.Norm.Bounds.normSq_sub_le_via a b c
    simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at via
    exact via.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct first.le last.le) (by decide)).trans_eq (by ring1))
  exact ⟨scalar bank.source.totalValue.left bank.chart.totalValue.left
      (PairedIncrementArea.total ((VertexTrace.increments
        (chartTrace evaluated) id))).left
      leftSource (inserted.1.trans_lt paid),
    scalar bank.source.totalValue.right bank.chart.totalValue.right
      (PairedIncrementArea.total ((VertexTrace.increments
        (chartTrace evaluated) id))).right
      rightSource (inserted.2.trans_lt paid)⟩

/-- The original cached source area and actual joined chart increment area satisfy the complete block-and-connector
comparison bound. -/
theorem BlockBank.joined_source_bound (bank : (CommonChartBlockComparison.BlockBank evaluated)) (small : target ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (bank.source.areaValue - PairedIncrementArea.area ((VertexTrace.increments
      (chartTrace evaluated) id))) ≤
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.joinedBlockScale common * target := by
  have localSmall : request.allowance ≤ 1 :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.allowance_le_target.trans small
  have inserted :=
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.BlockBank.chartTrace_insertion evaluated
    bank localSmall).1
  have insertion : Data.Gaussian.Norm.Basic.normSq (bank.chart.areaValue - PairedIncrementArea.area
    ((VertexTrace.increments (chartTrace
    evaluated) id))) ≤
      CommonRequestedBoundary.chartInsertionScale common * target := by
    have before : Data.Gaussian.Norm.Basic.normSq (bank.chart.areaValue - PairedIncrementArea.area
      ((VertexTrace.increments (chartTrace
      evaluated) id))) ≤
        CommonRequestedBoundary.chartInsertionScale common * request.allowance := inserted.trans_eq (by
            unfold CommonRequestedBoundary.chartInsertionScale;
            ring1)
    exact before.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      allowance_le_target
      (CommonRequestedBoundary.chartInsertionScale_nonnegative common))
  have source := bank.bounded.trans (bank.error_target evaluated)
  have via := Data.Gaussian.Norm.Bounds.normSq_sub_le_via bank.source.areaValue bank.chart.areaValue
    (PairedIncrementArea.area ((VertexTrace.increments
      (chartTrace evaluated) id)))
  exact via.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct source insertion) (by decide)).trans_eq
    (by unfold CommonRequestedBoundary.joinedBlockScale; ring1))

/-- The original requested boundary certificate pays the full source-versus-joined-chart increment area error. -/
theorem joined_source_accurate {requested : InverseRootPolynomial.Coordinate}
    (planned : CommonRequestedBoundary.BoundaryRequest regular common requested floor)
    (actual : planned.request.Evaluation index) (certificate : planned.Certificate actual)
    (small : planned.allowance ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (certificate.blocks.source.areaValue - PairedIncrementArea.area
      ((VertexTrace.increments (chartTrace
      actual) id))) < requested := by
  have before := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.BlockBank.joined_source_bound
    actual certificate.blocks small
  rw [← planned.blockScale_eq] at before
  have requestedPositive : 0 < requested := by
    have divided := planned.positive.trans_le (planned.allowance_eq.trans_le (Fraction.Order.Basic.min_le_left _ _))
    exact (Fraction.Order.Arithmetic.mul_pos_direct divided (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 32)).trans_eq
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel))
  have halfPositive := Fraction.Order.Field.div_pos_direct requestedPositive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
  have halfEq : requested / 2 + requested / 2 = requested :=
    (by ring1 : requested / 2 + requested / 2 = (requested / 2) * 2).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by
      decide))
  have halfLess := (Fraction.Field.zero_add _ ▸ Fraction.Order.Arithmetic.add_lt_add_right_direct halfPositive
    _).trans_eq halfEq
  exact before.trans_lt (((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (planned.allowance_eq.trans_le (Fraction.Order.Basic.min_le_right _ _)) planned.blockScale_nonnegative).trans
    (Weighted.mul_allowance_le halfPositive.le planned.blockScale_nonnegative)).trans_lt halfLess)

end Evaluation

namespace BoundaryBankRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {target requested : Coordinate} {minimum : Nat}
  {original : Request regular other parents
    target minimum} {request :
    BoundaryBankRequest original requested}
  (evaluated : request.Evaluation)

/-- The first chart vertex of an original parent reads its actual shared radial polynomial value. -/
private theorem parentTrace_first (branch : HyperellipticReciprocal.originOrder curve = 1)
    (i : Fin original.plans.length) :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get i)).first
      = (Evaluation.radialValues evaluated) ((Evaluation.firstCoordinate evaluated) i) := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace_first (evaluated.entries.get
    i)]
  unfold Evaluation.firstChartPoint
  rw [Evaluation.chartPoint_readback (evaluated.entries.get i) branch]
  rw [(evaluated.shared i).1, (evaluated.shared i).2]
  rfl

/-- The last chart vertex of an original parent reads its actual shared radial polynomial value. -/
private theorem parentTrace_last (branch : HyperellipticReciprocal.originOrder curve = 1)
    (i : Fin original.plans.length) :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get i)).last
      = (Evaluation.radialValues evaluated) ((Evaluation.lastCoordinate evaluated) i) := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace_last (evaluated.entries.get i)]
  unfold Evaluation.lastChartPoint
  rw [Evaluation.chartPoint_readback (evaluated.entries.get i) branch]
  rw [(evaluated.shared i).1, (evaluated.shared i).2]
  rfl

/-- The actual full trace formed by concatenating every original retained parent chart trace. -/
@[expose] def Evaluation.chartTrace : JoinedTrace.VertexTrace PrimitivePoint :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace (fun i =>
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get i)))

/-- Inserting the actual joins between original parent chart traces satisfies the retained complete area error bound. -/
theorem Evaluation.parentTrace_insertion {error magnitude : InverseRootPolynomial.Coordinate}
    (errorNonnegative : 0 ≤ error) (magnitudeNonnegative : 0 ≤ magnitude) (small : error ≤ magnitude)
    (totals : ∀ i, (PrimitivePoint.Bounded (PairedIncrementArea.total ((VertexTrace.increments
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get i))
      id)))) magnitude)
    (gaps : ∀ i : Fin (original.plans.length - 1),
      (PrimitivePoint.Bounded (((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace
        (evaluated.entries.get (PairedBoundaryClosure.rightParent i))).first).sub
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get
          (PairedBoundaryClosure.leftParent i))).last)) error) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (List.ofFn (fun i => (VertexTrace.increments
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get i))
      id))).flatten -
      PairedIncrementArea.area ((VertexTrace.increments
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
        evaluated) id))) ≤
      32 * ((2 * original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * error * magnitude :=
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.family_insertion (fun i =>
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get i)))
    errorNonnegative magnitudeNonnegative small totals gaps).1

/-- The cached original parent junction increment equals the actual next trace start minus the previous trace end. -/
theorem Evaluation.junctionIncrement_trace (i j : Fin original.plans.length) :
    (Evaluation.junctionIncrement evaluated) i j =
      ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get
      j)).first).sub
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get
        i)).last := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace_first (evaluated.entries.get
    j), Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace_last (evaluated.entries.get
    i)]
  rfl

/-- Inserting all original parent joins changes the complete retained trace total within its squared-count gap bound. -/
theorem Evaluation.parentTrace_total_insertion {error magnitude : InverseRootPolynomial.Coordinate}
    (errorNonnegative : 0 ≤ error) (magnitudeNonnegative : 0 ≤ magnitude) (small : error ≤ magnitude)
    (totals : ∀ i, (PrimitivePoint.Bounded (PairedIncrementArea.total ((VertexTrace.increments
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get i))
      id)))) magnitude)
    (gaps : ∀ i : Fin (original.plans.length - 1),
      (PrimitivePoint.Bounded (((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace
        (evaluated.entries.get (PairedBoundaryClosure.rightParent i))).first).sub
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get
          (PairedBoundaryClosure.leftParent i))).last)) error) :
    (PrimitivePoint.Bounded ((PairedIncrementArea.total (List.ofFn (fun i => (VertexTrace.increments
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get i))
      id))).flatten).sub
      (PairedIncrementArea.total ((VertexTrace.increments
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
        evaluated) id)))))
      (((2 * original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * error) :=
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.family_insertion (fun i =>
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace (evaluated.entries.get i)))
    errorNonnegative magnitudeNonnegative small totals gaps).2

/-- The original linked-boundary certificate pays each actual retained parent trace junction increment. -/
theorem LinkedRequest.Certificate.trace_increments_bounded {junctionTarget : InverseRootPolynomial.Coordinate}
    {linked : PairedBoundaryClosure.LinkedRequest request junctionTarget} (certificate : linked.Certificate)
    (i : Fin (original.plans.length - 1)) :
    (PrimitivePoint.Bounded (((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace
      (certificate.boundary.entries.get (PairedBoundaryClosure.rightParent i))).first).sub
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace
        (certificate.boundary.entries.get (PairedBoundaryClosure.leftParent i))).last)) linked.allowance :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.junctionIncrement_trace
    certificate.boundary _ _ ▸ certificate.increments_bounded i

/-- The full original parent chart trace area retains every cached parent area and all internal and cross-parent
connectors. -/
theorem Evaluation.chartTrace_area (branch : HyperellipticReciprocal.originOrder curve = 1) :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
      evaluated).area id = FiniteSum.Fin.sumFin (fun i => (evaluated.entries.get i).chartArea) +
      (Evaluation.internalConnectors evaluated) + FiniteSum.Fin.sumFin (Evaluation.parentConnector evaluated) := by
  rw [chartTrace, Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace_area]
  have areas := FiniteSum.Fin.sumFin_congr (fun i =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace_area (evaluated.entries.get i))
  rw [areas, FiniteSum.Fin.sumFin_add]
  apply congrArg (fun value => FiniteSum.Fin.sumFin (fun i => (evaluated.entries.get i).chartArea) +
    (Evaluation.internalConnectors evaluated) + value)
  exact FiniteSum.Fin.sumFin_congr (fun i => congrArg₂ Stokes.edgeArea
    (parentTrace_last evaluated branch
      _) (parentTrace_first evaluated
      branch _))

/-- The actual original joined parent trace with its first retained vertex appended as the closing point. -/
@[expose] def Evaluation.closedChartTrace : JoinedTrace.VertexTrace PrimitivePoint :=
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
    evaluated).join
    ⟨(Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
    evaluated).first, []⟩

/-- The actual increment total of the explicitly closed original chart trace is zero. -/
theorem Evaluation.closedChartTrace_total :
    PairedIncrementArea.total ((VertexTrace.increments
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace
      evaluated) id)) = PrimitivePoint.zero := by
  let trace :=
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace
    evaluated)
  have total := CenteredPathIncrements.increments_total (fun vertex => id (trace.indexed vertex))
  rw [(VertexTrace.indexed_increments trace id)] at total
  change PairedIncrementArea.total ((VertexTrace.increments trace id)) =
    (DyadicTrace.indexed trace.first trace.rest (Fin.last trace.rest.length)).sub trace.first at total
  rw [DyadicTrace.indexed_last] at total
  have last : trace.last = trace.first := VertexTrace.join_last _ _
  change PairedIncrementArea.total ((VertexTrace.increments trace id)) = trace.last.sub trace.first at total
  rw [last] at total
  exact total.trans (by
    apply congrArg₂ PrimitivePoint.mk <;> ring1)

/-- The explicitly closed original chart trace has the same area as its actual increment polygon. -/
theorem Evaluation.closedChartTrace_increment_area :
    PairedIncrementArea.area ((VertexTrace.increments
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace
      evaluated) id)) =
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace
      evaluated).area id := by
  let trace :=
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace
    evaluated)
  have traced := CenteredPathIncrements.increments_trace (fun vertex => id (trace.indexed vertex))
  rw [(VertexTrace.indexed_increments trace id), PairedIncrementArea.traceArea_eq,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace_total
    evaluated] at traced
  have equal := traced.trans (trace.indexed_area id)
  change PairedIncrementArea.area ((VertexTrace.increments trace id)) + Stokes.edgeArea trace.first PrimitivePoint.zero
    = trace.area id at equal
  have zero : Stokes.edgeArea trace.first PrimitivePoint.zero = 0 := by
    unfold Stokes.edgeArea PrimitivePoint.zero;
    ring1
  rw [zero, add_zero] at equal
  exact equal

/-- An empty original trace family is exactly the single retained zero vertex. -/
private theorem familyTrace_empty {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint) (absent : n
  = 0) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace traces = ⟨PrimitivePoint.zero, []⟩ := by
      subst n; rfl

/-- The unclosed trace total is paid by the actual root-return junction, not inferred from the area of its artificially
closed trace. -/
theorem ClosingPlan.trace_total_bounded {tolerance : InverseRootPolynomial.Coordinate} (closing :
  PairedClosedBoundary.ClosingPlan request tolerance)
    (later : closing.index request ≤ evaluated.externalFloor) (nonnegative : 0 ≤ tolerance)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    (PrimitivePoint.Bounded (PairedIncrementArea.total ((VertexTrace.increments
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace evaluated)
      id)))) tolerance := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.trace_increment_total]
  cases closing with
  | empty absent =>
      have empty := familyTrace_empty
        (fun i => (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace
        (evaluated.entries.get i))) absent
      change (PrimitivePoint.Bounded ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace
        _).last.sub (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace _).first)) tolerance
      rw [empty]
      constructor <;> change Data.Gaussian.Basic.Canonical.normSq (0 - 0) ≤ tolerance <;>
        rw [sub_self, Data.Gaussian.Basic.Canonical.normSq_zero] <;> exact nonnegative
  | present positive joined junction =>
      have bound := junction.increment_accurate evaluated later branch
      rw
        [Evaluation.junctionIncrement_trace
        evaluated] at bound
      rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace_last _ positive,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace_first _ positive]
      have reversed (a b : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical.normSq (a - b) =
        Data.Gaussian.Basic.Canonical.normSq (b - a) := by
        rw [show a - b = -(b - a) by ring1, Data.Gaussian.Basic.Canonical.normSq_neg]
      constructor
      · exact (reversed _ _).trans_le bound.1
      · exact (reversed _ _).trans_le bound.2

/-- Closing a cumulative increment path contributes no area: the final increment is the negative of its total. No
small-gap estimate is needed. -/
theorem Evaluation.chartTrace_closing_area :
    PairedIncrementArea.area ((VertexTrace.increments
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace evaluated)
      id)) =
      PairedIncrementArea.area ((VertexTrace.increments
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace
        evaluated) id)) := by
  rw
    [Evaluation.closedChartTrace_increment_area
    evaluated,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace,
    VertexTrace.join_area,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.trace_increment_area
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
      evaluated)]
  change _ = _ + Stokes.edgeArea
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
    evaluated).last
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
    evaluated).first + 0
  unfold Stokes.edgeArea PrimitivePoint.sub
  ring1

/-- The actual last-to-first trace edge is exactly the retained original closing connector. -/
theorem ClosingPlan.trace_connector {tolerance : InverseRootPolynomial.Coordinate} (closing :
  PairedClosedBoundary.ClosingPlan request tolerance)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Stokes.edgeArea
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
      evaluated).last
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
      evaluated).first = closing.connector evaluated := by
  cases closing with
  | empty absent =>
      have empty := familyTrace_empty
        (fun i => (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace
        (evaluated.entries.get i))) absent
      change Stokes.edgeArea (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace _).last
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace _).first = 0
      rw [empty]
      rfl
  | present positive joined junction =>
      rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace_last _ positive,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.familyTrace_first _ positive,
        parentTrace_last evaluated
          branch, parentTrace_first
          evaluated branch]
      rfl

/-- The complete closed original chart trace area retains every parent area, internal connector, parent connector and
actual closing connector. -/
theorem ClosingPlan.closedChartTrace_area {tolerance : InverseRootPolynomial.Coordinate} (closing :
  PairedClosedBoundary.ClosingPlan request tolerance)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace
      evaluated).area id = FiniteSum.Fin.sumFin (fun i => (evaluated.entries.get i).chartArea) +
      (Evaluation.internalConnectors evaluated) + FiniteSum.Fin.sumFin (Evaluation.parentConnector evaluated) +
        closing.connector evaluated := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace,
    VertexTrace.join_area,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace_area
    evaluated branch]
  change _ + Stokes.edgeArea
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
    evaluated).last
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
    evaluated).first + 0 = _
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.ClosingPlan.trace_connector
    evaluated closing branch]
  ring1

end BoundaryBankRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
