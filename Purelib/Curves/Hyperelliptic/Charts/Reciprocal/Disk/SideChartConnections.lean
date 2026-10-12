module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaJoins
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReplacementRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
open Purelib.Integration.Path
open Purelib.Integration.Path.IncrementAreaJoins
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization

/-!
# Full side chart paths with the original parent connectors

Each replacement has the original parent's total. Prepending the same
connector and appending the next parent preserves every cross term exactly.
The cached list of parent area differences pays the complete side error.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests (ChartReplacements)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget target :
    Coordinate}
  {minimum index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Join the actual retained replacement paths using the original parent endpoint connectors in their existing order. -/
@[expose] def connectedPaths : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers
  : UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → SideChartRequests.ChartReplacements target
      evaluated → InverseRootPolynomial.Gaussian → List (List InverseRootPolynomial.Gaussian)
  | _, _, _, _, .nil, .nil, _ => []
  | _, _, _, _, .cons first rest, .cons _ head tail, previous =>
      ((first.cap.firstValue - previous) :: head.replacement.paths.flatten) ::
        connectedPaths rest tail
        first.cap.joined.lastValue

set_option genInjectivity false in
/-- The complete retained replacement side path with the original connectors and exact area-error list.

Original parent totals preserve every cross term; one actual local error per parent pays the remaining full-side
discrepancy. -/
structure Connected {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) (charts : SideChartRequests.ChartReplacements
      target evaluated) (previous : InverseRootPolynomial.Gaussian) where
  /-- The cached ordered replacement blocks with their actual original leading connectors. -/ paths : List (List
    InverseRootPolynomial.Gaussian)
  /-- The block cache is exactly the original connected-path construction from the retained parent evaluations. -/
    paths_eq : paths = connectedPaths evaluated charts
    previous
  /-- The cached complete increment and area summary of these exact retained paths. -/ summary : IncrementArea.Summary
    paths.flatten
  /-- The complete replacement total equals the original connected parent-bank total. -/ total_eq : summary.total =
    ((Evaluations.connectedSummary evaluated previous)).total
  /-- The cached list of actual replacement-minus-original parent area discrepancies. -/ errors : List
    InverseRootPolynomial.Gaussian
  /-- There is exactly one retained area error for each actual original parent. -/ length_eq : errors.length =
    parents.length
  /-- The full connected area discrepancy equals the sum of the actual retained parent errors. -/ area_eq : summary.area
    - ((Evaluations.connectedSummary evaluated previous)).area = Data.Gaussian.Norm.Sum.Basic.gaussianSum errors
  /-- Every actual cached parent-area discrepancy satisfies the retained local target. -/ bounded : ∀ error ∈ errors,
    Data.Gaussian.Norm.Basic.normSq error ≤ target

constructive_injectivity Connected

namespace Connected

/-- Compose the cached replacement and original parent summaries with the same actual connectors, retaining exact total
and area-error readbacks. -/
@[expose] def build : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) → (previous : InverseRootPolynomial.Gaussian) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections.Connected evaluated charts previous
  | _, _, _, _, .nil, .nil, _ =>
      ⟨[], rfl, IncrementArea.Summary.build [], rfl, [], rfl, by
        change (0 : InverseRootPolynomial.Gaussian) - 0 = 0;
        ring1,
        fun _ member => False.elim (List.not_mem_nil member)⟩
  | _, _, _, _, .cons first rest, .cons _ head tail, previous => by
      let connector := first.cap.firstValue - previous
      let tail := build rest tail
        first.cap.joined.lastValue
      let headSummary := Summary.prepend head.replacement.summary connector
      have headTotal := head.replacement.total_preserved first.cap.joined
      refine ⟨(connector :: head.replacement.paths.flatten) :: tail.paths, ?_, headSummary.append tail.summary,
        ?_, (head.replacement.summary.area - first.cap.joined.summary.area) :: tail.errors,
        congrArg Nat.succ tail.length_eq, ?_, ?_⟩
      · change _ :: tail.paths = _ :: _
        rw [tail.paths_eq]
      · change connector + head.replacement.summary.total + tail.summary.total =
          connector + first.cap.joined.summary.total + ((Evaluations.connectedSummary rest
            first.cap.joined.lastValue)).total
        rw [headTotal, tail.total_eq]
      · change (head.replacement.summary.area + BoundaryRibbon.area connector head.replacement.summary.total) +
          tail.summary.area + BoundaryRibbon.area (connector + head.replacement.summary.total) tail.summary.total -
          ((first.cap.joined.summary.area + BoundaryRibbon.area connector first.cap.joined.summary.total) +
            ((Evaluations.connectedSummary rest first.cap.joined.lastValue)).area +
            BoundaryRibbon.area (connector + first.cap.joined.summary.total) ((Evaluations.connectedSummary rest
              first.cap.joined.lastValue)).total) =
          (head.replacement.summary.area - first.cap.joined.summary.area) +
            Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.errors
        rw [headTotal, tail.total_eq, ← tail.area_eq]
        ring1
      · intro error member
        rcases Data.List.Membership.mem_cons.mp member with same | member
        · subst error
          exact head.area_error.le
        · exact tail.bounded error member

variable {parents : List (CenteredEdge curve differential)}
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
  {prepared : SideBank regular covers} {requests :
    Requests sourceTarget reciprocalTarget
    coefficientTarget totalTarget areaTarget minimum prepared}
  {evaluated : Evaluations sample depth
    readingIndex requests} {charts :
    ChartReplacements target evaluated} {previous
    : Gaussian}

/-- The complete connected replacement total telescopes to the actual original last reading minus the supplied previous
value. -/
theorem total (connected : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections.Connected evaluated charts
  previous) : connected.summary.total = Evaluations.lastValue evaluated previous - previous :=
  connected.total_eq.trans (Evaluations.connected_total evaluated previous)

/-- The complete connected-side area discrepancy is bounded by the original parent count squared times the retained
local target. -/
theorem area_error (connected : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections.Connected evaluated
  charts previous) :
    Data.Gaussian.Norm.Basic.normSq (connected.summary.area - ((Evaluations.connectedSummary evaluated
      previous)).area) ≤ (parents.length : InverseRootPolynomial.Coordinate) ^ 2 * target := by
  rw [connected.area_eq]
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le connected.errors target connected.bounded
  rw [connected.length_eq] at estimate
  exact estimate.trans_eq (by ring1)

end Connected
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
