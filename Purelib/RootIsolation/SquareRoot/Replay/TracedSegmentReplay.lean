module
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.RootIsolation.SquareRoot.Preparation.Terminal
public import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

@[expose] public section

/-! Restore the canonical segment trace from its checked terminal acquisition. -/
namespace Purelib.RootIsolation.SquareRoot.Replay.TracedSegmentReplay

open Purelib.Riemann.Paths.PreparedClearPathModels
open Purelib.RootIsolation.SquareRoot.Preparation.Terminal
open Purelib.Riemann.Paths.PreparedPathTrace

/-- The original acquired dyadic segment indexed by the tracing budget's retained root-diameter request. -/
abbrev Acquisition {p : Riemann.Paths.PreparedClearPathModels.GaussianPolynomial} {box :
  Riemann.Paths.PreparedClearPathModels.Box} {start finish : Riemann.Paths.PreparedClearPathModels.Gaussian}
    (segment : Geometry.ClearPath.ClearSegment p box start finish) (within : segment.WithinAmbient)
    (owner : Riemann.Paths.PreparedClearPathModels.Owner (p.eval start)) (budget :
      Riemann.Paths.PreparedTraceBudget segment Riemann.Paths.PreparedClearPathModels.zeroEndpoint
      Riemann.Paths.PreparedClearPathModels.oneEndpoint) :=
  SquareRoot.Preparation.Terminal.AcquiredDyadic segment within owner budget.rootDiameter budget.rootDiameter_positive

/-- Run the original terminal acquisition using the budget's geometric preferred depth and certified safe depth. -/
def canonicalAcquisition {p : Riemann.Paths.PreparedClearPathModels.GaussianPolynomial} {box :
  Riemann.Paths.PreparedClearPathModels.Box} {start finish : Riemann.Paths.PreparedClearPathModels.Gaussian}
    (segment : Geometry.ClearPath.ClearSegment p box start finish) (within : segment.WithinAmbient)
    (owner : Riemann.Paths.PreparedClearPathModels.Owner (p.eval start)) (budget :
      Riemann.Paths.PreparedTraceBudget segment Riemann.Paths.PreparedClearPathModels.zeroEndpoint
      Riemann.Paths.PreparedClearPathModels.oneEndpoint) :=
  SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire segment within owner budget.rootDiameter
    budget.rootDiameter_positive
    (Approximation.Rational.Geometric.Search.firstQuarterBelow budget.variation 0 budget.movementBudget) budget.depth
    (budget.meshSafe (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner) (by decide))

/-- Restore a traced segment from an acquisition equal to the canonical selected result.

The original budget, generated requests and cached finishing owner are reused with their exact retained identities. -/
def restore {p : Riemann.Paths.PreparedClearPathModels.GaussianPolynomial} {box :
  Riemann.Paths.PreparedClearPathModels.Box} {start finish : Riemann.Paths.PreparedClearPathModels.Gaussian}
    (segment : Geometry.ClearPath.ClearSegment p box start finish) (within : segment.WithinAmbient)
    (owner : Riemann.Paths.PreparedClearPathModels.Owner (p.eval start)) (budget :
      Riemann.Paths.PreparedTraceBudget segment Riemann.Paths.PreparedClearPathModels.zeroEndpoint
      Riemann.Paths.PreparedClearPathModels.oneEndpoint)
    (acquired : SquareRoot.Replay.TracedSegmentReplay.Acquisition segment within owner budget)
    (same : acquired = (SquareRoot.Replay.TracedSegmentReplay.canonicalAcquisition segment within owner budget).val) :
    Riemann.Paths.PreparedPathTrace.TracedSegment segment within owner :=
  let depth := Approximation.Rational.Geometric.Search.firstQuarterBelow budget.variation 0 budget.movementBudget
  have selectedDepth : acquired.depth = depth ∨ acquired.depth = budget.depth := by
    rw [same]
    exact (SquareRoot.Replay.TracedSegmentReplay.canonicalAcquisition segment within owner budget).property
  have fits : budget.RequestsFit Riemann.Paths.PreparedClearPathModels.zeroEndpoint
    acquired.prepared.subdivision.requests := by
    rw [Riemann.Branches.PreparedSheetContinuation.Subdivision.tryDyadic_requests segment within
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
        (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner) acquired.depth budget.rootDiameter
      budget.rootDiameter_positive acquired.success]
    rcases selectedDepth with selected | selected
    · rw [selected]
      apply budget.dyadicRequests_fit_of_variation (by decide) depth budget.rootDiameter
        budget.rootDiameter_positive le_rfl
      exact (Approximation.Rational.Geometric.Search.firstQuarterBelow_accurate budget.variation (by
        rw [budget.variation_eq]
        exact Riemann.Branches.ClearSheetContinuation.variationBound_nonneg segment _ _) 0 _
        budget.movementBudget_positive).le
    · rw [selected]
      exact budget.dyadicRequests_fit (by decide)
  Riemann.Paths.PreparedPathTrace.TracedSegment.ofPrepared budget acquired.prepared fits acquired.requests
    acquired.requests_eq
    acquired.finishOwner acquired.finishOwner_eq

/-- Restoring a canonical budget and acquisition gives exactly the original traced-segment constructor. -/
theorem restore_eq {p : Riemann.Paths.PreparedClearPathModels.GaussianPolynomial} {box :
  Riemann.Paths.PreparedClearPathModels.Box} {start finish : Riemann.Paths.PreparedClearPathModels.Gaussian}
    (segment : Geometry.ClearPath.ClearSegment p box start finish) (within : segment.WithinAmbient)
    (owner : Riemann.Paths.PreparedClearPathModels.Owner (p.eval start)) (budget :
      Riemann.Paths.PreparedTraceBudget segment Riemann.Paths.PreparedClearPathModels.zeroEndpoint
      Riemann.Paths.PreparedClearPathModels.oneEndpoint)
    (budgetEq : budget = Riemann.Paths.PreparedTraceBudget.build segment
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint)
    (acquired : SquareRoot.Replay.TracedSegmentReplay.Acquisition segment within owner budget)
    (same : acquired = (SquareRoot.Replay.TracedSegmentReplay.canonicalAcquisition segment within owner budget).val) :
    SquareRoot.Replay.TracedSegmentReplay.restore segment within owner budget acquired same =
      Riemann.Paths.PreparedPathTrace.TracedSegment.build segment within owner := by
  cases budgetEq
  cases same
  rfl

/-- Thread the restored terminal owner through the canonical tail. -/
theorem cons_eq {p : Riemann.Paths.PreparedClearPathModels.GaussianPolynomial} {box :
  Riemann.Paths.PreparedClearPathModels.Box} {start middle finish : Riemann.Paths.PreparedClearPathModels.Gaussian}
    (head : Geometry.ClearPath.ClearSegment p box start middle) (tail : Polynomial.Geometry.ClearPath p box middle
      finish)
    (within : (Polynomial.Geometry.ClearPath.cons head tail).WithinAmbient) (owner :
      Riemann.Paths.PreparedClearPathModels.Owner (p.eval start))
    (first : Riemann.Paths.PreparedPathTrace.TracedSegment head within.head owner)
    (firstEq : first = Riemann.Paths.PreparedPathTrace.TracedSegment.build head within.head owner)
    (rest : Riemann.Paths.PreparedPathTrace.TracedPath tail first.finishOwner)
    (restEq : rest = Riemann.Paths.PreparedPathTrace.TracedPath.build tail within.tail first.finishOwner) :
    Riemann.Paths.PreparedPathTrace.TracedPath.cons first rest = Riemann.Paths.PreparedPathTrace.TracedPath.build (.cons
      head tail) within owner := by
  cases restEq
  cases firstEq
  rfl

end Purelib.RootIsolation.SquareRoot.Replay.TracedSegmentReplay
