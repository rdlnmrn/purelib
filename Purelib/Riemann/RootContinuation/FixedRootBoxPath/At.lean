module

public import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Fixed-box root agreement at an actual retained path parameter

The original dyadic walk already accepts arbitrary unit-interval endpoints.
Its actual scale times the squared requested span determines a finite depth
for 0 to time. Both original budgets and their separate retained owner
refinements remain unchanged; no endpoint equivalence is assumed.
-/

public section

namespace Purelib.Riemann.RootContinuation.FixedRootBoxPath.PathData

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.RootContinuation.FixedRootBoxBudget
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {firstSource secondSource : Canonical}
    {firstOwner : Owner firstSource} {secondOwner : Owner secondSource}
    {first : Budget firstOwner} {second : Budget secondOwner} (path : PathData first second)

/-- Propagate the original signed starting agreement to any requested retained unit-interval parameter.

The finite depth search uses the actual squared span and the same two
positive contour clearances. The original walk and its full operational
comparison preserve both requested starting sample indices.
-/
def equivalentAt (time : Rational) (inside : Inside time)
    (start : path.Agreement 0 (by decide +kernel)) : path.Agreement time inside := by
  unfold Agreement
  refine ⟨fun leftStart rightStart target positive => ?_⟩
  let cost := path.scale * (time - 0) ^ 2
  have nonnegative : 0 ≤ cost := Order.Arithmetic.mul_nonneg_direct path.scale_nonnegative
    (Order.Arithmetic.sq_nonneg_direct (time - 0))
  let depth := Geometric.Search.firstQuarterBelow cost 0 (min first.clearance second.clearance)
  have small := Geometric.Search.firstQuarterBelow_accurate cost nonnegative 0
    (min first.clearance second.clearance) (Order.Basic.lt_min first.clearance_positive second.clearance_positive)
  let result := path.walk depth 0 time (by decide +kernel) inside small start
  exact (path.expose result).compare leftStart rightStart target positive

/-- Derive agreement of two actual interior Owners from their separate original-box refinements and starting relation.

All four Owners are inputs retained at their original path parameters.
The finite path walk derives the interior signed comparison; no refinement
of one input to the other input's box is required or assumed.
-/
def retainedEquivalentAt (time : Rational) (inside : Inside time)
    (firstStart secondStart : Owner (path.point 0))
    (firstStartRefines : firstStart.track.initial.box.Refines firstOwner.track.initial.box)
    (secondStartRefines : secondStart.track.initial.box.Refines secondOwner.track.initial.box)
    (start : NamedEquivalent (ownerRootName firstStart.parameterNonzero firstStart)
      (ownerRootName secondStart.parameterNonzero secondStart))
    (firstAt secondAt : Owner (path.point time))
    (firstAtRefines : firstAt.track.initial.box.Refines firstOwner.track.initial.box)
    (secondAtRefines : secondAt.track.initial.box.Refines secondOwner.track.initial.box) :
    NamedEquivalent (ownerRootName firstAt.parameterNonzero firstAt)
      (ownerRootName secondAt.parameterNonzero secondAt) where
  compare := fun leftStart rightStart target positive =>
    let initial : path.Agreement 0 (by decide +kernel) := by
      unfold Agreement
      exact (path.firstRetained 0 (by decide +kernel) firstStart firstStartRefines).trans
        (start.trans (path.secondRetained 0 (by decide +kernel) secondStart secondStartRefines).symm)
    let compared := path.expose (path.equivalentAt time inside initial)
    let result := (path.firstRetained time inside firstAt firstAtRefines).symm.trans
      (compared.trans (path.secondRetained time inside secondAt secondAtRefines))
    result.compare leftStart rightStart target positive

end Purelib.Riemann.RootContinuation.FixedRootBoxPath.PathData

end
