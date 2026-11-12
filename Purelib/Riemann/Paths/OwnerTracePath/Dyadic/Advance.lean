module

public import Purelib.Riemann.Paths.OwnerTracePath.Dyadic
public import Purelib.Riemann.Paths.OwnerTraceReadings.Transport
public import Purelib.Riemann.RootContinuation.RootContinuationCongruence.Advance
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

/-! # Realizing one GIVEN signed advance and its retained target handoff

Exact polynomial endpoint evaluations reindex the whole original advance.
The same moved Owner and comparison are retained as data. The paid dyadic
trace constructor makes only the genuinely new interior and reading work.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Dyadic

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings
open Purelib.Riemann.RootContinuation.RootContinuationCongruence (Advance)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName_castOwnerParameter)
open Purelib.RootIsolation.SquareRoot.Owner.Transport

variable {referencePolynomial polynomial : CoefficientPolynomial} {count : Nat}
    (patch : ContinuedNeighborhood referencePolynomial count)
    {sourceParameter targetParameter : Canonical}
    (source : Owner sourceParameter) (target : Owner targetParameter)
    (boxes : source.track.initial.box = target.track.initial.box)
    (small : Norm.Basic.normSq (sourceParameter - targetParameter) < source.track.initial.clearance.bound)
    (retained : Advance source target boxes small)
    (firstEq : sourceParameter = value polynomial first) (lastEq : targetParameter = value polynomial last)

/-- Reindex the SAME original source Owner at the actual polynomial's initial evaluation. -/
@[expose] def sourceOwner : Owner (value polynomial first) := castOwnerParameter firstEq source

/-- Reindex the SAME whole GIVEN advance output at the actual polynomial's terminal evaluation. -/
@[expose] def movedOwner : Owner (value polynomial last) := castOwnerParameter lastEq retained.moved

/-- Reindex the SAME independent target Owner at the actual polynomial's terminal evaluation. -/
@[expose] def targetOwner : Owner (value polynomial last) := castOwnerParameter lastEq target

variable (sourceRefines : source.track.initial.box.Refines patch.base.seed.owner.track.initial.box)

include sourceRefines in
/-- The exact source reindexing retains its original signed-box refinement. -/
theorem sourceOwner_refines :
    (sourceOwner (source := source) (firstEq := firstEq)).track.initial.box.Refines
      patch.base.seed.owner.track.initial.box :=
  Eq.mpr (congrArg (fun box : Box => box.Refines patch.base.seed.owner.track.initial.box)
    (castOwnerParameter_initial_box firstEq source)) sourceRefines

include small lastEq in
/-- The exact endpoint evaluation equalities transport the original advance's actual clearance payment. -/
theorem endpoint_small : Norm.Basic.normSq (value polynomial first - value polynomial last) <
    (sourceOwner (source := source) (firstEq := firstEq)).track.initial.clearance.bound := by
  have parameters := congrArg₂ (fun first last : Canonical => Norm.Basic.normSq (first - last)) firstEq lastEq
  exact Eq.mp (congrArg₂ (fun movement clearance : Rational => movement < clearance) parameters
    (castOwnerParameter_clearance_bound firstEq source).symm) small

variable (nonzero : ∀ endpoint : Endpoint, value polynomial endpoint ≠ 0)

/-- The reindexed GIVEN moved Owner keeps the whole original advance factory, without another advance. -/
theorem movedOwner_factory : movedOwner (source := source) (target := target) (boxes := boxes) (small := small)
      (retained := retained) (lastEq := lastEq) =
    (sourceOwner (source := source) (firstEq := firstEq)).advance (nonzero last)
      (endpoint_small (source := source) (small := small) (firstEq := firstEq) (lastEq := lastEq)) :=
  (congrArg (castOwnerParameter lastEq) retained.moved_eq).trans
    (castOwnerParameter_advance firstEq lastEq source target.parameterNonzero small
      (nonzero last) (endpoint_small (source := source) (small := small) (firstEq := firstEq) (lastEq := lastEq)))

/-- The SAME actual target handoff is transported through whole-Owner parameter readbacks. -/
def handoff : NamedEquivalent (ownerName (movedOwner (source := source) (target := target)
      (boxes := boxes) (small := small)
      (retained := retained) (lastEq := lastEq)))
    (ownerName (targetOwner (target := target) (lastEq := lastEq))) :=
  NamedEquivalent.transport (ownerRootName_castOwnerParameter lastEq retained.moved).symm
    (ownerRootName_castOwnerParameter lastEq target).symm retained.compared

variable (scale : Rational) (scaleNonnegative : 0 ≤ scale)
    (variation : ∀ left right : Endpoint, Norm.Basic.normSq (value polynomial left - value polynomial right) ≤
      scale * (right.parameter - left.parameter) ^ 2)
    (wholeSmall : scale < source.track.initial.clearance.bound)

include wholeSmall in
/-- Whole-Owner source reindexing preserves the actual coarse scale clearance payment. -/
theorem source_scale_small :
    scale < (sourceOwner (source := source) (firstEq := firstEq)).track.initial.clearance.bound :=
  wholeSmall.trans_eq (castOwnerParameter_clearance_bound firstEq source).symm

/-- The SAME original advance/cache and its actual fine trace, with complete factory and endpoint ownership retained. -/
@[expose] def AdvanceTrace :=
  (_original : { value : Advance source target boxes small // value = retained }) ×
    Preparation patch polynomial (sourceOwner (source := source) (firstEq := firstEq))
      (sourceOwner_refines (patch := patch) (source := source) (firstEq := firstEq)
        (sourceRefines := sourceRefines)) nonzero scale scaleNonnegative variation
      (source_scale_small (source := source) (firstEq := firstEq) (scale := scale) (wholeSmall := wholeSmall))
      (movedOwner (source := source) (target := target) (boxes := boxes) (small := small)
      (retained := retained) (lastEq := lastEq)) (targetOwner (target := target) (lastEq := lastEq))
      (endpoint_small (source := source) (small := small) (firstEq := firstEq) (lastEq := lastEq))
      (movedOwner_factory (source := source) (target := target) (boxes := boxes) (small := small)
        (retained := retained) (firstEq := firstEq) (lastEq := lastEq) (nonzero := nonzero))
      (handoff (source := source) (target := target) (boxes := boxes) (small := small)
        (retained := retained) (lastEq := lastEq))

/-- Realize the GIVEN coarse signed advance once, retaining the original advance and the complete resulting trace.

All endpoint equalities are exact polynomial evaluation readbacks. No
source/target Owner is acquired, and the GIVEN advance is not executed.
The only new work is the dyadic preparation's explicit interior advances,
tails, comparisons, final stationary join and one reading realization.
-/
def realizeAdvance : AdvanceTrace patch source target boxes small retained firstEq lastEq sourceRefines nonzero
    scale scaleNonnegative variation wholeSmall :=
  let result := prepare patch polynomial (sourceOwner (source := source) (firstEq := firstEq))
    (sourceOwner_refines (patch := patch) (source := source) (firstEq := firstEq)
        (sourceRefines := sourceRefines)) nonzero scale scaleNonnegative variation
    (source_scale_small (source := source) (firstEq := firstEq) (scale := scale) (wholeSmall := wholeSmall))
    (movedOwner (source := source) (target := target) (boxes := boxes) (small := small)
      (retained := retained) (lastEq := lastEq)) (targetOwner (target := target) (lastEq := lastEq))
    (endpoint_small (source := source) (small := small) (firstEq := firstEq) (lastEq := lastEq))
    (movedOwner_factory (source := source) (target := target) (boxes := boxes) (small := small)
        (retained := retained) (firstEq := firstEq) (lastEq := lastEq) (nonzero := nonzero))
    (handoff (source := source) (target := target) (boxes := boxes) (small := small)
        (retained := retained) (lastEq := lastEq))
  ⟨⟨retained, rfl⟩, result⟩

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Dyadic

end
