module

public import Purelib.Riemann.Paths.OwnerTracePath.Dyadic.Advance
public import Purelib.Riemann.Paths.OwnerTracePath.Between
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings.Trace
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Trace
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath.Dyadic
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootContinuationCongruence.Advance
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

/-! # Retaining the actual advance link prefix before endpoint readings

The original exact endpoint transports, source clearance and whole advance
factory are reused. The shared dyadic worker stops before realization;
its complete input advance, midpoint/request tree and final stationary
handoff remain data for the common-corner consumer.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Dyadic

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings
open Purelib.Riemann.RootContinuation.SquareRootProvenance (traceAllowance)
open Purelib.Riemann.RootContinuation.RootContinuationCongruence (Advance)

variable {referencePolynomial polynomial : CoefficientPolynomial} {count : Nat}
    (patch : ContinuedNeighborhood referencePolynomial count)
    {sourceParameter targetParameter : Canonical}
    (source : Owner sourceParameter) (target : Owner targetParameter)
    (boxes : source.track.initial.box = target.track.initial.box)
    (small : Norm.Basic.normSq (sourceParameter - targetParameter) < source.track.initial.clearance.bound)
    (retained : Advance source target boxes small)
    (firstEq : sourceParameter = value polynomial first) (lastEq : targetParameter = value polynomial last)

variable (sourceRefines : source.track.initial.box.Refines patch.base.seed.owner.track.initial.box)

variable (nonzero : ∀ endpoint : Endpoint, value polynomial endpoint ≠ 0)

variable (scale : Rational) (scaleNonnegative : 0 ≤ scale)
    (variation : ∀ left right : Endpoint, Norm.Basic.normSq (value polynomial left - value polynomial right) ≤
      scale * (right.parameter - left.parameter) ^ 2)
    (wholeSmall : scale < source.track.initial.clearance.bound)

/-- The SAME advance/cache and its actual prefix before displayed readings, retaining whole factories and endpoints. -/
@[expose] def AdvanceLinks :=
  (_original : { value : Advance source target boxes small // value = retained }) ×
    LinkPreparation patch polynomial (sourceOwner (source := source) (firstEq := firstEq))
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

/-- Retain the SAME whole advance and all actual link/request caches without realizing them yet. -/
def linkAdvance : AdvanceLinks patch source target boxes small retained firstEq lastEq sourceRefines nonzero
    scale scaleNonnegative variation wholeSmall :=
  let result := prepareLinks patch polynomial (sourceOwner (source := source) (firstEq := firstEq))
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

namespace AdvanceLinks

variable {patch source target boxes small retained firstEq lastEq sourceRefines nonzero
    scale scaleNonnegative variation wholeSmall}
    (linked : AdvanceLinks patch source target boxes small retained firstEq lastEq sourceRefines nonzero
      scale scaleNonnegative variation wholeSmall)

/-- Read the SAME whole first request on the exact transported source Owner, including its original factory. -/
@[expose] def firstRequest :
    { result : OwnerTail.TraceRequest (sourceOwner (source := source) (firstEq := firstEq))
        patch.rootLower patch.rootLower_positive //
      result = OwnerTail.requestTrace (sourceOwner (source := source) (firstEq := firstEq))
        patch.rootLower patch.rootLower_positive } := LinkPreparation.firstRequest (cached := linked.2)

/-- Read the SAME whole target request on the exact transported cached Owner, including its original factory. -/
@[expose] def targetRequest :
    { result : OwnerTail.TraceRequest (targetOwner (target := target) (lastEq := lastEq))
        patch.rootLower patch.rootLower_positive //
      result = OwnerTail.requestTrace (targetOwner (target := target) (lastEq := lastEq))
        patch.rootLower patch.rootLower_positive } := LinkPreparation.targetRequest (cached := linked.2)

/-- A supplied first reading beyond this SAME retained request floor meets the original strict trace residual. -/
theorem first_residual
    (sample : OwnerReading (sourceOwner (source := source) (firstEq := firstEq)))
    (later : (AdvanceLinks.firstRequest (linked := linked)).val.compared.leftIndex ≤ sample.index) :
    Norm.Basic.normSq (sample.value * sample.value - value polynomial first) < traceAllowance patch.rootLower := by
  let required := (AdvanceLinks.firstRequest (linked := linked)).val
  exact required.residual (sample.inTail required.tail (required.compared.left_ge.trans later)) later

/-- A supplied target reading beyond this SAME retained request floor meets the original strict trace residual. -/
theorem target_residual
    (sample : OwnerReading (targetOwner (target := target) (lastEq := lastEq)))
    (later : (AdvanceLinks.targetRequest (linked := linked)).val.compared.leftIndex ≤ sample.index) :
    Norm.Basic.normSq (sample.value * sample.value - value polynomial last) < traceAllowance patch.rootLower := by
  let required := (AdvanceLinks.targetRequest (linked := linked)).val
  exact required.residual (sample.inTail required.tail (required.compared.left_ge.trans later)) later

/-- Read the SAME actual path, including its final stationary moved-to-cached Owner handoff. -/
@[expose] def whole : OwnerPath polynomial (Cast.Path.ofCoordinate first.parameter)
    (sourceOwner (source := source) (firstEq := firstEq)) (Cast.Path.ofCoordinate last.parameter)
    (targetOwner (target := target) (lastEq := lastEq)) := LinkPreparation.whole (cached := linked.2)

/-- The SAME path is genuinely nonempty before any displayed corner or interior reading is taken. -/
theorem nonempty : linked.whole.vertices ≠ [] := LinkPreparation.nonempty (cached := linked.2)

end AdvanceLinks

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Dyadic

end
