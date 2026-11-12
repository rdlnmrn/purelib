module

import Purelib.Riemann.RootContinuation.CoherentRoot.Localization
import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
import Purelib.Approximation.Gaussian.Sequence.Selection

/-! # Original localization requests from retained assignments and payments -/

namespace TestPurelib.Riemann.RootLocalizationRequest

open Purelib
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.CoherentRoot
open Purelib.Riemann.RootContinuation.CoherentRoot.Localization
open Purelib.Approximation.Gaussian
open Purelib.Data.Rat.Fraction

variable {polynomial : GaussianPolynomial} {input : FTA.Squarefree.Input polynomial}
  {source : Geometric.GeometricApproximation} (preparation : Preparation input source)
  {current : Nat} {target : Rational}
  (request : Sequence.Selection.Coverage.Request preparation.coverage current target)

/-- Assemble the exact original nearby result from a retained assignment and actual owner payment. -/
def nearbyFromCaches
    (localized : { value : Residual.Global.Assignment.AssignedResult input
      (preparation.source.sample request.index) (Preparation.localizationRadius target) preparation.boxes.isolation //
      value = Residual.Global.Assignment.assignInsideUsing input preparation.boxes preparation.support
        (preparation.source.sample request.index) (preparation.request_inside request)
        (Preparation.localizationRadius_positive target) (preparation.request_residualSmall request) })
    (paid : Refinement (preparation.roots.get localized.val.owner.owner) (max 0 1))
    (paidSame : paid = Refinement.ofTarget (preparation.roots.get localized.val.owner.owner)
      (max 0 1) (((target / 4) / 4) / 4)
      (Order.Field.div_pos_direct (Order.Field.div_pos_direct
        (Order.Field.div_pos_direct request.positive (by decide)) (by decide)) (by decide))) :
    { value : Sequence.Selection.Nearby preparation.candidates (preparation.source.sample request.index) target //
      value = request.locate } := by
  let nearby := Assignment.nearbyFromOwnerPaid input preparation.boxes.isolation preparation.roots
    (preparation.source.sample request.index) request.positive
    (Preparation.localizationRadius_small request.positive) localized.val paid paidSame
  refine ⟨nearby, ?_⟩
  have same := Assignment.nearbyFromOwnerPaid_eq input preparation.boxes.isolation preparation.roots
    (preparation.source.sample request.index) request.positive
    (Preparation.localizationRadius_small request.positive) localized.val paid paidSame
  exact same.trans ((congrArg (fun assigned => Assignment.nearby input preparation.boxes.isolation preparation.roots
    (preparation.source.sample request.index) request.positive
    (Preparation.localizationRadius_small request.positive) assigned) localized.property).trans
      (preparation.request_locate_eq request).symm)

/-- The paid cache chain retains the complete original localization, rather than only its owner index. -/
example
    (localized : { value : Residual.Global.Assignment.AssignedResult input
      (preparation.source.sample request.index) (Preparation.localizationRadius target) preparation.boxes.isolation //
      value = Residual.Global.Assignment.assignInsideUsing input preparation.boxes preparation.support
        (preparation.source.sample request.index) (preparation.request_inside request)
        (Preparation.localizationRadius_positive target) (preparation.request_residualSmall request) })
    (paid : Refinement (preparation.roots.get localized.val.owner.owner) (max 0 1))
    (paidSame : paid = Refinement.ofTarget (preparation.roots.get localized.val.owner.owner)
      (max 0 1) (((target / 4) / 4) / 4)
      (Order.Field.div_pos_direct (Order.Field.div_pos_direct
        (Order.Field.div_pos_direct request.positive (by decide)) (by decide)) (by decide))) :
    (nearbyFromCaches preparation request localized paid paidSame).val = request.locate :=
  (nearbyFromCaches preparation request localized paid paidSame).property

/-- Independent starts consume the authenticated nearby result and retain the original selected comparison. -/
example (selection : Preparation.Selection preparation) (left right : Nat) (target : Rational)
    (positive : 0 < target)
    (request : Sequence.Selection.Coverage.Request preparation.coverage (max left selection.anchor.index)
      (min (preparation.separated.gap / 16) (target / 8)))
    (nearby : { value : Sequence.Selection.Nearby preparation.candidates
      (preparation.source.sample request.index) (min (preparation.separated.gap / 16) (target / 8)) //
      value = request.locate }) :
    selection.compareFromNearby left right target positive request nearby =
      selection.equivalent.compare left right target positive :=
  selection.compareFromNearby_eq left right target positive request nearby

end TestPurelib.Riemann.RootLocalizationRequest
