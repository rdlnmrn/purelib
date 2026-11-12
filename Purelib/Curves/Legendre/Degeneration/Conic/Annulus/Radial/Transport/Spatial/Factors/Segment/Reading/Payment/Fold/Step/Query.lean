module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Step
public import Purelib.Riemann.Integration.PreparedConstantModels.Query.Product
public import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Actual interior query agreement on a retained paid physical step

The old factor source, prepared request and complete Step comparison are
retained. The affine query fraction pays a subwidth of the original accepted
step. Actual new interior factor observations use their own retained
requests; original trace fit and width fit derive the whole sum payment.
The returned relation concerns the literal old direct-query Owner, not an
assumed common root or a replacement physical path.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment.Fold.Step

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Owner Endpoint StepRequest CachedSource parameterAt)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (edgeOfStep)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current owner request}
variable {first : Reading completed current.parameter current.inside}
variable {firstSamples : RequestedSamples (anchor := anchor) first}
variable {sourceAgreement : SourceAgreement (owner := owner) first}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current owner request).track.initial.clearance.bound}
variable {left right : Endpoint} {trace : PreparedTraceBudget segment left right}
variable {requestFit : request.rootDiameter ≤ trace.rootDiameter}
variable {width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance}

/-- An actual unit fraction's source-to-query squared width is paid by the SAME retained original step width. -/
theorem query_width_le (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction) :
    (current.parameter - parameterAt current request fraction) ^ 2 ≤
      (current.parameter - request.endpoint.parameter) ^ 2 := by
  have fractionSquare : fraction ^ 2 ≤ (1 : Fraction.Rational) := by
    have bound := Arithmetic.pow_le_pow_direct inside.1 inside.2 2
    exact bound.trans_eq (of_decide_eq_true rfl)
  rewrite [PreparedSheetContinuation.parameterAt_eq_affine]
  have identity : (current.parameter -
      (current.parameter + fraction * (request.endpoint.parameter - current.parameter))) ^ 2 =
      fraction ^ 2 * (current.parameter - request.endpoint.parameter) ^ 2 := by ring1
  rewrite [identity]
  exact (Arithmetic.mul_le_mul_of_nonneg_right_direct fractionSquare
    (Arithmetic.sq_nonneg_direct _)).trans_eq (Fraction.Field.one_mul _)

variable (step : Step (cached := cached) first firstSamples sourceAgreement small trace requestFit width)
variable {fraction : Fraction.Rational} {inside : FixedRootBoxPath.Inside fraction}
variable (ordered : current.parameter ≤ request.endpoint.parameter)
variable {interior : Reading completed (parameterAt current request fraction)
  (PreparedSheetContinuation.parameterAt_inside current request ordered fraction inside)}
variable (samples : RequestedSamples (anchor := anchor) interior)

/-- Original old source/prepared observations and actual interior factor requests pay the signed query sum bound.

The cached prepared diameter is paid by the original Trace request. The old
source radius and original prepared request retain their complete caches.
The current interior's two residual requests and the actual affine subwidth
pay movement; no endpoint request or old observation is retagged.
-/
theorem query_payment_le : CachedSource.advancePayment firstSamples.samples.product step.observed.reading
    (comparisonTarget anchor).tolerance cached.preparedOwner.track.initial.box.diagonalSq
    (productMovement (time := current.parameter) (lastTime := parameterAt current request fraction)
      (anchor := anchor) (segment := segment) (firstUnit := firstSamples.requests.first)
      (firstNormal := firstSamples.requests.last) (lastUnit := samples.requests.first)
      (lastNormal := samples.requests.last)) ≤ floor anchor := by
  have comparison := firstSamples.comparison_bound_le step.observed
  have diameter := Clearance.prepared_diameter_le anchor segment within trace current owner request cached requestFit
  have localWidth := (query_width_le (current := current) (request := request) fraction inside).trans width
  have movement := firstSamples.movement_le samples localWidth
  have paid := Arithmetic.add_le_add_direct
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct comparison
        (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 4))
      (Arithmetic.mul_le_mul_of_nonneg_left_direct diameter
        (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 4)))
    (Arithmetic.mul_le_mul_of_nonneg_left_direct movement
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2))
  exact paid.trans_eq (by
    change 4 * (floor anchor / 16) + 4 * (floor anchor / 16) + 2 * (floor anchor / 4) = floor anchor
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    calc
      _ = (4 * (16 : Fraction.Rational)⁻¹ + 4 * (16 : Fraction.Rational)⁻¹ +
          2 * (4 : Fraction.Rational)⁻¹) * floor anchor := by ring1
      _ = _ := by
        rewrite [show (4 * (16 : Fraction.Rational)⁻¹ + 4 * (16 : Fraction.Rational)⁻¹ +
          2 * (4 : Fraction.Rational)⁻¹) = 1 from of_decide_eq_true rfl]
        exact Fraction.Field.one_mul _)

variable {frame : Paths.Frame parameter}
variable {basis : Curves.Hyperelliptic.Differentials.Basic.Differential 1} {sheet : Fin 2}

/-- The actual original accepted edge's direct query agrees with the SAME interior full factor product.

The query is supplied as its retained original cache, and the Step contributes
its existing source comparison rather than executing another comparison.
Both interior factor observations remain those supplied in Samples. Exact
original affine-parameter readback identifies only the common target point;
all sign evidence comes from original refinement, residual and width bounds.
-/
def queryEquivalent
    (query : PreparedEdge.Query
      (edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small sheet)
      fraction inside)
    (queryRoot : CertifiedSquareRoot.Certificate ((Fibre.frameCurve frame).polynomial.eval
      ((edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small sheet).point
        fraction)))
    (queryRoot_eq : queryRoot = query.owner.certificate query.owner.parameterNonzero) :
    NamedEquivalent
      ((edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small
        sheet).rootName fraction inside) interior.values.value.name := by
  let sourceAgreed := sourceAgreement
  unfold SourceAgreement SquareRootTrackEquivalence.ownerRootName at sourceAgreed
  have compared : Equivalence.Observation.Comparison firstSamples.samples.product step.observed.reading
      (comparisonTarget anchor).tolerance :=
    CachedSource.AdvanceAgreement.comparison
      (cached := cached) (within := within) (small := cachedSmall (cached := cached) small)
      (sourceChannel := first.values.value) (targetChannel := step.last.values.value)
      (sourceReading := firstSamples.samples.product) (targetReading := step.lastSamples.samples.product)
      (sourceAgreement := sourceAgreed) (root := step.root) (root_eq := step.root_eq)
      (preparedReading := step.observed.reading) (comparisonTarget := (comparisonTarget anchor).tolerance)
      (comparisonPositive := (comparisonTarget anchor).positive) step.compared
  have pointEq := PreparedSheetContinuation.pointAt_parameterAt segment within current request fraction
  have targetSquare : SquareRootProvenance.SquareIdentity interior.values.value
      ((Fibre.frameCurve frame).polynomial.eval
        ((edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small
          sheet).point fraction)) :=
    NamedEquivalent.transport rfl (congrArg Name.Basic.Named.exact
      (congrArg (Paths.polynomial parameter).eval pointEq)) interior.values.square
  exact query.productEquivalent queryRoot queryRoot_eq firstSamples.samples.product samples.samples.product
    step.root_eq step.observed.reading
    compared targetSquare (floor anchor) (floor_positive anchor)
    (firstSamples.samples.candidate_normSq_lower firstSamples.samples.product.possible)
    (productMovement (time := current.parameter) (lastTime := parameterAt current request fraction)
      (anchor := anchor) (segment := segment) (firstUnit := firstSamples.requests.first)
      (firstNormal := firstSamples.requests.last) (lastUnit := samples.requests.first)
      (lastNormal := samples.requests.last))
    (fun possible => firstSamples.samples.candidates_distance_le samples.samples
      firstSamples.samples.product.possible possible)
    (query_payment_le (inside := inside) step ordered samples)

end Reading.Payment.Fold.Step

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
