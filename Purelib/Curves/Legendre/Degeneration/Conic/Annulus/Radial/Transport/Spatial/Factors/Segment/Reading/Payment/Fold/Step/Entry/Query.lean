module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Step.Entry
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Step.Query
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Interior factor comparison on the actual retained cross-segment entry

The original preceding Reading and Samples remain the first source. Its
actual Entry comparison supplies the prepared-reading relation unchanged.
An interior target Reading on the current physical preparation pays a
subwidth of the SAME accepted request. The original candidate movement
across preparations derives its signed direct-query comparison.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment.Fold.Step.Entry.Cache

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
    {positive : (0 : Fraction.Rational) < 2}
    {actual : Transport.Quarter site parameter 2 quarter positive}
    {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
    {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
    {budgets previousBudgets : Budgets anchor}
    {start finish previousStart previousFinish : Canonical}
    {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
    {previousSegment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) previousStart previousFinish}
    {within : segment.WithinAmbient} {previousWithin : previousSegment.WithinAmbient}
    {completed : Segment budgets segment within}
    {previousCompleted : Segment previousBudgets previousSegment previousWithin}
    {previousTime : Fraction.Rational} {previousInside : FixedRootBoxPath.Inside previousTime}
    {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {request : StepRequest} {cached : CachedSource segment current owner request}
    {first : Reading previousCompleted previousTime previousInside}
    {firstSamples : RequestedSamples (anchor := anchor) first}
    {point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter}
    {agreement : NamedEquivalent first.values.value.name
      (SquareRootTrackEquivalence.ownerRootName owner.parameterNonzero owner)}
    {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment current owner request).track.initial.clearance.bound}
    {left right : Endpoint} {trace : PreparedTraceBudget segment left right}
    {requestFit : request.rootDiameter ≤ trace.rootDiameter}
    {width : (current.parameter - request.endpoint.parameter) ^ 2 ≤ (widthRequest anchor segment).tolerance}

variable (retained : Cache (completed := completed) (cached := cached)
    first firstSamples point_eq agreement small trace requestFit width)
    (ordered : current.parameter ≤ request.endpoint.parameter)
    {fraction : Fraction.Rational} {inside : FixedRootBoxPath.Inside fraction}
    {interior : Reading completed (parameterAt current request fraction)
      (PreparedSheetContinuation.parameterAt_inside current request ordered fraction inside)}
    (samples : RequestedSamples (anchor := anchor) interior)

/-- The unchanged preceding product, retained prepared observation and actual interior samples pay the query sum floor.

Only the original accepted width is restricted to the supplied unit
fraction. The two separate preparation families keep their original states,
requests and product observations; no preceding Sample is replaced by a
current-segment Sample or assigned a new tolerance.
-/
private theorem query_payment_le : CachedSource.advancePayment firstSamples.samples.product retained.observed.reading
    (comparisonTarget anchor).tolerance cached.preparedOwner.track.initial.box.diagonalSq
    (productMovement (time := current.parameter) (lastTime := parameterAt current request fraction)
      (anchor := anchor) (segment := segment) (firstUnit := firstSamples.requests.first)
      (firstNormal := firstSamples.requests.last) (lastUnit := samples.requests.first)
      (lastNormal := samples.requests.last)) ≤ floor anchor := by
  have comparison := firstSamples.comparison_bound_le retained.observed
  have diameter := Clearance.prepared_diameter_le anchor segment within trace current owner request cached requestFit
  have localWidth := (Step.query_width_le (current := current) (request := request) fraction inside).trans width
  have movement := firstSamples.movement_le_from (time := current.parameter) samples localWidth
  have paid := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct comparison
        (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 4))
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct diameter
        (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 4)))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movement
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
    {basis : Curves.Hyperelliptic.Differentials.Basic.Differential 1} {sheet : Fin 2}

/-- The actual cross-segment child's retained query agrees with its separately queried interior factor product.

The original Entry supplies its complete cached source/prepared comparison.
The preceding physical point equation is used by the original cross-family
candidate movement law. Both target factor queries and samples remain the
actual supplied observations. The original query certificate and whole
Owner equation attach the derived sign to this exact direct query.
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
  let sourceAgreed := agreement
  unfold SquareRootTrackEquivalence.ownerRootName at sourceAgreed
  let compared : Equivalence.Observation.Comparison firstSamples.samples.product retained.observed.reading
      (comparisonTarget anchor).tolerance :=
    CachedSource.AdvanceAgreement.comparison
      (cached := cached) (within := within) (small := cachedSmall (cached := cached) small)
      (sourceChannel := first.values.value) (targetChannel := retained.last.values.value)
      (sourceReading := firstSamples.samples.product) (targetReading := retained.lastSamples.samples.product)
      (sourceAgreement := sourceAgreed) (root := retained.root) (root_eq := retained.root_eq)
      (preparedReading := retained.observed.reading) (comparisonTarget := (comparisonTarget anchor).tolerance)
      (comparisonPositive := (comparisonTarget anchor).positive) retained.compared
  have pointEq := PreparedSheetContinuation.pointAt_parameterAt segment within current request fraction
  let targetSquare : SquareRootProvenance.SquareIdentity interior.values.value
      ((Fibre.frameCurve frame).polynomial.eval
        ((edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small
          sheet).point fraction)) :=
    NamedEquivalent.transport rfl (congrArg Name.Basic.Named.exact
      (congrArg (Paths.polynomial parameter).eval pointEq)) interior.values.square
  exact query.productEquivalent queryRoot queryRoot_eq firstSamples.samples.product samples.samples.product
    retained.root_eq retained.observed.reading compared targetSquare (floor anchor) (floor_positive anchor)
    (firstSamples.samples.candidate_normSq_lower firstSamples.samples.product.possible)
    (productMovement (time := current.parameter) (lastTime := parameterAt current request fraction)
      (anchor := anchor) (segment := segment) (firstUnit := firstSamples.requests.first)
      (firstNormal := firstSamples.requests.last) (lastUnit := samples.requests.first)
      (lastNormal := samples.requests.last))
    (fun possible => firstSamples.samples.candidates_distance_le_from samples.samples point_eq
      firstSamples.samples.product.possible possible)
    (query_payment_le (inside := inside) retained ordered samples)

end Reading.Payment.Fold.Step.Entry.Cache

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

end
