module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Step.Query
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Samples.Arithmetic
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Spatial
public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Channels
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fine.Coefficient
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # The actual prepared source query on a literal paid subdivision head

The original centered head is the existing edgeOfStep with its supplied
center cache. One old six-channel query bundle retains its raw factory law.
The original patch comparison and actual paid Step comparison identify its
signed root at the identical physical fraction. The numerical comparison
consumes the supplied same-state full-root arithmetic cache unchanged.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment.Fold.Step

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Owner Endpoint StepRequest CachedSource parameterAt)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (edgeOfStep CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Integration.Path.Primitive.PrimitiveEdge

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {span : Data.Rat.Interval.Bounds}
variable {referenceInside : FixedRootBoxPath.Inside span.lower}
variable {source : Transport.Reading actual span.lower referenceInside} {anchor : Parameter.Anchor source.lift}
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
variable (step : Step (cached := cached) first firstSamples sourceAgreement small trace requestFit width)
variable (ordered : current.parameter ≤ request.endpoint.parameter)
variable {fraction : Fraction.Rational} {inside : FixedRootBoxPath.Inside fraction}
variable {interior : Reading completed (parameterAt current request fraction)
  (PreparedSheetContinuation.parameterAt_inside current request ordered fraction inside)}
variable (samples : RequestedSamples (anchor := anchor) interior)
variable {frame : Paths.Frame parameter}
variable {basis : Curves.Hyperelliptic.Differentials.Basic.Differential 1} {sheet : Fin 2}
variable {center : PreparedEdge.CenterState
  (edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small sheet)}
variable {patch : PreparedPatch
  (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small sheet,
    center⟩ : CenteredEdge (Fibre.frameCurve frame) basis)}
variable {count floor : Nat}
variable {covered : (patch.neighborhood count).box.Contains
  ((edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small sheet).point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable (prepared : Jets.Source.Cell.PreparedParent patch count floor covered targets)
variable (observed : Jets.Source.CellModels.Observations frame
  (Jets.Source.Cell.PreparedParent.liftedCell
    (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small sheet,
      center⟩ : CenteredEdge (Fibre.frameCurve frame) basis)) prepared.preparation.cell.models
  prepared.preparation.query.requests fraction)
variable (observed_eq : observed = prepared.preparation.query.observe frame fraction inside.1 inside.2)
variable (query : PreparedEdge.Query
  (edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small sheet)
  fraction inside)
variable (queryRoot : CertifiedSquareRoot.Certificate ((Fibre.frameCurve frame).polynomial.eval
  ((edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small sheet).point
    fraction)))
variable (queryRoot_eq : queryRoot = query.owner.certificate query.owner.parameterNonzero)

/-- Each old raw source channel agrees with the actual retained two-factor product at the SAME physical point. -/
def sourceQueryEquivalent (index : Fin 6) :
    NamedEquivalent interior.values.value.name (observed.channel index).algebraic.sheetValue.value.name := by
  have product := queryEquivalent step ordered samples query queryRoot queryRoot_eq
  have raw := prepared.querySampleEquivalent fraction inside observed.retained.sample query
  have name := prepared.preparation.query.channel_root_name frame fraction inside.1 inside.2
    observed observed_eq index
  exact NamedEquivalent.transport rfl name.symm (product.symm.trans raw)

/-- The actual old source observation and actual interior factor channel use the identical physical point. -/
theorem sourceQueryPoint (index : Fin 6) : segment.pointAt (parameterAt current request fraction) =
    (observed.channel index).algebraic.point :=
  (PreparedSheetContinuation.pointAt_parameterAt segment within current request fraction).trans
    ((prepared.queryPoint_eq fraction).symm.trans (observed.channel_point index).symm)

variable {index : Fin 6} {accuracy : AccuracyRequest}
variable {retained : Samples.Root samples.samples}
variable (arithmetic : Samples.Arithmetic retained (Jets.Specification.Table.forms parameter index) accuracy)

/-- Compare one old literal source polynomial to the actual original arithmetic cache without a supplied root relation.

The original Step and patch comparisons derive signed agreement. The
source observation bundle, direct-query Owner/certificate and original
factor/root/arithmetic caches remain exactly the supplied retained inputs.
-/
def compareSourceQuery :
    Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation.ArithmeticComparison
      (observed.channel index) arithmetic.numeric.original arithmetic.identity :=
  arithmetic.compare (observed.channel index) (sourceQueryPoint ordered prepared observed index)
    (retained.equivalent.symm.trans
      (sourceQueryEquivalent step ordered samples prepared observed observed_eq query queryRoot queryRoot_eq index))

variable {data : Waist.Differential.Bounds.Data site parameter
  (Jets.Specification.Table.forms parameter index)}
variable (bounds : Coefficient.Bounds data anchor) {sourceAccuracy : AccuracyRequest}
variable (old : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot sourceAccuracy)

include step ordered observed observed_eq query queryRoot queryRoot_eq

/-- The literal old source polynomial pays its full pointwise discrepancy from the old curved scalar internally.

The SAME old raw bundle, Step, direct query/certificate, factor requests and
new arithmetic cache are consumed. The comparison is constructed above
from their original geometry; no coefficient or final sample inequality is
an input, and every old visible radius remains in the computed payment.
-/
theorem sourcePolynomial_error_le :
    Data.Gaussian.Norm.Basic.normSq
      (Primitive.reading (site := site) (Jets.Specification.Table.forms parameter index)
        quarter span.lower old.reading -
        Polynomial.Ascending.Gaussian.Evaluation.eval
          (prepared.preparation.cell.models.cell index).polynomial ⟨fraction, 0⟩) ≤
      arithmetic.polynomialBound (sourceAccuracy := sourceAccuracy)
        (cell := prepared.preparation.cell.models.cell index) bounds :=
  arithmetic.polynomial_error_le (observed.channel index) bounds old
    (compareSourceQuery step ordered samples prepared observed observed_eq query queryRoot queryRoot_eq arithmetic)

variable (model : Differential.Cells.Model data source sourceAccuracy)
variable (spatial : Differential.Cells.Model.Spatial model)

/-- The actual original curved-cell scalar cache obeys the same physical-source polynomial payment.

The old Model and Spatial cache supply their literal cofactor observation
and defining scalar law. The original source, differential, chart span,
orientation and sampled state are preserved, without a new curved sample.
-/
theorem spatialPolynomial_error_le :
    Data.Gaussian.Norm.Basic.normSq
      (spatial.value - Polynomial.Ascending.Gaussian.Evaluation.eval
        (prepared.preparation.cell.models.cell index).polynomial ⟨fraction, 0⟩) ≤
      arithmetic.polynomialBound (sourceAccuracy := sourceAccuracy)
        (cell := prepared.preparation.cell.models.cell index) bounds := by
  rewrite [spatial.value_eq]
  exact sourcePolynomial_error_le step ordered samples prepared observed observed_eq query queryRoot queryRoot_eq
    arithmetic bounds model.sample

variable {target : AccuracyRequest}

/-- New fine factor observations pay a chosen free target plus the SAME old curved scalar's residual cost.

The original raw source model and observation bundle remain unchanged.
The paid Step and original patch derive the signed query comparison for
these newly acquired primary observations. Actual physical displacement
and actual source allowance payments remain the two local admissions.
-/
theorem fineSpatialPolynomial_error_le
    (fine : Payment.Fine interior bounds target)
    (root : Samples.Root fine.selected.samples)
    (fineArithmetic : Samples.Arithmetic root (Jets.Specification.Table.forms parameter index) fine.work)
    (physicalPaid : Coefficient.distance (segment := segment)
      (time := parameterAt current request fraction) ≤ fine.work.tolerance)
    (allowancePaid : (prepared.preparation.cell.models.cell index).localAllowance ≤ fine.work.tolerance) :
    Data.Gaussian.Norm.Basic.normSq
      (spatial.value - Polynomial.Ascending.Gaussian.Evaluation.eval
        (prepared.preparation.cell.models.cell index).polynomial ⟨fraction, 0⟩) ≤
      4 * (Coefficient.Allocation.sourceCoefficient bounds * sourceAccuracy.tolerance) + target.tolerance := by
  rewrite [spatial.value_eq]
  exact fine.polynomial_error_le model.sample root (observed.channel index) fineArithmetic
    (compareSourceQuery step ordered fine.selected prepared observed observed_eq query queryRoot queryRoot_eq
      fineArithmetic) physicalPaid allowancePaid

end Reading.Payment.Fold.Step

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

end
