module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Step.Source
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fine.Coefficient
import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive.Constant
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Samples.Arithmetic
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Spatial
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Channels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Actual fine-query coefficient payments on the original physical cell integral

Every family below consists of supplied complete original query caches.
The local signed comparison is derived from the paid Step and source patch,
and the fine residual/width/model payments give the polynomial estimate.
The original variable coefficient table and integral are unchanged. No
aggregate integral inequality or observation replay is an input.
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
variable {index : Fin 6}
variable {data : Waist.Differential.Bounds.Data site parameter
  (Jets.Specification.Table.forms parameter index)}
variable (bounds : Coefficient.Bounds data anchor) {sourceAccuracy : AccuracyRequest}
variable (model : Differential.Cells.Model data source sourceAccuracy)
variable (spatial : Differential.Cells.Model.Spatial model)
variable (target : AccuracyRequest)

include step

/-- Integrate the fine-query estimate on the SAME original physical source polynomial.

All original query, factor, prepared full-root and arithmetic caches are
supplied at their actual unit parameters. Their whole factory equations
are retained. The only extra payments concern actual physical width and
actual local allowance; neither is a final coefficient or integral bound.
The old curved-source residual remains an explicit, unchanged error term.
-/
theorem fineSpatialIntegral_error_le
    (interiors : (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
      Reading completed (parameterAt current request fraction)
        (PreparedSheetContinuation.parameterAt_inside current request ordered fraction inside))
    (fines : (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
      Payment.Fine (interiors fraction inside) bounds target)
    (roots : (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
      Samples.Root (fines fraction inside).selected.samples)
    (arithmetics : (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
      Samples.Arithmetic (roots fraction inside) (Jets.Specification.Table.forms parameter index)
        (fines fraction inside).work)
    (observeds : (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
      Jets.Source.CellModels.Observations frame
        (Jets.Source.Cell.PreparedParent.liftedCell
          (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small sheet,
            center⟩ : CenteredEdge (Fibre.frameCurve frame) basis)) prepared.preparation.cell.models
        prepared.preparation.query.requests fraction)
    (observeds_eq : ∀ fraction inside,
      observeds fraction inside = prepared.preparation.query.observe frame fraction inside.1 inside.2)
    (queries : (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
      PreparedEdge.Query
        (edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered small sheet)
        fraction inside)
    (queryRoots : (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
      CertifiedSquareRoot.Certificate ((Fibre.frameCurve frame).polynomial.eval
        ((edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached ordered
          small sheet).point fraction)))
    (queryRoots_eq : ∀ fraction inside,
      queryRoots fraction inside = (queries fraction inside).owner.certificate
        (queries fraction inside).owner.parameterNonzero)
    (physicalPaid : ∀ fraction inside,
      Coefficient.distance (segment := segment) (time := parameterAt current request fraction) ≤
        (fines fraction inside).work.tolerance)
    (allowancePaid : ∀ fraction inside,
      (prepared.preparation.cell.models.cell index).localAllowance ≤ (fines fraction inside).work.tolerance) :
    Data.Gaussian.Norm.Basic.normSq
      ((prepared.preparation.cell.models.cell index).integralSample -
        (prepared.preparation.cell.models.cell index).displacement * spatial.value) ≤
      2 * (4 * (Coefficient.Allocation.sourceCoefficient bounds * sourceAccuracy.tolerance) + target.tolerance) *
        Data.Gaussian.Norm.Basic.normSq (prepared.preparation.cell.models.cell index).displacement := by
  apply Integration.Polynomial.Gaussian.Cell.Primitive.integral_sub_coefficient_le
    (prepared.preparation.cell.models.cell index) spatial.value
    (4 * (Coefficient.Allocation.sourceCoefficient bounds * sourceAccuracy.tolerance) + target.tolerance)
  intro fraction inside
  exact fineSpatialPolynomial_error_le
    (step := step) (ordered := ordered) (prepared := prepared)
    (observed := observeds fraction inside) (observed_eq := observeds_eq fraction inside)
    (query := queries fraction inside) (queryRoot := queryRoots fraction inside)
    (queryRoot_eq := queryRoots_eq fraction inside) (model := model) (spatial := spatial)
    (fine := fines fraction inside) (root := roots fraction inside) (fineArithmetic := arithmetics fraction inside)
    (physicalPaid := physicalPaid fraction inside) (allowancePaid := allowancePaid fraction inside)

end Reading.Payment.Fold.Step

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

end
