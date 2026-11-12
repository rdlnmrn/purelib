module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
import Purelib.Riemann.Integration.PreparedConstantModels.Endpoints
import Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource.Observation
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Original full-product readings at retained moving-child occurrences

The original paid subdivision and its complete factor Fold are retained inputs.
A bounded child lookup reads the actual source Reading and Samples already
stored at that occurrence. The original edge's cached preparation comparison
and the same source agreement derive the full-cubic source-name relation.
No factor query, source preparation, observation or continuation is replayed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment.Fold.Cache

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Owner Endpoint Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (CenterStates centeredEdges edgeOfStep CenteredEdge)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {left right : Endpoint} (trace : PreparedTraceBudget segment left right)
variable {frame : Paths.Frame parameter} {basis : Differential 1} {sheet : Fin 2}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Read the same retained source Reading at one bounded original moving-child occurrence.

The recursion follows the actual subdivision and its already completed Fold.
The head returns the supplied Reading. The successor reads the identical
stored Step's target and unchanged Fold tail; it never executes Reading.build.
-/
@[expose] def sourceReadingAt (trace : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {first : Reading completed current.parameter current.inside}
      {samples : RequestedSamples (anchor := anchor) first}
      {agreement : SourceAgreement (current := current) (owner := owner) first}
      {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision},
      Cache trace subdivision first samples agreement fits widths →
      (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
      (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length) →
      Reading completed
        ((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).parameterEdge.left.parameter
        ((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).parameterEdge.left.inside
  | _, _, .stop _ _, _, _, _, _, _, _, _, index => Fin.elim0 index
  | _, _, .next _ _ _ _ _ _ remaining, first, _, _, _, _, retained, centers, index =>
      Fin.cases first (fun next => sourceReadingAt trace (subdivision := remaining) retained.2 centers.2 next) index
termination_by structural _ _ subdivision _ _ _ _ _ _ _ _ => subdivision

/-- Read the actual complete Samples of that SAME bounded original source Reading.

The old factor request objects, product observation, states and radii are
retained. Successor lookup follows only the original Step and Fold caches;
no request or observation producer is executed.
-/
@[expose] def sourceSamplesAt (trace : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {first : Reading completed current.parameter current.inside}
      {samples : RequestedSamples (anchor := anchor) first}
      {agreement : SourceAgreement (current := current) (owner := owner) first}
      {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision}
      (retained : Cache trace subdivision first samples agreement fits widths)
      (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
      (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length),
      RequestedSamples (anchor := anchor) (sourceReadingAt trace retained centers index)
  | _, _, .stop _ _, _, _, _, _, _, _, _, index => Fin.elim0 index
  | _, _, .next _ _ _ _ _ _ remaining, _, samples, _, _, _, retained, centers, index =>
      Fin.cases samples (fun next => sourceSamplesAt trace (subdivision := remaining) retained.2 centers.2 next) index
termination_by structural _ _ subdivision _ _ _ _ _ _ _ _ => subdivision

/-- Derive each original child query's signed full-cubic agreement with its actual cached source factor channel.

The head composes the original zero-query name law, the retained CachedSource
reconditioning relation and the SAME Type-valued source agreement. The tail
uses the original Step's exact target Reading, Samples and agreement.
Neither matching physical coordinates nor a sheet key determines the sign.
-/
def sourceEquivalentAt (trace : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {first : Reading completed current.parameter current.inside}
      {samples : RequestedSamples (anchor := anchor) first}
      {agreement : SourceAgreement (current := current) (owner := owner) first}
      {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision}
      (retained : Cache trace subdivision first samples agreement fits widths)
      (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
      (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length),
      NamedEquivalent
        (((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).edge.rootName 0
          ((centeredEdges (Fibre.frameCurve frame) basis sheet
          subdivision centers)[index.val]'index.isLt).edge.baseInside)
        (sourceReadingAt trace retained centers index).values.value.name
  | _, _, .stop _ _, _, _, _, _, _, _, _, index => Fin.elim0 index
  | _, _, .next current owner request cached ordered small remaining,
      _first, _, agreement, _, _, retained, centers, index =>
      Fin.cases
        (let edge := edgeOfStep (Fibre.frameCurve frame) basis segment within current owner request cached
           ordered small sheet
         have prepared : NamedEquivalent (ownerRootName owner.parameterNonzero owner)
             (ownerRootName cached.preparedOwner.parameterNonzero cached.preparedOwner) := by
           unfold ownerRootName
           exact cached.sourceEquivalent
         NamedEquivalent.transport edge.rootName_zero_eq_cached.symm rfl
           (prepared.symm.trans agreement.symm))
        (fun next => sourceEquivalentAt trace (subdivision := remaining) retained.2 centers.2 next) index
termination_by structural _ _ subdivision _ _ _ _ _ _ _ _ => subdivision

variable {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {subdivision : Subdivision segment within current owner}
variable {first : Reading completed current.parameter current.inside}
variable {samples : RequestedSamples (anchor := anchor) first}
variable {agreement : SourceAgreement (current := current) (owner := owner) first}
variable {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision}
variable (retained : Cache trace subdivision first samples agreement fits widths)
variable (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
variable (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length)
variable {count floor : Nat} {baseStart baseFinish : LiftedPoint 2}
variable {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
  ((centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt)}
variable {covered : (patch.neighborhood count).box.Contains
  (((centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt).edge.point 1)}

/-- Compare a SAME actual child's retained original source sample with the actual cached full factor Reading.

The original PreparedParent's endpoint comparison is composed with the
producer-backed Fold occurrence relation. All source requests, selected
models, endpoint observations and original center states remain inputs;
no source or factor observer is replayed and no final relation is assumed.
-/
def sourceSampleEquivalentAt (prepared : PreparedParent patch count floor covered targets) :
    NamedEquivalent prepared.firstSample.certificate.value.name
      (sourceReadingAt trace retained centers index).values.value.name :=
  prepared.firstQueryEquivalent.symm.trans (sourceEquivalentAt trace retained centers index)

end Reading.Payment.Fold.Cache

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

end
