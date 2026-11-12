module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Entry
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Step.Entry.Query
public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Fin
import Purelib.Data.List.Membership
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Interior comparisons at the unchanged paid subdivision occurrences

The original Fold and CenterStates select the actual accepted child and its
stored comparison. The ordinary case follows its exact retained tail. A
cross-segment entry consumes the previous Reading/Samples on its first
child and follows the SAME ordinary tail thereafter. No subdivision,
advance, factor observation, source preparation or center is reconstructed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment.Fold

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Owner Endpoint Subdivision parameterAt)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (CenterStates CenteredEdge centeredEdges centeredEdges_point)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    {positive : (0 : Fraction.Rational) < 2}
    {actual : Transport.Quarter site parameter 2 quarter positive}
    {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
    {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
    {budgets : Budgets anchor} {start finish : Canonical}
    {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
    {within : segment.WithinAmbient} {completed : Segment budgets segment within}
    {frame : Paths.Frame parameter} {basis : Differential 1} {sheet : Fin 2}
    {left right : Endpoint}

/-- One newly materialized interior Reading and Samples on their SAME retained physical preparation and child.

Both whole factory equations are stored next to the actual values. The
original child, fraction, signed full-cubic query relation and actual paid
factor requests remain indices. An exact physical point equation keeps
the factor Reading on that same child. Existing Sigma/Subtype containers
retain these values without a new nominal root or preparation family.
-/
@[expose] def QueryAt (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction) :=
  Σ reading : { actual : Reading completed
        (parameterAt parent.edge.left parent.edge.request fraction)
        (PreparedSheetContinuation.parameterAt_inside parent.edge.left parent.edge.request
          parent.edge.ordered fraction inside) //
      actual = Reading.build completed (parameterAt parent.edge.left parent.edge.request fraction)
        (PreparedSheetContinuation.parameterAt_inside parent.edge.left parent.edge.request
          parent.edge.ordered fraction inside) },
    Σ _samples : { actual : RequestedSamples (anchor := anchor) reading.val //
        actual = RequestedSamples.build reading.val },
      { _compared : NamedEquivalent (parent.edge.rootName fraction inside) reading.val.values.value.name //
          parent.edge.point fraction = segment.pointAt (parameterAt parent.edge.left parent.edge.request fraction) }

namespace QueryAt

variable {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {fraction : Fraction.Rational} {inside : FixedRootBoxPath.Inside fraction}
    (retained : QueryAt (completed := completed) parent fraction inside)

/-- Read the SAME whole newly queried physical factor Reading, including both original factor factory equations. -/
@[expose] def reading : Reading completed (parameterAt parent.edge.left parent.edge.request fraction)
    (PreparedSheetContinuation.parameterAt_inside parent.edge.left parent.edge.request
      parent.edge.ordered fraction inside) := retained.1.val

/-- Read the SAME whole requested Samples, original states, residual payments and full product observation. -/
@[expose] def samples : RequestedSamples (anchor := anchor) retained.reading := retained.2.1.val

/-- Read the actual signed relation from the unchanged direct-child query to this retained interior factor channel. -/
@[expose] def equivalent : NamedEquivalent (parent.edge.rootName fraction inside)
    retained.reading.values.value.name := retained.2.2.val

/-- The original factor Reading is queried at the SAME actual child point, retaining its physical segment lineage. -/
theorem point_eq (retained : QueryAt (completed := completed) parent fraction inside) :
    parent.edge.point fraction =
    segment.pointAt (parameterAt parent.edge.left parent.edge.request fraction) := retained.2.2.property

/-- The retained interior Reading is the complete original factory at the actual interpolated child parameter. -/
theorem reading_eq : retained.reading =
    Reading.build completed (parameterAt parent.edge.left parent.edge.request fraction)
      (PreparedSheetContinuation.parameterAt_inside parent.edge.left parent.edge.request
        parent.edge.ordered fraction inside) := retained.1.property

/-- The retained Samples are the complete original request-and-sampling factory on that SAME Reading. -/
theorem samples_eq : retained.samples = RequestedSamples.build retained.reading := retained.2.1.property

/-- The actual interior-query comparison on one retained centered parent and its original factor preparation.

The same Reading, requested Samples, direct Query and entire original
query-root certificate remain arguments. This exact function type is shared
by ordinary and corner-entry folds; it constructs no query or observation.
-/
@[expose] def Comparison (sourceParent : CenteredEdge (Fibre.frameCurve frame) basis) :=
  (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
  (interior : Reading completed (parameterAt sourceParent.edge.left sourceParent.edge.request fraction)
    (PreparedSheetContinuation.parameterAt_inside sourceParent.edge.left sourceParent.edge.request
      sourceParent.edge.ordered fraction inside)) →
  RequestedSamples (anchor := anchor) interior →
  (query : PreparedEdge.Query sourceParent.edge fraction inside) →
  (queryRoot : CertifiedSquareRoot.Certificate ((Fibre.frameCurve frame).polynomial.eval
    (sourceParent.edge.point fraction))) →
  queryRoot = query.owner.certificate query.owner.parameterNonzero →
  NamedEquivalent (sourceParent.edge.rootName fraction inside) interior.values.value.name

end QueryAt

namespace Cache

/-- Derive interior factor agreement at a bounded original child using the SAME already completed ordinary Fold.

Structural descent reads only the actual head Step and unchanged tail.
The supplied interior Reading/Samples and direct Query keep their own
factories and states. Their original affine fraction, request, orderedness
and whole query-certificate equation determine the comparison at that
same stored child; no desired interior relation is supplied.
-/
def queryEquivalentAt (trace : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {first : Reading completed current.parameter current.inside}
      {samples : RequestedSamples (anchor := anchor) first}
      {agreement : SourceAgreement (current := current) (owner := owner) first}
      {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision},
      Cache trace subdivision first samples agreement fits widths →
      (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
      (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length) →
      QueryAt.Comparison (completed := completed)
        ((centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt)
  | _, _, .stop _ _, _, _, _, _, _, _, _, index => Fin.elim0 index
  | _, _, .next childStart childOwner childRequest childCached ordered childSmall remaining,
      _, _, _, _, _, retained, centers, index =>
      Data.Fin.casesDependent
        (motive := fun selected => QueryAt.Comparison (completed := completed)
          ((centeredEdges (Fibre.frameCurve frame) basis sheet
            (.next childStart childOwner childRequest childCached ordered childSmall remaining)
            centers)[selected.val]'selected.isLt))
        (fun _fraction _inside _interior samples query queryRoot queryRoot_eq =>
          Step.queryEquivalent retained.1 ordered samples query queryRoot queryRoot_eq)
        (fun next => queryEquivalentAt trace (subdivision := remaining) retained.2 centers.2 next) index
termination_by structural _ _ subdivision _ _ _ _ _ _ _ _ => subdivision

/-- Query and sample one actual ordinary child interior once, retaining the unchanged Fold and direct Query inputs.

The original Reading and RequestedSamples factories each execute once.
The pure indexed comparison follows only the supplied Fold's exact head
and unchanged tail. No advance, source sample, center or subdivision is
reconstructed; the direct Query is supplied and not executed again.
-/
def queryAt (trace : PreparedTraceBudget segment left right)
    {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current owner}
    {first : Reading completed current.parameter current.inside}
    {samples : RequestedSamples (anchor := anchor) first}
    {agreement : SourceAgreement (current := current) (owner := owner) first}
    {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision}
    (retained : Cache trace subdivision first samples agreement fits widths)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
    (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length)
    (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction)
    (query : PreparedEdge.Query
      ((centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt).edge
      fraction inside) :
    QueryAt (completed := completed)
      ((centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt)
      fraction inside :=
  let parent := (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt
  let reading := Reading.build completed (parameterAt parent.edge.left parent.edge.request fraction)
    (PreparedSheetContinuation.parameterAt_inside parent.edge.left parent.edge.request
      parent.edge.ordered fraction inside)
  let samples := RequestedSamples.build reading
  let root := query.owner.certificate query.owner.parameterNonzero
  have point_eq := centeredEdges_point (Fibre.frameCurve frame) basis sheet subdivision centers
    parent (List.getElem_mem index.isLt) fraction
  let compared := queryEquivalentAt trace retained centers index fraction inside reading samples query root rfl
  ⟨⟨reading, rfl⟩, ⟨samples, rfl⟩, ⟨compared, point_eq⟩⟩

end Cache

namespace Entry.Cache

variable {previousBudgets : Budgets anchor} {previousStart previousFinish : Canonical}
    {previousSegment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) previousStart previousFinish}
    {previousWithin : previousSegment.WithinAmbient}
    {previousCompleted : Segment previousBudgets previousSegment previousWithin}
    {previousTime : Fraction.Rational} {previousInside : FixedRootBoxPath.Inside previousTime}

/-- Derive every actual interior query comparison from a retained cross-segment Entry and its SAME ordinary tail.

The first child consumes the stored preceding preparation's entire Reading,
Samples, physical incidence and actual Entry comparison. Successor children
read the identical ordinary Fold tail. No preceding observation is replaced
by a current-segment observation and no entry or advance is executed again.
-/
def queryEquivalentAt
    (first : Reading previousCompleted previousTime previousInside)
    (firstSamples : RequestedSamples (anchor := anchor) first)
    (trace : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter}
      {agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner)}
      {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision},
      Cache (completed := completed) first firstSamples trace subdivision point_eq agreement fits widths →
      (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
      (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length) →
      QueryAt.Comparison (completed := completed)
        ((centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt)
  | _, _, .stop _ _, _, _, _, _, _, _, index => Fin.elim0 index
  | _, _, .next childStart childOwner childRequest childCached ordered childSmall remaining,
      _, _, _, _, retained, centers, index =>
      Data.Fin.casesDependent
        (motive := fun selected => QueryAt.Comparison (completed := completed)
          ((centeredEdges (Fibre.frameCurve frame) basis sheet
            (.next childStart childOwner childRequest childCached ordered childSmall remaining)
            centers)[selected.val]'selected.isLt))
        (fun _fraction _inside _interior samples query queryRoot queryRoot_eq =>
          Step.Entry.Cache.queryEquivalent retained.1 ordered samples query queryRoot queryRoot_eq)
        (fun next => Fold.Cache.queryEquivalentAt trace (subdivision := remaining) retained.2 centers.2 next) index

/-- Query and sample one actual corner-entry child once without replacing the preceding retained source channel.

The interior Reading/Samples are newly materialized at this fraction.
The first child comparison still consumes the supplied previous Reading,
Samples and Entry cache, while later children use its SAME ordinary tail.
Whole factory equations retain the new observations separately from those
unchanged preceding values. No advance, Entry or direct Query is rebuilt.
-/
def queryAt
    (first : Reading previousCompleted previousTime previousInside)
    (firstSamples : RequestedSamples (anchor := anchor) first)
    (trace : PreparedTraceBudget segment left right)
    {current : Endpoint} {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current owner}
    {point_eq : previousSegment.pointAt previousTime = segment.pointAt current.parameter}
    {agreement : NamedEquivalent first.values.value.name (ownerRootName owner.parameterNonzero owner)}
    {fits : TraceFits trace subdivision} {widths : Widths (anchor := anchor) subdivision}
    (retained : Cache (completed := completed) first firstSamples trace subdivision point_eq agreement fits widths)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
    (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers).length)
    (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction)
    (query : PreparedEdge.Query
      ((centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt).edge
      fraction inside) :
    Fold.QueryAt (completed := completed)
      ((centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt)
      fraction inside :=
  let parent := (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)[index.val]'index.isLt
  let reading := Reading.build completed (parameterAt parent.edge.left parent.edge.request fraction)
    (PreparedSheetContinuation.parameterAt_inside parent.edge.left parent.edge.request
      parent.edge.ordered fraction inside)
  let samples := RequestedSamples.build reading
  let root := query.owner.certificate query.owner.parameterNonzero
  have point_eq := centeredEdges_point (Fibre.frameCurve frame) basis sheet subdivision centers
    parent (List.getElem_mem index.isLt) fraction
  let compared := queryEquivalentAt first firstSamples trace retained centers index
    fraction inside reading samples query root rfl
  ⟨⟨reading, rfl⟩, ⟨samples, rfl⟩, ⟨compared, point_eq⟩⟩

end Entry.Cache

end Reading.Payment.Fold

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

end
