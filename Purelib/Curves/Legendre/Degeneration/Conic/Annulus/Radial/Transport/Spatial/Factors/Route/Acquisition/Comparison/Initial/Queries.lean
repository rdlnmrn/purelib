module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Query
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly
public import Purelib.Polynomial.Geometry.ClearPath.HalfOpen
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.Acquired
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.Query
import Purelib.Data.Fin
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.List.Membership
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Newly paid interior factor queries on the same retained sharp route

The actual zero-, one- and two-edge comparison cache selects the identical
physical acquisition and stored Parents. Each requested interior Reading
and Samples is materialized once through the original factories. Direct
Queries and old factor-fold/Entry caches are consumed unchanged. Exact
whole-parent transport preserves original center and child occurrence;
no source, acquisition, advance, factor preparation or Alignment is rebuilt.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

namespace Route.Acquisition.Comparison.Initial

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.RootContinuation
open Segment.Reading.Payment

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    {positive : (0 : Fraction.Rational) < 2}
    {actual : Transport.Quarter site parameter 2 quarter positive}
    {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
    {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
    {budgets : Budgets anchor} {entry : Initial source}
    {middle finish : Canonical}
    {head : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive reference) middle}
    {headWithin : head.WithinAmbient} {headFactors : Segment budgets head headWithin}
    {headPaid : CoveredTracedPath.Acquisition.Segment (segment := head) (within := headWithin)
      (owner := entry.owner) (widthRequest anchor head)}
    {second : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) middle finish}
    {secondWithin : second.WithinAmbient} {secondFactors : Segment budgets second secondWithin}
    {secondPaid : CoveredTracedPath.Acquisition.Segment (segment := second) (within := secondWithin)
      (owner := headPaid.traced.finishOwner) (widthRequest anchor second)}
    {frame : Paths.Frame parameter} {basis : Differential 1} {sheet : Fin 2} {count floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace First

/-- Materialize one first-edge factor query on the SAME retained physical child, retaining both complete factories.

The supplied direct Query is transported only along the original whole
acquiredParent_eq. The returned entire Reading/Samples/comparison cache is
transported back along that SAME child equality, preserving its exact
physical parameter, center, source Owner and original paid Fold input.
-/
def queryAt (retained : First entry headFactors headPaid)
    (parents : CoveredTracedPath.Acquisition.Segment.Parents (curve := Fibre.frameCurve frame)
      basis sheet count headPaid)
    (index : Fin parents.covered.parents.length)
    (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction)
    (query : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge fraction inside) :
    Fold.QueryAt (completed := headFactors) (parents.covered.parents[index.val]'index.isLt) fraction inside := by
  let equal := parents.acquiredParent_eq index
  let direct := Eq.mp (congrArg (fun child : CenteredEdge (Fibre.frameCurve frame) basis =>
    PreparedEdge.Query child.edge fraction inside) equal) query
  let compared := Fold.Cache.queryAt (frame := frame) (basis := basis) (sheet := sheet)
    (completed := headFactors) headPaid.prepared.budget.trace
    (Fold.Acquisition.Initial.Result.fold (completed := headFactors) (suppliedOwner := entry.owner)
      (suppliedAgreement := Fold.Acquisition.Initial.ownerAgreement entry.owner entry.equivalent)
      (suppliedPaid := headPaid.prepared.paid) retained)
    parents.acquiredCenters (parents.acquiredIndex index) fraction inside direct
  exact Eq.mpr (congrArg (fun child : CenteredEdge (Fibre.frameCurve frame) basis =>
    Fold.QueryAt (completed := headFactors) child fraction inside) equal) compared

end First

namespace Second

/-- Materialize one second-edge interior without replacing its retained preceding terminal Reading or Samples.

The supplied Second cache still owns the actual previous terminal and
whole original corner Entry. Exact parent equality transports the supplied
direct Query and the complete new interior cache only. The pure Entry
comparison uses its unchanged preceding values on the first child and
its unchanged ordinary tail thereafter; no handoff or advance is replayed.
-/
def queryAt {firstResult : First entry headFactors headPaid}
    (retained : Second entry headFactors headPaid secondFactors secondPaid firstResult)
    (parents : CoveredTracedPath.Acquisition.Segment.Parents (curve := Fibre.frameCurve frame)
      basis sheet count secondPaid)
    (index : Fin parents.covered.parents.length)
    (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction)
    (query : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge fraction inside) :
    Fold.QueryAt (completed := secondFactors) (parents.covered.parents[index.val]'index.isLt) fraction inside := by
  let equal := parents.acquiredParent_eq index
  let direct := Eq.mp (congrArg (fun child : CenteredEdge (Fibre.frameCurve frame) basis =>
    PreparedEdge.Query child.edge fraction inside) equal) query
  let terminal := Second.terminal entry retained
  let compared := Fold.Entry.Cache.queryAt (frame := frame) (basis := basis) (sheet := sheet)
    (completed := secondFactors) terminal.1 terminal.2.1 secondPaid.prepared.budget.trace
    retained.2.val parents.acquiredCenters (parents.acquiredIndex index) fraction inside direct
  exact Eq.mpr (congrArg (fun child : CenteredEdge (Fibre.frameCurve frame) basis =>
    Fold.QueryAt (completed := secondFactors) child fraction inside) equal) compared

end Second

namespace Cache

variable (entry : Initial source)

/-- The actual original factor-query cache at the SAME selected physical Segment and child of a short paid route.

The existing zero/one/two-edge Cache and bounded outer position select
only the original factor preparation. Each result is the original Fold
QueryAt Sigma retaining one actual Reading, Samples and signed relation.
The empty route has no occurrence; a longer route has no such Cache.
-/
@[expose] def QueryAt : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive reference) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner) → (retained : Cache entry path within factors paid) →
    (kept : Physical.Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets)
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid) →
    (outer : Fin (Physical.Spine.Sources.parentWords
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid kept).length) →
    (child : Fin (Physical.Spine.Sources.segmentAt
      (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner paid kept outer).parents.covered.parents.length) →
    (fraction : Fraction.Rational) → FixedRootBoxPath.Inside fraction → Type 1 := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _retained _kept outer
      exact Fin.elim0 outer
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within factors _paid _retained kept outer
          cases outer using Data.Fin.casesDependent with
          | first =>
            exact fun child fraction inside =>
              Fold.QueryAt (completed := factors.1.val)
                (kept.1.covered.parents[child.val]'child.isLt) fraction inside
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within factors _paid _retained kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun child fraction inside =>
                  Fold.QueryAt (completed := factors.1.val)
                    (kept.1.covered.parents[child.val]'child.isLt) fraction inside
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun child fraction inside =>
                    Fold.QueryAt (completed := factors.2.1.val)
                      (kept.2.2.1.covered.parents[child.val]'child.isLt) fraction inside
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

/-- Query one actual route child once using its literal factor preparations, paid cache, Parents and direct Query.

The finite path/outer dispatch performs no preparation or acquisition.
The selected original first/second operation materializes exactly one
Reading and RequestedSamples result, preserving their whole factories.
The second-edge entry retains its original previous terminal observations.
-/
def queryAt : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive reference) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner) → (retained : Cache entry path within factors paid) →
    (kept : Physical.Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets)
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid) →
    (outer : Fin (Physical.Spine.Sources.parentWords
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid kept).length) →
    (child : Fin (Physical.Spine.Sources.segmentAt
      (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner paid kept outer).parents.covered.parents.length) →
    (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
    PreparedEdge.Query
      ((Physical.Spine.Sources.segmentAt (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).parents.covered.parents[child.val]'child.isLt).edge fraction inside →
    QueryAt entry path within factors paid retained kept outer child fraction inside := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _retained _kept outer
      exact Fin.elim0 outer
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within _factors _paid retained kept outer
          cases outer using Data.Fin.casesDependent with
          | first =>
            exact fun child fraction inside direct => First.queryAt retained kept.1 child fraction inside direct
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid retained kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun child fraction inside direct =>
                  First.queryAt retained.1 kept.1 child fraction inside direct
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun child fraction inside direct =>
                    Second.queryAt retained.2 kept.2.2.1 child fraction inside direct
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

/-- Every strict-fraction query on this SAME retained route has its actual half-open geometric visit.

Original Parents mesh strictness pays the parameter progress. Only the
literal route/outer/child cases are inspected. Fraction one is deliberately
not admitted by this lemma and must use the actual endpoint Completion.
-/
theorem query_halfOpen : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive reference) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner) → (retained : Cache entry path within factors paid) →
    (kept : Physical.Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets)
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid) →
    (outer : Fin (Physical.Spine.Sources.parentWords
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid kept).length) →
    (child : Fin (Physical.Spine.Sources.segmentAt
      (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner paid kept outer).parents.covered.parents.length) →
    (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) → fraction < 1 →
    path.HalfOpen
      (((Physical.Spine.Sources.segmentAt (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).parents.covered.parents[child.val]'child.isLt).edge.point
          fraction) := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _retained _kept outer
      exact Fin.elim0 outer
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within _factors _paid _retained kept outer
          cases outer using Data.Fin.casesDependent with
          | first =>
            exact fun child fraction inside below =>
              kept.1.child_query_halfOpen _ (List.getElem_mem child.isLt) fraction inside below
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid _retained kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                intro child fraction inside below
                have here := kept.1.child_query_halfOpen _ (List.getElem_mem child.isLt) fraction inside below
                cases here with
                | inl visited => exact Or.inl visited
                | inr impossible => exact False.elim impossible
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun child fraction inside below => Or.inr
                    (kept.2.2.1.child_query_halfOpen _ (List.getElem_mem child.isLt) fraction inside below)
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

namespace QueryAt

/-- Read the SAME actual interior factor product channel from the selected original Route query cache. -/
@[expose] def channel : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive reference) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner) → (retained : Cache entry path within factors paid) →
    (kept : Physical.Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets)
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid) →
    (outer : Fin (Physical.Spine.Sources.parentWords
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid kept).length) →
    (child : Fin (Physical.Spine.Sources.segmentAt
      (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner paid kept outer).parents.covered.parents.length) →
    (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
    (_queried : QueryAt entry path within factors paid retained kept outer child fraction inside) →
    CoherentNamed := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _retained _kept outer
      exact Fin.elim0 outer
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within _factors _paid _retained _kept outer
          cases outer using Data.Fin.casesDependent with
          | first =>
            exact fun _child _fraction _inside queried => (Fold.QueryAt.reading queried).values.value
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid _retained _kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun _child _fraction _inside queried => (Fold.QueryAt.reading queried).values.value
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun _child _fraction _inside queried => (Fold.QueryAt.reading queried).values.value
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

/-- Read the SAME actual product observation, preserving its requests, state, value and visible radius. -/
@[expose] def product : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive reference) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner) → (retained : Cache entry path within factors paid) →
    (kept : Physical.Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets)
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid) →
    (outer : Fin (Physical.Spine.Sources.parentWords
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid kept).length) →
    (child : Fin (Physical.Spine.Sources.segmentAt
      (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner paid kept outer).parents.covered.parents.length) →
    (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
    (queried : QueryAt entry path within factors paid retained kept outer child fraction inside) →
    Approximation.Gaussian.Equivalence.Observation.Reading
      (channel entry path within factors paid retained kept outer child fraction inside queried) := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _retained _kept outer
      exact Fin.elim0 outer
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within _factors _paid _retained _kept outer
          cases outer using Data.Fin.casesDependent with
          | first =>
            exact fun _child _fraction _inside queried => (Fold.QueryAt.samples queried).samples.product
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid _retained _kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun _child _fraction _inside queried => (Fold.QueryAt.samples queried).samples.product
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun _child _fraction _inside queried => (Fold.QueryAt.samples queried).samples.product
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

/-- Read the retained signed relation from the SAME original physical child query to its actual factor channel. -/
@[expose] def equivalent : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive reference) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner) → (retained : Cache entry path within factors paid) →
    (kept : Physical.Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets)
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid) →
    (outer : Fin (Physical.Spine.Sources.parentWords
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid kept).length) →
    (child : Fin (Physical.Spine.Sources.segmentAt
      (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner paid kept outer).parents.covered.parents.length) →
    (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
    (queried : QueryAt entry path within factors paid retained kept outer child fraction inside) →
    NamedEquivalent
      (((Physical.Spine.Sources.segmentAt (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).parents.covered.parents[child.val]'child.isLt).edge.rootName
        fraction inside)
      (channel entry path within factors paid retained kept outer child fraction inside queried).name := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _retained _kept outer
      exact Fin.elim0 outer
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within _factors _paid _retained _kept outer
          cases outer using Data.Fin.casesDependent with
          | first =>
            exact fun _child _fraction _inside queried => Fold.QueryAt.equivalent queried
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid _retained _kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun _child _fraction _inside queried => Fold.QueryAt.equivalent queried
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun _child _fraction _inside queried => Fold.QueryAt.equivalent queried
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

/-- The retained query's factor Reading occurs at the SAME literal physical child point on its selected Segment. -/
theorem point_eq : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive reference) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner) → (retained : Cache entry path within factors paid) →
    (kept : Physical.Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets)
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid) →
    (outer : Fin (Physical.Spine.Sources.parentWords
      (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid kept).length) →
    (child : Fin (Physical.Spine.Sources.segmentAt
      (fun {_start _finish} segment => widthRequest anchor segment)
      path within entry.owner paid kept outer).parents.covered.parents.length) →
    (fraction : Fraction.Rational) → (inside : FixedRootBoxPath.Inside fraction) →
    (_queried : QueryAt entry path within factors paid retained kept outer child fraction inside) →
    ((Physical.Spine.Sources.segmentAt (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).parents.covered.parents[child.val]'child.isLt).edge.point fraction =
      (Physical.Spine.Sources.segmentAt (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).segment.pointAt
          (Riemann.Branches.PreparedSheetContinuation.parameterAt
            ((Physical.Spine.Sources.segmentAt (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).parents.covered.parents[child.val]'child.isLt).edge.left
            ((Physical.Spine.Sources.segmentAt (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).parents.covered.parents[child.val]'child.isLt).edge.request
            fraction) := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _retained _kept outer
      exact Fin.elim0 outer
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within _factors _paid _retained _kept outer
          cases outer using Data.Fin.casesDependent with
          | first =>
            exact fun _child _fraction _inside queried => Fold.QueryAt.point_eq queried
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid _retained _kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun _child _fraction _inside queried => Fold.QueryAt.point_eq queried
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun _child _fraction _inside queried => Fold.QueryAt.point_eq queried
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

end QueryAt

end Cache

end Route.Acquisition.Comparison.Initial

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

end
