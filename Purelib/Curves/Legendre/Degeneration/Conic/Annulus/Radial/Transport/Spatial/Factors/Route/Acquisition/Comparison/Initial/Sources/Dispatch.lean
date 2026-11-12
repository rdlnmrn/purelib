module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial.Sources
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
import Purelib.Data.List.Membership
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Sources.Visits
import Purelib.Data.Fin
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Actual original factor origins at retained paid physical source occurrences

The First operation reads the original ordinary Fold. The Second operation
reads the same stored cross-segment Entry, preserving its preceding terminal
Reading/Samples on the first child. Actual Parents centers are transported
only by the original whole traced_prepared_eq. No source or factor query,
request, observation or preparation factory is replayed. Existing operational
comparison machinery constructs the required certificates on those same inputs.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold

namespace Route.Acquisition.Comparison.Initial

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (CenterStates centeredEdges centeredEdges_point_zero CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.RootContinuation
open Segment.Reading.Payment

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {entry : Initial source}
variable {middle finish : Canonical}
variable {head : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
  (Spatial.coordinate site parameter 2 quarter positive reference) middle}
variable {headWithin : head.WithinAmbient} {headFactors : Segment budgets head headWithin}
variable {headPaid : CoveredTracedPath.Acquisition.Segment (segment := head) (within := headWithin)
  (owner := entry.owner) (widthRequest anchor head)}
variable {second : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) middle finish}
variable {secondWithin : second.WithinAmbient} {secondFactors : Segment budgets second secondWithin}
variable {secondPaid : CoveredTracedPath.Acquisition.Segment (segment := second) (within := secondWithin)
  (owner := headPaid.traced.finishOwner) (widthRequest anchor second)}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {sheet : Fin 2} {count floor : Nat}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace First

variable (retained : First entry headFactors headPaid)
variable (parents : CoveredTracedPath.Acquisition.Segment.Parents (curve := Fibre.frameCurve frame)
  basis sheet count headPaid)
variable (index : Fin parents.covered.parents.length)

/-- The ordinary Fold's original source origin in the existing two-owner SourceAt family.

The previous alternative is the SAME retained initial Reading. The getter
below always returns its actual current Reading; no cross-segment Entry or
additional Reading is constructed for this ordinary first-edge case.
-/
@[expose] def SourceAt :=
  Entry.Cache.SourceAt (frame := frame) (basis := basis) (sheet := sheet) (completed := headFactors)
    retained.1.val parents.acquiredCenters (parents.acquiredIndex index)

/-- Read the actual first-edge origin with its complete unchanged Samples and existing signed query witness. -/
def sourceAt : SourceAt retained parents index := by
  let reading := sourceReading retained parents index
  let samples := sourceSamples retained parents index
  have names := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    parent.edge.rootName 0 parent.edge.baseInside) (parents.acquiredParent_eq index)
  exact Sum.inr ⟨reading, samples, NamedEquivalent.transport names rfl
    (sourceEquivalent retained parents index)⟩

/-- The actual first-edge origin retains the literal original moving child's physical point. -/
theorem sourceAt_point_eq :
    Entry.Cache.SourceAt.point retained.1.val (sourceAt retained parents index) =
      (parents.covered.parents[index.val]'index.isLt).edge.point 0 := by
  unfold sourceAt
  exact sourcePoint_eq parents index

end First

namespace Cache

variable (entry : Initial source)

/-- The actual retained ordinary or corner source-origin family at the SAME original physical Segment and child.

Only the original zero/one/two-edge path shape and finite outer position
select a family. The second edge retains its original preceding terminal
Reading as an index. No dummy current-segment Reading is introduced. -/
@[expose] def SourceAt : {finish : Canonical} →
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
    Type 1 := by
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
            exact fun child => First.SourceAt retained kept.1 child
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid retained kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun child => First.SourceAt retained.1 kept.1 child
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun child => Entry.Cache.SourceAt
                    (frame := frame) (basis := basis) (sheet := sheet) (completed := _factors.2.1.val)
                    (Second.terminal entry retained.2).1 kept.2.2.1.acquiredCenters
                    (kept.2.2.1.acquiredIndex child)
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

/-- Read the original cached origin at the literal selected physical source occurrence without replaying a producer. -/
@[expose] def sourceAt : {finish : Canonical} →
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
    SourceAt entry path within factors paid retained kept outer child := by
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
            exact fun child => First.sourceAt retained kept.1 child
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid retained kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun child => First.sourceAt retained.1 kept.1 child
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun child => Second.sourceAt retained.2 kept.2.2.1 child
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

namespace SourceAt

/-- Read the SAME source origin point, preserving the preceding segment at a corner. -/
@[expose] def point : {finish : Canonical} →
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
    (_origin : SourceAt entry path within factors paid retained kept outer child) → Canonical := by
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
            exact fun _child origin => Entry.Cache.SourceAt.point retained.1.val origin
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid retained kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun _child origin => Entry.Cache.SourceAt.point retained.1.1.val origin
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun _child origin =>
                    Entry.Cache.SourceAt.point (Second.terminal entry retained.2).1 origin
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

/-- Read the identical full-cubic factor product channel of the original selected source origin. -/
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
    (_origin : SourceAt entry path within factors paid retained kept outer child) → CoherentNamed := by
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
            exact fun _child origin => Entry.Cache.SourceAt.channel retained.1.val origin
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid retained kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun _child origin => Entry.Cache.SourceAt.channel retained.1.1.val origin
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun _child origin =>
                    Entry.Cache.SourceAt.channel (Second.terminal entry retained.2).1 origin
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

/-- Read the SAME OLD product observation, including its actual original state, requests and radius. -/
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
    (origin : SourceAt entry path within factors paid retained kept outer child) →
      Approximation.Gaussian.Equivalence.Observation.Reading
        (channel entry path within factors paid retained kept outer child origin) := by
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
            exact fun _child origin => Entry.Cache.SourceAt.product retained.1.val origin
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid retained kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun _child origin => Entry.Cache.SourceAt.product retained.1.1.val origin
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun _child origin =>
                    Entry.Cache.SourceAt.product (Second.terminal entry retained.2).1 origin
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

/-- Read the original signed comparison from the literal child query to that SAME origin channel.

The only transport is the original whole acquired/traced subdivision law
retained by Parents. It changes neither Reading nor Samples. -/
def equivalent : {finish : Canonical} →
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
    (origin : SourceAt entry path within factors paid retained kept outer child) →
      NamedEquivalent ((((Physical.Spine.Sources.segmentAt
        (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).parents.covered.parents[child.val]'child.isLt).edge.rootName 0
        ((Physical.Spine.Sources.segmentAt
        (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).parents.covered.parents[child.val]'child.isLt).edge.baseInside))
        (channel entry path within factors paid retained kept outer child origin).name := by
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
            intro child origin
            have same := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
              parent.edge.rootName 0 parent.edge.baseInside) (kept.1.acquiredParent_eq child)
            exact NamedEquivalent.transport same.symm rfl
              (Entry.Cache.SourceAt.equivalent retained.1.val origin)
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid retained kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                intro child origin
                have same := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
                  parent.edge.rootName 0 parent.edge.baseInside) (kept.1.acquiredParent_eq child)
                exact NamedEquivalent.transport same.symm rfl
                  (Entry.Cache.SourceAt.equivalent retained.1.1.val origin)
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  intro child origin
                  have same := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
                    parent.edge.rootName 0 parent.edge.baseInside) (kept.2.2.1.acquiredParent_eq child)
                  exact NamedEquivalent.transport same.symm rfl
                    (Entry.Cache.SourceAt.equivalent (Second.terminal entry retained.2).1 origin)
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

end SourceAt

/-- The actual selected factor origin has the literal original moving child point, including the second-edge corner. -/
theorem sourceAt_point_eq : {finish : Canonical} →
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
    SourceAt.point entry path within factors paid retained kept outer child
        (sourceAt entry path within factors paid retained kept outer child) =
      ((Physical.Spine.Sources.segmentAt
        (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).parents.covered.parents[child.val]'child.isLt).edge.point 0 := by
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
            exact fun child => First.sourceAt_point_eq retained kept.1 child
          | following empty => exact Fin.elim0 empty
      | cons _second rest =>
          cases rest with
          | nil _finish =>
              intro _within _factors _paid retained kept outer
              cases outer using Data.Fin.casesDependent with
              | first =>
                exact fun child => First.sourceAt_point_eq retained.1 kept.1 child
              | following next =>
                cases next using Data.Fin.casesDependent with
                | first =>
                  exact fun child => Second.sourcePoint_eq retained.2 kept.2.2.1 child
                | following empty => exact Fin.elim0 empty
          | cons _third _tail =>
              intro _within _factors _paid retained _kept _outer
              exact nomatch retained

section Selected

variable {finish : Canonical}
variable (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
  (Spatial.coordinate site parameter 2 quarter positive reference) finish)
variable (within : path.WithinAmbient) (factors : Path budgets path within)
variable (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
  path within entry.owner)
variable (retained : Cache entry path within factors paid)
variable (kept : Physical.Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets)
  (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid)
variable (outer : Fin (Physical.Spine.Sources.parentWords
  (fun {_start _finish} segment => widthRequest anchor segment) path within entry.owner paid kept).length)
variable (child : Fin (Physical.Spine.Sources.segmentAt
  (fun {_start _finish} segment => widthRequest anchor segment)
  path within entry.owner paid kept outer).parents.covered.parents.length)

/-- The SAME actual origin visits the original Route's half-open image using its retained physical Mesh. -/
theorem sourceAt_halfOpen : path.HalfOpen
    (SourceAt.point entry path within factors paid retained kept outer child
        (sourceAt entry path within factors paid retained kept outer child)) := by
  have original := Physical.Spine.Sources.segmentAt_halfOpen
    (fun {_start _finish} segment => widthRequest anchor segment)
    path within entry.owner paid kept outer child
  exact Eq.mpr (congrArg (fun point => path.HalfOpen point)
    (sourceAt_point_eq entry path within factors paid retained kept outer child)) original

/-- Compare the SAME old local PreparedParent sample to its literal retained ordinary-or-corner factor origin.

Both original sample owners remain inputs. This composes the original
prepared sample/query comparison with the actual cached signed factor
comparison; it observes neither source again.
-/
def sourceSampleEquivalent :
    NamedEquivalent
      ((Physical.Spine.Sources.segmentAt
        (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).prepared.entry child).firstSample.certificate.value.name
      (SourceAt.channel entry path within factors paid retained kept outer child
        (sourceAt entry path within factors paid retained kept outer child)).name :=
  ((Physical.Spine.Sources.segmentAt
        (fun {_start _finish} segment => widthRequest anchor segment)
        path within entry.owner paid kept outer).prepared.entry child).firstQueryEquivalent.symm.trans
    (SourceAt.equivalent entry path within factors paid retained kept outer child
      (sourceAt entry path within factors paid retained kept outer child))

end Selected

end Cache

end Route.Acquisition.Comparison.Initial

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

end
