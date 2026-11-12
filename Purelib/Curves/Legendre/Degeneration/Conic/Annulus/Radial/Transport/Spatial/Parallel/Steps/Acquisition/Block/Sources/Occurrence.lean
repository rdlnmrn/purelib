module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial.Sources.Dispatch
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly
import Purelib.Data.List.Flatten.Occurrence
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Exact factor origins of one retained actual paid Block

The original complete Block and physical source family remain inputs.
One original physical locator and its actual ordinary/corner source view
are retained with whole factory equations. The source point, full product,
old observation and signed query relation all read those SAME caches.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Block

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Factors.Segment.Reading.Payment (widthRequest)
open Factors.Route.Acquisition.Comparison (Initial)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {current target : Endpoint} {reading : ReadingAt actual current}
variable {queried : { retained : ReadingAt actual target // QueryCache actual target retained }}
variable {payment : (target.parameter - current.parameter) ^ 2 ≤
  Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable {geometry : Geometry reading queried.val regular payment}
variable {sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {agreement : InitialAgreement current reading sourceOwner}
variable (block : Block queried geometry sourceOwner agreement)
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets sourcePath stage}
variable (sources : Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets)
  (fun {_start _finish} segment => widthRequest block.anchor segment)
  geometry.route.path geometry.route.within sourceOwner block.paid.spine)
variable (index : Fin (Spine.Sources.assemble
  (fun {_start _finish} segment => widthRequest block.anchor segment)
  geometry.route.path geometry.route.within sourceOwner block.paid.spine sources).geometry.parents.length)

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The SAME original physical location and its actual ordinary/corner source origin, with both whole factory equations.

Existing Sigma/subtype containers retain only the two real lookup results.
The complete Block, paid factor Fold and source family stay original indices.
The source origin is the original SourceAt Sum, preserving the preceding
Reading/Samples on a second-edge initial child. No root or observer is built.
-/
@[expose] def SourceOccurrence :=
  Σ located : { value : Flatten.Occurrence
      (Spine.Sources.parentWords (fun {_start _finish} segment => widthRequest block.anchor segment)
        geometry.route.path geometry.route.within sourceOwner block.paid.spine sources)
      (Spine.Sources.flattenedIndex geometry.route.path geometry.route.within sourceOwner
        block.paid.spine sources index) //
    value = Spine.Sources.locate geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index },
    { origin : Initial.Cache.SourceAt block.initial geometry.route.path geometry.route.within
        block.paid.factors.path block.paid.spine block.comparison.val sources located.val.1
        (Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
          block.paid.spine sources index located.val) //
      origin = Initial.Cache.sourceAt block.initial geometry.route.path geometry.route.within
        block.paid.factors.path block.paid.spine block.comparison.val sources located.val.1
        (Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
          block.paid.spine sources index located.val) }

/-- Locate one original Block source once and read its SAME actual retained factor origin without producer replay. -/
def sourceOccurrence : SourceOccurrence block sources index :=
  let located := Spine.Sources.locate geometry.route.path geometry.route.within sourceOwner
    block.paid.spine sources index
  let origin := Initial.Cache.sourceAt block.initial geometry.route.path geometry.route.within
    block.paid.factors.path block.paid.spine block.comparison.val sources located.1
    (Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index located)
  ⟨⟨located, rfl⟩, ⟨origin, rfl⟩⟩

namespace SourceOccurrence

variable {block sources index} (retained : SourceOccurrence block sources index)

/-- Read the identical original physical Segment/child location retained by this actual source occurrence. -/
@[expose] def position := retained.1.val

/-- The retained physical position is the whole original finite locator result on this SAME occurrence. -/
theorem position_eq : retained.position =
    Spine.Sources.locate geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index := retained.1.property

/-- Read the SAME original two-owner Sum, keeping its actual preceding or current Reading and OLD Samples. -/
@[expose] def origin := retained.2.val

/-- The retained source origin is exactly its original readonly getter on those identical old caches. -/
theorem origin_eq : retained.origin =
    Initial.Cache.sourceAt block.initial geometry.route.path geometry.route.within
      block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
      (Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
        block.paid.spine sources index retained.position) := retained.2.property

/-- Read the literal physical point of this SAME old ordinary-or-corner source origin. -/
@[expose] def point : Canonical :=
  Initial.Cache.SourceAt.point block.initial geometry.route.path geometry.route.within
    block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
    (Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position) retained.origin

/-- Read the SAME original full-cubic product channel, preserving its actual factor owners and signed sheet. -/
@[expose] def channel :=
  Initial.Cache.SourceAt.channel block.initial geometry.route.path geometry.route.within
    block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
    (Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position) retained.origin

/-- Read the actual OLD product observation with its identical state, value, radius and request objects. -/
@[expose] def product :=
  Initial.Cache.SourceAt.product block.initial geometry.route.path geometry.route.within
    block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
    (Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position) retained.origin

/-- Read the literal original centered parent of this SAME aggregate source occurrence. -/
@[expose] def parent (_retained : SourceOccurrence block sources index) : CenteredEdge (Fibre.frameCurve frame) basis :=
  (Spine.Sources.assemble (fun {_start _finish} segment => widthRequest block.anchor segment)
    geometry.route.path geometry.route.within sourceOwner block.paid.spine sources).geometry.parents[index.val]'
      index.isLt

/-- The actual retained source origin has the SAME original aggregate parent's physical source point. -/
theorem point_eq : retained.point =
    ((Spine.Sources.assemble (fun {_start _finish} segment => widthRequest block.anchor segment)
      geometry.route.path geometry.route.within sourceOwner block.paid.spine sources).geometry.parents[index.val]'
        index.isLt).edge.point 0 := by
  have localPoint := Initial.Cache.sourceAt_point_eq block.initial geometry.route.path geometry.route.within
    block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
    (Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position)
  have parent := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge.point 0)
    (Spine.Sources.parent_eq geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position)
  unfold point
  rewrite [retained.origin_eq]
  exact localPoint.trans parent.symm

/-- The retained origin has the exact physical coordinate of its SAME nominal lifted source vertex. -/
theorem point_start : retained.point = (PreparedParent.startPoint retained.parent).coordinate :=
  retained.point_eq.trans retained.parent.edge.point_zero

/-- The SAME retained source occurrence lies on its original Route's actual half-open physical image. -/
theorem halfOpen : geometry.route.path.HalfOpen retained.point := by
  have visited := Initial.Cache.sourceAt_halfOpen block.initial geometry.route.path geometry.route.within
    block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
    (Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position)
  unfold point
  rewrite [retained.origin_eq]
  exact visited

/-- The SAME aggregate source query agrees with its retained full factor origin through original cache incidence. -/
def queryEquivalent :
    NamedEquivalent
      (((Spine.Sources.assemble (fun {_start _finish} segment => widthRequest block.anchor segment)
        geometry.route.path geometry.route.within sourceOwner block.paid.spine sources).geometry.parents[index.val]'
          index.isLt).edge.rootName 0
        ((Spine.Sources.assemble (fun {_start _finish} segment => widthRequest block.anchor segment)
          geometry.route.path geometry.route.within sourceOwner block.paid.spine sources).geometry.parents[index.val]'
            index.isLt).edge.baseInside)
      retained.channel.name := by
  have names := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    parent.edge.rootName 0 parent.edge.baseInside)
    (Spine.Sources.parent_eq geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position)
  exact NamedEquivalent.transport names.symm rfl
    (Initial.Cache.SourceAt.equivalent block.initial geometry.route.path geometry.route.within
      block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
      (Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
        block.paid.spine sources index retained.position) retained.origin)

/-- Compare the literal OLD aggregate PreparedParent source sample with its SAME original factor channel.

The original sample/query comparison and exact physical parent incidence
are composed. Both original owners and all observation/request data stay
inputs; no source, continuation, factor Reading or observer is replayed.
-/
def sourceSampleEquivalent :
    NamedEquivalent
      ((Spine.Sources.assemble (fun {_start _finish} segment => widthRequest block.anchor segment)
        geometry.route.path geometry.route.within sourceOwner
        block.paid.spine sources).prepared.entry index).firstSample.certificate.value.name
      retained.channel.name :=
  ((Spine.Sources.assemble (fun {_start _finish} segment => widthRequest block.anchor segment)
      geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources).prepared.entry index).firstQueryEquivalent.symm.trans retained.queryEquivalent

end SourceOccurrence

end Steps.Acquisition.Block

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
