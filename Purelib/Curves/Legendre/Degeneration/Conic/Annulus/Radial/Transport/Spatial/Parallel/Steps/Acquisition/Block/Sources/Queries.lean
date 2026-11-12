module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block.Sources.Occurrence
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial.Queries
public import Purelib.Riemann.Integration.PreparedConstantModels.Query.Transport
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Interior factor queries at the same retained original Block occurrence

The existing SourceOccurrence supplies the literal physical locator and
unchanged paid Route cache. Whole original parent equality transports one
supplied direct Query. One new interior Reading/Samples cache is retained
with its original factories; source preparation and paid trace are untouched.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Block

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.RootContinuation
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

namespace SourceOccurrence

variable {block sources index} (retained : SourceOccurrence block sources index)

/-- Read this SAME retained position's bounded child on its original physical Segment without another locator. -/
@[expose] def physicalChild := Spine.Sources.child geometry.route.path geometry.route.within sourceOwner
  block.paid.spine sources index retained.position

/-- The aggregate and local physical occurrence retain the SAME complete original centered parent. -/
theorem physicalParent_eq : retained.parent =
    ((Spine.Sources.selected geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position).parents.covered.parents[
        retained.physicalChild.val]'retained.physicalChild.isLt) :=
  Spine.Sources.parent_eq geometry.route.path geometry.route.within sourceOwner
    block.paid.spine sources index retained.position

/-- Transport one SAME whole direct Query to the actual local physical child, preserving its factory and Owners. -/
@[expose] def directQuery (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction)
    (query : PreparedEdge.Query retained.parent.edge fraction inside) :
    PreparedEdge.Query
      ((Spine.Sources.selected geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position).parents.covered.parents[
          retained.physicalChild.val]'retained.physicalChild.isLt).edge fraction inside :=
  PreparedEdge.Query.castEdge
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge) retained.physicalParent_eq)
    query

/-- Physical-child index transport retains the entire supplied original Query heterogeneously. -/
theorem directQuery_heq (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction)
    (query : PreparedEdge.Query retained.parent.edge fraction inside) :
    HEq (retained.directQuery fraction inside query) query :=
  PreparedEdge.Query.castEdge_heq
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge) retained.physicalParent_eq)
    query

/-- The exact original Route-query cache type at this SAME materialized aggregate source occurrence. -/
@[expose] def QueryAt (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction) :=
  Initial.Cache.QueryAt block.initial geometry.route.path geometry.route.within
    block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
    retained.physicalChild fraction inside

/-- Query the selected physical child's actual factors once, preserving the same retained occurrence and direct Query.

Only the original Route query producer runs. The complete new Reading and
RequestedSamples factories remain stored, separately from historical
SourceAt and old source observations. No Block, source, locator, factor
preparation, paid acquisition, comparison Fold or direct Query is rebuilt.
-/
def queryAt (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction)
    (query : PreparedEdge.Query retained.parent.edge fraction inside) : QueryAt retained fraction inside :=
  let direct := directQuery retained fraction inside query
  Initial.Cache.queryAt block.initial geometry.route.path geometry.route.within
    block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
    retained.physicalChild fraction inside direct

namespace QueryAt

variable {retained} {fraction : Fraction.Rational} {inside : FixedRootBoxPath.Inside fraction}
    (queried : QueryAt retained fraction inside)

/-- Read the SAME newly retained interior factor product channel, preserving both original factor Owners. -/
@[expose] def channel : CoherentNamed :=
  Initial.Cache.QueryAt.channel block.initial geometry.route.path geometry.route.within
    block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
    retained.physicalChild fraction inside queried

/-- Read the SAME actual factor product observation, including its exact requests, state and visible radius. -/
@[expose] def product : Approximation.Gaussian.Equivalence.Observation.Reading queried.channel :=
  Initial.Cache.QueryAt.product block.initial geometry.route.path geometry.route.within
    block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
    retained.physicalChild fraction inside queried

/-- The literal aggregate child query agrees with this SAME newly paid interior factor channel. -/
def equivalent : NamedEquivalent (retained.parent.edge.rootName fraction inside) queried.channel.name :=
  let names := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    parent.edge.rootName fraction inside) retained.physicalParent_eq
  NamedEquivalent.transport names.symm rfl
    (Initial.Cache.QueryAt.equivalent block.initial geometry.route.path geometry.route.within
      block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
      retained.physicalChild fraction inside queried)

/-- Exact parent transport keeps the factor Reading at the SAME aggregate child's original physical point. -/
theorem point_eq (queried : QueryAt retained fraction inside) : retained.parent.edge.point fraction =
    (Spine.Sources.selected geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position).segment.pointAt
      (Riemann.Branches.PreparedSheetContinuation.parameterAt
        ((Spine.Sources.selected geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position).parents.covered.parents[
            retained.physicalChild.val]'retained.physicalChild.isLt).edge.left
        ((Spine.Sources.selected geometry.route.path geometry.route.within sourceOwner
      block.paid.spine sources index retained.position).parents.covered.parents[
            retained.physicalChild.val]'retained.physicalChild.isLt).edge.request fraction) :=
  (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge.point fraction)
    retained.physicalParent_eq).trans
    (Initial.Cache.QueryAt.point_eq block.initial geometry.route.path geometry.route.within
      block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
      retained.physicalChild fraction inside queried)

end QueryAt

/-- A strict-fraction aggregate query has the SAME actual original Route half-open visit, including constant edges. -/
theorem query_halfOpen (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction)
    (below : fraction < 1) : geometry.route.path.HalfOpen (retained.parent.edge.point fraction) := by
  have visited := Initial.Cache.query_halfOpen block.initial geometry.route.path geometry.route.within
    block.paid.factors.path block.paid.spine block.comparison.val sources retained.position.1
    retained.physicalChild fraction inside below
  have same := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge.point fraction)
    retained.physicalParent_eq
  exact Eq.mpr (congrArg (fun point => geometry.route.path.HalfOpen point) same) visited

end SourceOccurrence

end Steps.Acquisition.Block

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
