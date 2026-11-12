module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation.Rows
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Distance
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Distance

/-! # Actual six-row physical source payments on the SAME retained paid Route

The common positive row request determines the chart width before queries.
The original Geometry and retained paid acquisition supply the actual edges.
Their original source-family builder's head/tail cache spine transports the
derived path payment to every literal source-model coordinate query.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation

namespace Rows

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Jets.Source.Cell.PreparedParents.Trace.Physical

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {data : (index : Fin 6) →
  Waist.Differential.Bounds.Data site parameter (Jets.Specification.Table.forms parameter index)}
variable (rows : Rows (anchor := anchor) data) (target : AccuracyRequest)

/-- The common six-row positive physical tolerance computes its sufficient original chart width before observations. -/
def chartWidthRequest : AccuracyRequest :=
  Parallel.Geometry.widthRequest site parameter (rows.commonRequest target)

/-- The original finite search computes a sufficient chart depth using the SAME common six-row work tolerance. -/
def chartWidthMinimum : Nat := Parallel.Geometry.widthMinimum site parameter (rows.commonRequest target)

variable {last : Fraction.Rational} {lastInside : FixedRootBoxPath.Inside last}
variable {targetReading : Transport.Reading actual last lastInside}
variable {payment : (last - reference) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {budgets : Budgets anchor}
variable {geometry : Parallel.Geometry source targetReading anchor.regular payment}
variable {factorRoute : Factors.Route budgets geometry}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval
  (Spatial.coordinate site parameter 2 quarter positive reference))}
variable (paid : Factors.Route.Acquisition factorRoute sourceOwner)
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets sourcePath stage}
variable (sources : Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets)
  (fun {_start _finish} segment => Segment.Reading.Payment.widthRequest anchor segment)
  geometry.route.path geometry.route.within sourceOwner paid.spine)

/-- A computed-depth-paid chart block pays every literal query of its actual retained physical source family. -/
theorem source_distanceBound
    (widthPaid : (reference - last) ^ 2 ≤ Geometric.Basic.quarterRadius 1 (rows.chartWidthMinimum target)) :
    Spine.Sources.DistanceBound (Spatial.coordinate site parameter 2 quarter positive reference)
      (rows.commonRequest target).tolerance
      (fun {_start _finish} segment => Segment.Reading.Payment.widthRequest anchor segment)
      geometry.route.path geometry.route.within sourceOwner paid.spine sources :=
  Spine.Sources.distanceBound _ _ _ _ _ _ paid.spine sources
    (geometry.route_pointBound_of_depth (rows.commonRequest target) widthPaid)

/-- The SAME whole-query payment also fits each original row's own actual Fine.work tolerance. -/
theorem source_distanceBound_row
    (widthPaid : (reference - last) ^ 2 ≤ Geometric.Basic.quarterRadius 1 (rows.chartWidthMinimum target))
    (index : Fin 6) :
    Spine.Sources.DistanceBound (Spatial.coordinate site parameter 2 quarter positive reference)
      (request (rows.get index) target).tolerance
      (fun {_start _finish} segment => Segment.Reading.Payment.widthRequest anchor segment)
      geometry.route.path geometry.route.within sourceOwner paid.spine sources :=
  Spine.Sources.distanceBound _ _ _ _ _ _ paid.spine sources
    ((geometry.route_pointBound_of_depth (rows.commonRequest target) widthPaid).mono (rows.common_le target index))

end Rows

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation

end
