module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Distance
import Purelib.Tactic.Ring

/-! # An actual paid spatial Block on one SAME old curved piece

The original scalar piece and complete cached target query remain inputs.
The actual span endpoint incidence pays the sharp Geometry, and the existing
supplied-owner Block factory prepares its actual paid Route once. The whole
original factories and exact finishOwner remain retained.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry

namespace Spatial

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods
open Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Transport.Spatial

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}
variable (piece : Piece data actual accuracy) {target : Endpoint}
variable (queried : { reading : ReadingAt actual target // QueryCache actual target reading })
variable {regular : parameter ≠ criticalValue site}
variable (sourceOwner : OwnerAt site parameter quarter positive piece.lowerEndpoint)
variable (agreement : Steps.Acquisition.InitialAgreement piece.lowerEndpoint piece.source sourceOwner)

attribute [local irreducible] Transport.Spatial.coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The actual scalar span, target incidence, sharp Geometry and complete original paid Block factory.

Both old source/target Readings remain unchanged. The target incidence is
an exact scalar endpoint law derived from the original Layer Chain, not
an owner/root equivalence. The actual paid Block obtains its original
root handoffs from the supplied sourceOwner and input agreement.
-/
@[expose] def Block : Type 1 :=
  PSigma fun _incidence : target.parameter = piece.span.upper =>
    PSigma fun payment : (target.parameter - piece.span.lower) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7 =>
      Σ geometry : { value : Geometry piece.source queried.val regular payment //
          value = Geometry.build piece.source queried.val regular payment },
        { block : Steps.Acquisition.Block
            (site := site) (parameter := parameter) (unitQuarter := quarter) (positive := positive)
            (actual := actual) (regular := regular) (current := piece.lowerEndpoint) (target := target)
            (reading := piece.source) (payment := payment)
            queried geometry.val sourceOwner agreement //
          block = Steps.Acquisition.Block.build
             (site := site) (parameter := parameter) (unitQuarter := quarter) (positive := positive)
             (actual := actual) (regular := regular) (current := piece.lowerEndpoint) (target := target)
             (reading := piece.source) (payment := payment)
             queried geometry.val sourceOwner agreement }

namespace Block

/-- Construct one actual paid Block on unchanged cached old source/target queries and exact original span incidence. -/
def build (incidence : target.parameter = piece.span.upper)
    (width : piece.span.width ^ 2 ≤ Geometric.Basic.quarterRadius 1 7) :
    Block (regular := regular) piece queried sourceOwner agreement :=
  have payment : (target.parameter - piece.span.lower) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7 := by
    rewrite [incidence]
    exact width
  let geometry := Geometry.build piece.source queried.val regular payment
  let block := Steps.Acquisition.Block.build
    (site := site) (parameter := parameter) (unitQuarter := quarter) (positive := positive)
    (actual := actual) (regular := regular) (current := piece.lowerEndpoint) (target := target)
    (reading := piece.source) (payment := payment)
    queried geometry sourceOwner agreement
  ⟨incidence, payment, ⟨geometry, rfl⟩, ⟨block, rfl⟩⟩

variable {piece queried sourceOwner agreement}
variable (retained : Block (regular := regular) piece queried sourceOwner agreement)

include retained

/-- Read the exact original target-to-span incidence retained with this same actual paid Block. -/
theorem incidence : target.parameter = piece.span.upper := retained.1

/-- Read the original actual depth-seven sharp-box width payment. -/
theorem payment : (target.parameter - piece.span.lower) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7 := retained.2.1

/-- Read the SAME actual sharp Geometry retaining both complete old queries and the literal physical Route. -/
@[expose] def geometry : Geometry piece.source queried.val regular retained.payment := retained.2.2.1.val

/-- The whole actual Geometry is the original factory on these SAME cached old source and target readings. -/
theorem geometry_eq : retained.geometry = Geometry.build piece.source queried.val regular retained.payment :=
  retained.2.2.1.property

/-- Read the identical complete supplied-owner Block with all paid acquisitions, comparisons and final Endpoint. -/
@[expose] def paid : Steps.Acquisition.Block
      (site := site) (parameter := parameter) (unitQuarter := quarter) (positive := positive)
      (actual := actual) (regular := regular) (current := piece.lowerEndpoint) (target := target)
      (reading := piece.source) (payment := retained.payment)
      queried retained.geometry sourceOwner agreement :=
  retained.2.2.2.val

/-- The complete actual paid Block is the original factory on the SAME geometry and exact input Owner/agreement. -/
theorem paid_eq : retained.paid =
    Steps.Acquisition.Block.build
      (site := site) (parameter := parameter) (unitQuarter := quarter) (positive := positive)
      (actual := actual) (regular := regular) (current := piece.lowerEndpoint) (target := target)
      (reading := piece.source) (payment := retained.payment)
      queried retained.geometry sourceOwner agreement :=
  retained.2.2.2.property

/-- Read the literal full-cubic finishOwner stored by this particular original paid execution. -/
@[expose] def finishOwner : OwnerAt site parameter quarter positive target := retained.paid.finishOwner

/-- Read the actual original cached target-reading agreement for the next source handoff. -/
@[expose] def nextAgreement : Steps.Acquisition.InitialAgreement target queried.val retained.finishOwner :=
  retained.paid.nextAgreement

/-- The original retained span width also measures the actual ordered physical route endpoint parameters. -/
theorem width_eq : (piece.span.lower - target.parameter) ^ 2 = piece.span.width ^ 2 := by
  rewrite [retained.incidence]
  change (piece.span.lower - piece.span.upper) ^ 2 = (piece.span.upper - piece.span.lower) ^ 2
  ring1

/-- An internally chosen sufficient chart width pays actual whole-source distances on this SAME stored paid Route. -/
theorem pointBound (physical : AccuracyRequest)
    (width : piece.span.width ^ 2 ≤
      Geometric.Basic.quarterRadius 1 (Geometry.widthMinimum site parameter physical)) :
    Polynomial.Geometry.ClearPath.PointBound
      (Transport.Spatial.coordinate site parameter 2 quarter positive piece.span.lower)
      physical.tolerance retained.geometry.route.path :=
  retained.geometry.route_pointBound_of_depth physical (retained.width_eq.trans_le width)

variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets sourcePath stage}

/-- The SAME retained physical source-family caches inherit actual query distances from their stored paid Route.

The source family is already acquired on the identical paid acquisition.
This operation descends that existing family and its literal head/tail
owners. It neither prepares a new source model nor substitutes an equal
model/query or constant polynomial for the original cached one.
-/
theorem source_distanceBound (physical : AccuracyRequest)
    (width : piece.span.width ^ 2 ≤
      Geometric.Basic.quarterRadius 1 (Geometry.widthMinimum site parameter physical))
    (sources : Spine.Sources
      (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet) (targets := targets)
      (fun {_start _finish} segment =>
        Factors.Segment.Reading.Payment.widthRequest retained.paid.anchor segment)
      retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine) :
    Spine.Sources.DistanceBound
      (Transport.Spatial.coordinate site parameter 2 quarter positive piece.span.lower) physical.tolerance
      (fun {_start _finish} segment =>
        Factors.Segment.Reading.Payment.widthRequest retained.paid.anchor segment)
      retained.geometry.route.path retained.geometry.route.within sourceOwner retained.paid.paid.spine sources :=
  Spine.Sources.distanceBound _ _ _ _ _ _
    retained.paid.paid.spine sources (retained.pointBound physical width)

end Block

end Spatial

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

end
