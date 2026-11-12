module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Observation.Spine
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Append
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment

/-! # The same old quarter observations on actual paid Blocks and physical Segments

The retained paid Steps spine supplies every original Block and its actual
Route.Acquisition. Splitting its SAME old whole trace retains each entire
Block spine, then the original physical acquisition splits that cache into
literal Segment observations. No old observations or paid preparations are
acquired again. The original circuit closing cache remains independent.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source (Row)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
  (widthRequest)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Rational) < 2}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

namespace Observation

/-- Every SAME original paid Block retains its complete old split and its actual physical-Segment view factory. -/
@[expose] def Blocks
    (actual : Transport.Quarter site parameter 2 unitQuarter positive) (regular : parameter ≠ criticalValue site)
    (expression : Expression (Paths.polynomial parameter)) (accuracy : AccuracyRequest) :
    (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    Primitive.Spine expression accuracy paid.trace → Type 1
  | [] => fun _ _ _ _ _ _ _ _ => PUnit
  | target :: targets => fun _ _ _ original _sourceOwner _agreement paid observed =>
      Σ divided : { cached : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
            paid.head.paid.trace paid.tail.trace //
          cached = Primitive.Spine.split paid.head.paid.trace paid.tail.trace observed },
        Σ _physical : { cached : CoveredTracedPath.Acquisition.Observations paid.head.paid.paid divided.val.before //
            cached = CoveredTracedPath.Acquisition.Observations.build paid.head.paid.paid divided.val.before },
          Blocks actual regular expression accuracy targets target original.nextReading
            original.headCovered.finishOwner original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail
            divided.val.after
termination_by structural targets => targets

namespace Blocks

/-- Descend the same old paid trace through its actual retained Blocks, then split every literal physical Segment
once. -/
def build
    (actual : Transport.Quarter site parameter 2 unitQuarter positive) (regular : parameter ≠ criticalValue site)
    (expression : Expression (Paths.polynomial parameter)) (accuracy : AccuracyRequest) :
    (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (observed : Primitive.Spine expression accuracy paid.trace) →
    Blocks actual regular expression accuracy targets current reading originalOwner original sourceOwner agreement paid
      observed
  | [] => fun _ _ _ _ _ _ _ _ => PUnit.unit
  | target :: targets => fun _ _ _ original _sourceOwner _agreement paid observed =>
      let divided := Primitive.Spine.split paid.head.paid.trace paid.tail.trace observed
      let physical := CoveredTracedPath.Acquisition.Observations.build paid.head.paid.paid divided.before
      let following := build actual regular expression accuracy targets target original.nextReading
        original.headCovered.finishOwner original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail
        divided.after
      ⟨⟨divided, rfl⟩, ⟨physical, rfl⟩, following⟩
termination_by structural targets => targets

variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {expression : Expression (Paths.polynomial parameter)} {accuracy : AccuracyRequest}
variable {target : Endpoint} {targets : List Endpoint} {current : Endpoint} {reading : ReadingAt actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {original : Steps actual regular current reading originalOwner (target :: targets)}
variable {agreement : InitialAgreement current reading sourceOwner}
variable {paid : Acquisition original sourceOwner agreement}
variable {observed : Primitive.Spine expression accuracy paid.trace}
variable (views : Blocks actual regular expression accuracy (target :: targets) current reading originalOwner
  original sourceOwner agreement paid observed)

/-- Read the actual complete old head/suffix split from the SAME paid quarter observation execution. -/
@[expose] def divided : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
    paid.head.paid.trace paid.tail.trace := views.1.val

/-- Read the complete old primitive observations of the literal same stored paid Block. -/
@[expose] def head : Primitive.Spine expression accuracy paid.head.paid.trace := views.divided.before

/-- Read the complete old suffix, whose source is the SAME literal preceding old target vertex. -/
@[expose] def following : Primitive.Spine expression accuracy paid.tail.trace := views.divided.after

/-- Read every original physical Segment view, preserving the complete original acquired Route spine and old Block
cache. -/
@[expose] def physical : CoveredTracedPath.Acquisition.Observations paid.head.paid.paid views.head := views.2.1.val

/-- Read the unchanged actual tail of old Block/Segment views on the literal paid finish Owner and cached agreement. -/
@[expose] def tail : Blocks actual regular expression accuracy targets target original.nextReading
    original.headCovered.finishOwner original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail
      views.following := views.2.2

/-- The whole split is the original append-boundary operation on this SAME old actual paid input. -/
theorem divided_eq : views.divided = Primitive.Spine.split paid.head.paid.trace paid.tail.trace observed :=
  views.1.property

/-- Physical Segment views are the exact factory on this identical stored paid Block and its complete old spine. -/
theorem physical_eq : views.physical = CoveredTracedPath.Acquisition.Observations.build
    paid.head.paid.paid views.head := views.2.1.property

/-- Both old paid-Block views retain one literal shared observation cache. -/
theorem shared : views.following.first = views.head.last := views.divided.shared

/-- The actual head Block retains the complete original quarter source vertex. -/
theorem head_first : views.head.first = observed.first :=
  (congrArg (fun divided : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
    paid.head.paid.trace paid.tail.trace => divided.before.first) views.divided_eq).trans
      (Primitive.Spine.split_first observed)

/-- The actual suffix retains the complete original quarter returned vertex. -/
theorem following_last : views.following.last = observed.last :=
  (congrArg (fun divided : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
    paid.head.paid.trace paid.tail.trace => divided.after.last) views.divided_eq).trans
      (Primitive.Spine.split_last observed)

end Blocks

end Observation

namespace Quarter

variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {current : Endpoint} {reading : ReadingAt actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {originalQuarter : Steps.Quarter actual regular current reading originalOwner}
variable {agreement : InitialAgreement current reading sourceOwner}
variable {expression : Expression (Paths.polynomial parameter)} {accuracy : AccuracyRequest}
variable (quarter : Quarter originalQuarter sourceOwner agreement)
variable (observed : Primitive.Spine expression accuracy quarter.receipt.trace)

/-- Retain complete old Block/Segment views on the actual SAME original paid-quarter receipt. -/
@[expose] def Observations :=
  Σ original : { cached : Primitive.Spine expression accuracy quarter.receipt.trace // cached = observed },
    { blocks : Observation.Blocks actual regular expression accuracy quarter.originalQuarter.cache.val current reading
        originalOwner quarter.originalQuarter.steps sourceOwner agreement quarter.receipt original.val //
      blocks = Observation.Blocks.build actual regular expression accuracy quarter.originalQuarter.cache.val current
        reading originalOwner quarter.originalQuarter.steps sourceOwner agreement quarter.receipt original.val }

namespace Observations

/-- Split the supplied SAME old quarter spine once along its stored actual paid Block and physical acquisition
factories. -/
def build : Observations quarter observed :=
  let blocks := Observation.Blocks.build actual regular expression accuracy quarter.originalQuarter.cache.val current
    reading originalOwner quarter.originalQuarter.steps sourceOwner agreement quarter.receipt observed
  ⟨⟨observed, rfl⟩, ⟨blocks, rfl⟩⟩

variable {observed}
variable (views : Observations quarter observed)

/-- Read the complete literal original quarter observation input, unchanged. -/
@[expose] def original : Primitive.Spine expression accuracy quarter.receipt.trace := views.1.val

/-- Read the complete actual old observation descent through this SAME stored paid quarter and all its physical
Segments. -/
@[expose] def blocks : Observation.Blocks actual regular expression accuracy quarter.originalQuarter.cache.val current
    reading originalOwner quarter.originalQuarter.steps sourceOwner agreement quarter.receipt views.original :=
  views.2.val

/-- The full old primitive observation input is the supplied original cache. -/
theorem original_eq : views.original = observed := views.1.property

/-- Every actual Block and physical Segment view is the original split factory on the SAME old input and paid
receipt. -/
theorem blocks_eq : views.blocks = Observation.Blocks.build actual regular expression accuracy
    quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps sourceOwner agreement
      quarter.receipt views.original := views.2.property

end Observations

end Quarter

namespace Observation.Blocks

variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {target : Endpoint} {targets : List Endpoint} {current : Endpoint} {reading : ReadingAt actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {original : Steps actual regular current reading originalOwner (target :: targets)}
variable {agreement : InitialAgreement current reading sourceOwner} {paid : Acquisition original sourceOwner agreement}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourceOriginal : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourceOriginal stage} {accuracy : AccuracyRequest}
variable (row : Row)
variable {observed : Primitive.Spine (row.expression parameter) accuracy paid.trace}
variable (views : Blocks actual regular (row.expression parameter) accuracy (target :: targets) current reading
  originalOwner original sourceOwner agreement paid observed)
variable (sources : PreparedParents.Trace.Physical.Spine.Sources (frame := frame) (basis := basis) (count := count)
  (floor := floor) (sheet := sheet) (targets := sourceTargets)
  (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
  original.headGeometry.route.path original.headGeometry.route.within sourceOwner paid.head.paid.spine)
variable (allocation : sourceTargets.endpoint = 4 * accuracy.tolerance)

/-- Construct the actual original Physical fold on every Segment of this SAME old head Block and stored paid Route.

The exact scalar request-index admission keeps all original old states and
radii. Original Parents and source preparations are supplied complete caches;
no final numerical bound or desired root equivalence is an input.
-/
def compareHead :=
  PreparedParents.Trace.Physical.Spine.compare row paid.head.paid.paid views.physical sources allocation

/-- The actual same-cache Physical comparison internally pays this head Block's complete source integral residual. -/
theorem compareHead_integral_error_le : Norm.Basic.normSq
    (views.head.last.value - views.head.first.value -
      Norm.Sum.Basic.gaussianSum (compareHead row views sources allocation).integrals) ≤
        (CoveredTracedPath.Acquisition.Spine.requestCount
          (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
          original.headGeometry.route.path original.headGeometry.route.within sourceOwner
          paid.head.paid.spine : Rational) *
        ((CoveredTracedPath.Acquisition.Spine.requestCount
          (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
          original.headGeometry.route.path original.headGeometry.route.within sourceOwner
          paid.head.paid.spine : Rational) *
          (26 * sourceTargets.endpoint)) :=
  (compareHead row views sources allocation).integral_error_le

end Observation.Blocks

end Steps.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
