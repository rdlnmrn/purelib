module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Closure.Descent
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Requests
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Schedule
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Approximation.AccuracyRequest
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Joint original row/source allocations on the same actual paid circuit

The literal retained paid subdivisions determine the global request count
before source models or primitive observations. One original finite search
chooses the source targets. The inverse aggregate request makes the SAME
original closed observer's actual local request exactly T/4. Its single old
spine is then partitioned and descended through the stored paid geometry.
This is an exact allocation/payment construction, not an integral identity.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter}
variable {firstReading : ReadingAt circuit.first.actual UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginalOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginal : Steps.Quarter circuit.first.actual circuit.first.regular
  UniformPrimitiveMesh.firstEndpoint firstReading firstOriginalOwner}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {agreement : InitialAgreement UniformPrimitiveMesh.firstEndpoint firstReading sourceOwner}
variable {initial : Quarter firstOriginal sourceOwner agreement}
variable {secondReading : ReadingAt circuit.second.actual UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginalOwner : OwnerAt site parameter .second (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginal : Steps.Quarter circuit.second.actual circuit.second.regular
  UniformPrimitiveMesh.firstEndpoint secondReading secondOriginalOwner}
variable {thirdReading : ReadingAt circuit.third.actual UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginalOwner : OwnerAt site parameter .third (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginal : Steps.Quarter circuit.third.actual circuit.third.regular
  UniformPrimitiveMesh.firstEndpoint thirdReading thirdOriginalOwner}
variable {fourthReading : ReadingAt circuit.fourth.actual UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginalOwner : OwnerAt site parameter .fourth (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginal : Steps.Quarter circuit.fourth.actual circuit.fourth.regular
  UniformPrimitiveMesh.firstEndpoint fourthReading fourthOriginalOwner}
variable {execution : Execution initial secondOriginal thirdOriginal fourthOriginal}

open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Legendre.Periods.Jets.Source (Row)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Closure.Result

variable (result : Closure.Result execution) (row : Row)
variable {baseStart baseFinish : LiftedPoint 2} (sourcePath : LiftedPath 2 baseStart baseFinish)
variable (currentStage : Nat) (request : AccuracyRequest)

set_option genInjectivity false in
/-- Joint source/observation allocation retains the actual count, search, targets and complete original observer caches.

The original row expression supplies its own original vertex-domain
proofs. The actual request list and source target are selected before any
old primitive observation is acquired. The one completed observation cache
then supplies every actual quarter/Block/Segment view and literal closing.
The nominal constructor retains all seven complete cache fields without
expanding their dependent physical-path families at every native use.
-/
structure Requested where
  /-- The exact actual prepared-request count, computed before source preparation or primitive observation. -/
  cachedCount : { retained : Nat // retained = execution.requestCount }
  /-- The original completed finite search at the SAME actual count and caller request. -/
  cachedSelection : { retained : Search.Selection (PreparedParents.Trace.closedScale cachedCount.val)
        currentStage request.tolerance //
      retained = Search.Selection.build (PreparedParents.Trace.closedScale cachedCount.val)
        (PreparedParents.Trace.closedScale_nonnegative cachedCount.val)
        currentStage request.tolerance request.positive }
  /-- The original source targets completed once at the retained search's actual stage. -/
  cachedTargets : { retained : CellEndpoints.Targets sourcePath cachedSelection.val.stage //
      retained = CellEndpoints.Targets.build sourcePath cachedSelection.val.stage }
  /-- The original exact local request chosen from those SAME source targets. -/
  cachedAccuracy : { retained : AccuracyRequest // retained = PreparedParents.Trace.localAccuracy cachedTargets.val }
  /-- The SAME original inverse-request/Closed acquisition, including all old observations and literal closing. -/
  cachedObservations : { retained : Primitive.Closed.Requested result.traced.path
        (PreparedParents.Trace.defined row result.traced.path) result.join cachedAccuracy.val //
      retained = Primitive.Closed.Requested.build result.traced.path
        (PreparedParents.Trace.defined row result.traced.path) result.join cachedAccuracy.val }
  /-- The complete original partition of that IDENTICAL stored Closed acquisition, with its factory identity. -/
  cachedPartition : { retained : Partitioned result (row.expression parameter)
        (PreparedParents.Trace.defined row result.traced.path) cachedObservations.val.request //
      retained = Partitioned.ofObserved result (row.expression parameter)
        (PreparedParents.Trace.defined row result.traced.path) cachedObservations.val.request
        cachedObservations.val.closed }
  /-- The actual whole quarter/Block/Segment descent of the SAME stored partition, without observer replay. -/
  cachedDescent : { retained : Partitioned.Descent cachedPartition.val //
      retained = Partitioned.Descent.build cachedPartition.val }

constructive_injectivity Requested

namespace Requested

/-- Compute compatible original source/closed requests, observe once, and retain the complete old physical descent. -/
def build : Requested result row sourcePath currentStage request :=
  let count := execution.requestCount
  let selection := Search.Selection.build (PreparedParents.Trace.closedScale count)
    (PreparedParents.Trace.closedScale_nonnegative count) currentStage request.tolerance request.positive
  let targets := CellEndpoints.Targets.build sourcePath selection.stage
  let accuracy := PreparedParents.Trace.localAccuracy targets
  let observations := Primitive.Closed.Requested.build result.traced.path
    (PreparedParents.Trace.defined row result.traced.path) result.join accuracy
  let partition := Partitioned.ofObserved result (row.expression parameter)
    (PreparedParents.Trace.defined row result.traced.path) observations.request observations.closed
  let descended := Partitioned.Descent.build partition
  { cachedCount := ⟨count, rfl⟩
    cachedSelection := ⟨selection, rfl⟩
    cachedTargets := ⟨targets, rfl⟩
    cachedAccuracy := ⟨accuracy, rfl⟩
    cachedObservations := ⟨observations, rfl⟩
    cachedPartition := ⟨partition, rfl⟩
    cachedDescent := ⟨descended, rfl⟩ }

variable {result row sourcePath currentStage request}
variable (retained : Requested result row sourcePath currentStage request)

/-- Read the SAME actual moving-request count computed before observations from the literal paid subdivisions. -/
@[expose] def count : Nat := retained.cachedCount.val

/-- Read the entire original finite stage search, including its real fuel, quotient and attained target payment. -/
@[expose] def selection : Search.Selection (PreparedParents.Trace.closedScale retained.count)
    currentStage request.tolerance := retained.cachedSelection.val

/-- Read the exact original source targets built once at the actual selected finite stage. -/
@[expose] def targets : CellEndpoints.Targets sourcePath retained.selection.stage := retained.cachedTargets.val

/-- Read the actual local request selected from the SAME source target before observing any retained vertex. -/
@[expose] def accuracy : AccuracyRequest := retained.cachedAccuracy.val

/-- Read the complete original cached-vertices/inverse-request/closed-observation execution unchanged. -/
@[expose] def observations : Primitive.Closed.Requested result.traced.path
    (PreparedParents.Trace.defined row result.traced.path) result.join retained.accuracy :=
  retained.cachedObservations.val

/-- Read the actual original partition of that SAME completed old closing acquisition, without observation replay. -/
@[expose] def partition : Partitioned result (row.expression parameter)
    (PreparedParents.Trace.defined row result.traced.path) retained.observations.request := retained.cachedPartition.val

/-- Read all actual old physical Segment views of the SAME stored paid quarters and completed observation cache. -/
@[expose] def descended : Partitioned.Descent retained.partition := retained.cachedDescent.val

/-- The count belongs to the SAME actual retained four-quarter paid execution. -/
theorem count_eq : retained.count = execution.requestCount := retained.cachedCount.property

/-- The full original search is the actual factory on the retained global count and original request. -/
theorem selection_eq : retained.selection = Search.Selection.build
    (PreparedParents.Trace.closedScale retained.count) (PreparedParents.Trace.closedScale_nonnegative retained.count)
    currentStage request.tolerance request.positive := retained.cachedSelection.property

/-- The complete source targets are their original factory at the identical selected stage. -/
theorem targets_eq : retained.targets = CellEndpoints.Targets.build sourcePath retained.selection.stage :=
  retained.cachedTargets.property

/-- The exact intended local request is the original source-target quarter allocator. -/
theorem accuracy_eq : retained.accuracy = PreparedParents.Trace.localAccuracy retained.targets :=
  retained.cachedAccuracy.property

/-- The original observation execution is its actual single inverse-request factory on the SAME expression and path. -/
theorem observations_eq : retained.observations = Primitive.Closed.Requested.build result.traced.path
    (PreparedParents.Trace.defined row result.traced.path) result.join retained.accuracy :=
  retained.cachedObservations.property

/-- The partition is the exact complete-cache constructor on this SAME stored old Closed execution. -/
theorem partition_eq : retained.partition = Partitioned.ofObserved result (row.expression parameter)
    (PreparedParents.Trace.defined row result.traced.path) retained.observations.request retained.observations.closed :=
  retained.cachedPartition.property

/-- Every original paid quarter/Block/Segment view is the factory on the SAME old completed partition. -/
theorem descended_eq : retained.descended = Partitioned.Descent.build retained.partition :=
  retained.cachedDescent.property

/-- The partition retains the literal same complete old Closed result, including the original actual closing
Comparison. -/
theorem partition_observed : retained.partition.observed = retained.observations.closed :=
  (congrArg (fun partition : Partitioned result (row.expression parameter)
      (PreparedParents.Trace.defined row result.traced.path) retained.observations.request => partition.observed)
    retained.partition_eq).trans
    (Partitioned.ofObserved_observed result (row.expression parameter)
      (PreparedParents.Trace.defined row result.traced.path) retained.observations.request retained.observations.closed)

/-- The actual observer's original local request equals the SAME source-target allocator as a whole request object. -/
theorem observed_accuracy : retained.partition.observed.observations.accuracy =
    PreparedParents.Trace.localAccuracy retained.targets :=
  ((congrArg (fun closed : Primitive.Closed result.traced.path
      (PreparedParents.Trace.defined row result.traced.path) result.join retained.observations.request =>
        closed.observations.accuracy) retained.partition_observed).trans
      (Primitive.Closed.Requested.accuracy_eq retained.observations)).trans
    retained.accuracy_eq

/-- The original source target and actual OLD observation request satisfy the exact index admission internally. -/
theorem allocation : retained.targets.endpoint = 4 * retained.partition.observed.observations.accuracy.tolerance :=
  (PreparedParents.Trace.localAccuracy_allocation retained.targets).trans
    (congrArg (fun accuracy : AccuracyRequest => 4 * accuracy.tolerance) retained.observed_accuracy).symm

/-- The actual chosen source stage pays the retained global count coefficient by the original target's own decay law. -/
theorem source_payment : PreparedParents.Trace.closedScale retained.count * retained.targets.endpoint <
    request.tolerance := by
  have decays := retained.targets.mul_localBound_le_quarterRadius
    (PreparedParents.Trace.closedScale retained.count) (PreparedParents.Trace.closedScale_nonnegative retained.count)
  rewrite [← retained.targets.endpoint_eq] at decays
  exact decays.trans_lt (retained.selection.later_accurate (Nat.le_refl _))

end Requested

end Closure.Result

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
