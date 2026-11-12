module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Trace
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Actual retained closure of the four paid quarter traces

The derived full-cubic final-to-initial comparison supplies the original
OwnerJoin.acquire factory. Its actual retained owner tails and selected
comparison indices feed OwnerPath.close on the same cached appended path.
The original ClosedRealization is retained with its exact factory identity.
These realized root readings remain distinct from numerical period samples.
Canonical cycle and integral attachment remain additional certificates.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {site : Fin 2} {parameter : Canonical}
section ActualInputs

variable {circuit : Transport.Circuit site parameter}
variable {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable (execution : Execution.Cache initial secondInput thirdInput fourthInput)

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] ownerRootName

namespace Closure.Result

/-- Read the SAME derived signed return witness at the original OwnerJoin names, without another comparison. -/
def ownerComparison : NamedEquivalent (ownerName execution.returnOwner) (ownerName sourceOwner) := by
  have compared := Execution.Cache.returnEquivalentAt (initial := initial)
    (secondInput := secondInput) (thirdInput := thirdInput) (fourthInput := fourthInput) execution
  unfold ownerRootName at compared
  exact compared

/-- Retain the SAME actual four-quarter trace, derived return witness, original OwnerJoin and literal path closure.

The trace cache comes from the actual retained quarter realizations.
OwnerJoin.acquire selects finite tails of those literal returned/initial
Owners using the internally derived signed witness. path.close consumes
that SAME join and complete append cache. No desired final agreement,
replacement closed trace or canonical-cycle relation is an input.
-/
@[expose] def Cache :=
  Σ traced : { retained : Trace.Result.Cache execution // retained = Trace.Result.Cache.build execution },
    Σ compared : { retained : NamedEquivalent (ownerName execution.returnOwner) (ownerName sourceOwner) //
        retained = ownerComparison execution },
      Σ join : { retained : OwnerJoin execution.returnOwner sourceOwner //
          retained = OwnerJoin.acquire execution.returnOwner sourceOwner compared.val },
        { closed : OwnerPath.ClosedRealization traced.val.path // closed = traced.val.path.close join.val }

namespace Cache

/-- Execute the same original append, comparison readback, join and path-close factories once and retain them whole. -/
def build : Cache execution :=
  let traced := Trace.Result.Cache.build execution
  let compared := ownerComparison execution
  let join := OwnerJoin.acquire execution.returnOwner sourceOwner compared
  let closed := traced.path.close join
  ⟨⟨traced, rfl⟩, ⟨compared, rfl⟩, ⟨join, rfl⟩, ⟨closed, rfl⟩⟩

variable (cache : Cache execution)

/-- Read the SAME whole actual append/path cache. -/
@[expose] def traced : Trace.Result.Cache execution := cache.1.val

/-- Read the SAME derived full-cubic return comparison on the literal returned and initial Owners. -/
@[expose] def compared : NamedEquivalent (ownerName execution.returnOwner) (ownerName sourceOwner) := cache.2.1.val

/-- Read the SAME original join, including actual selected owner tails and operational comparison caches. -/
@[expose] def join : OwnerJoin execution.returnOwner sourceOwner := cache.2.2.1.val

/-- Read the SAME original closed realization on this literal path and retained join. -/
@[expose] def closed : OwnerPath.ClosedRealization cache.traced.path := cache.2.2.2.val

/-- The retained trace is the shared original append factory on those SAME quarter realizations. -/
theorem traced_eq : cache.traced = Trace.Result.Cache.build execution := cache.1.property

/-- The retained signed return witness is exactly the actual original return-name readback. -/
theorem compared_eq : cache.compared = ownerComparison execution := cache.2.1.property

/-- The join is the complete original acquire factory on these SAME actual Owners and cached comparison. -/
theorem join_eq : cache.join = OwnerJoin.acquire execution.returnOwner sourceOwner cache.compared :=
  cache.2.2.1.property

/-- The closed realization is exactly path.close on this SAME retained path and join. -/
theorem closed_eq : cache.closed = cache.traced.path.close cache.join := cache.2.2.2.property

/-- The SAME closed path retains the four actual original paid vertex lists in their signed circuit order. -/
theorem vertices_eq : cache.traced.path.vertices = execution.first.trace.vertices ++
    (execution.second.paid.trace.vertices ++
      (execution.third.paid.trace.vertices ++ execution.fourth.paid.trace.vertices)) := cache.traced.vertices_eq

end Cache

end Closure.Result

end ActualInputs

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
variable (execution : Execution initial secondOriginal thirdOriginal fourthOriginal)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Closure

/-- Read the derived full-cubic return witness at the same original Owner names required by the join factory. -/
def ownerComparison : NamedEquivalent (ownerName execution.returnOwner) (ownerName sourceOwner) :=
  Result.ownerComparison (firstInput := Input.ofSteps firstOriginal rfl) execution

/-- The actual retained paid circuit, its original owner join and its complete closed realization.

The trace cache is acquired once, the actual returned and initial owner
names are compared by the derived return operation, and the original join
selects finite tails of those same Owners. The original path closure then
reuses that retained join and the identical appended trace. No desired
return witness or replacement closed trace is supplied as an input.
-/
@[expose] def Result :=
  Result.Cache (firstInput := Input.ofSteps firstOriginal rfl) execution

namespace Result

/-- Construct and retain the exact paid trace, actual owner join and original closed-realization factories once. -/
def build : Result execution :=
  Cache.build (firstInput := Input.ofSteps firstOriginal rfl) execution

/-- The old closure entry is exactly the shared original join/close factory on the SAME retained old execution. -/
theorem build_eq : build execution = Cache.build (firstInput := Input.ofSteps firstOriginal rfl) execution := by
  unfold build
  rfl

variable (result : Result execution)

/-- Read the entire same four-path append cache with its unchanged actual paid traces and ordered vertices. -/
@[expose] def traced : Trace.Result execution := result.1.val

/-- Read the exact derived comparison between the actual returned and original initial full-cubic Owner names. -/
@[expose] def compared : NamedEquivalent (ownerName execution.returnOwner) (ownerName sourceOwner) := result.2.1.val

/-- Read the actual original join, preserving its selected tails, comparison indices and operational evidence. -/
@[expose] def join : OwnerJoin execution.returnOwner sourceOwner := result.2.2.1.val

/-- Read the original full closed-realization cache over the identical retained actual paid OwnerPath. -/
@[expose] def closed : OwnerPath.ClosedRealization result.traced.path := result.2.2.2.val

/-- The trace cache is the exact four-paid-quarter factory on the same original complete execution input. -/
theorem traced_eq : result.traced = Trace.Result.build execution :=
  result.1.property.trans (Trace.Result.build_eq execution).symm

/-- The join's operational comparison is the exact derived return operation on the actual original Owner inputs. -/
theorem compared_eq : result.compared = Closure.ownerComparison execution := by
  unfold Closure.ownerComparison
  exact result.2.1.property

/-- The whole original join cache is acquired from these same Owners and the identical stored comparison witness. -/
theorem join_eq : result.join = OwnerJoin.acquire execution.returnOwner sourceOwner result.compared :=
  result.2.2.1.property

/-- The whole actual closed realization is the original close operation on this same cached trace and retained join. -/
theorem closed_eq : result.closed = result.traced.path.close result.join := result.2.2.2.property

/-- The realized closed path has exactly the ordered vertices of the same four retained actual paid traces. -/
theorem vertices_eq : result.traced.path.vertices = execution.first.receipt.trace.vertices ++
    (execution.second.paid.receipt.trace.vertices ++
      (execution.third.paid.receipt.trace.vertices ++ execution.fourth.paid.receipt.trace.vertices)) :=
  result.traced.vertices_eq

end Result

end Closure

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
