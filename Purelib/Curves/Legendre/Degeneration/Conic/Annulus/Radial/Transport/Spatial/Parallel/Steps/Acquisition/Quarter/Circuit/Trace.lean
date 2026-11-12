module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Seam.Trace
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit.Seam.Trace
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Geometry.Rational.Polygon.Chain

/-! # The same four paid traces in original geometric order

Each quarter contributes its identical stored paid OwnerPath, with only
the exact physical seam endpoint transported. The four complete transported
paths and their ordered append are cached with whole factory identities.
Their vertices are exactly the ordered concatenation of the original four
actual paid trace vertex lists. No old unpaid trace is substituted.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

variable {site : Fin 2} {parameter : Canonical}
section ActualInputs

variable {circuit : Transport.Circuit site parameter}
variable {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable (execution : Execution.Cache (site := site) (parameter := parameter) (circuit := circuit)
  (firstInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement)
  initial secondInput thirdInput fourthInput)

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Trace.Result

/-- The SAME actual first paid path ends at the second actual input's original source point and handoff Owner. -/
@[expose] def First := OwnerPath (Paths.polynomial parameter)
  (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter) sourceOwner
  (coordinate site parameter 2 .second (of_decide_eq_true rfl) secondInput.sourceEndpoint.parameter)
    execution.second.seam.owner

/-- The SAME actual second paid path retains its exact supplied source Owner and next handoff Owner. -/
@[expose] def Second := OwnerPath (Paths.polynomial parameter)
  (coordinate site parameter 2 .second (of_decide_eq_true rfl) secondInput.sourceEndpoint.parameter)
    (Execution.Cache.second (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput) (fourthInput := fourthInput) execution).seam.owner
  (coordinate site parameter 2 .third (of_decide_eq_true rfl) thirdInput.sourceEndpoint.parameter)
    (Execution.Cache.third (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput) (fourthInput := fourthInput) execution).seam.owner

/-- The SAME actual third paid path retains its exact supplied source Owner and next handoff Owner. -/
@[expose] def Third := OwnerPath (Paths.polynomial parameter)
  (coordinate site parameter 2 .third (of_decide_eq_true rfl) thirdInput.sourceEndpoint.parameter)
    (Execution.Cache.third (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput) (fourthInput := fourthInput) execution).seam.owner
  (coordinate site parameter 2 .fourth (of_decide_eq_true rfl) fourthInput.sourceEndpoint.parameter)
    (Execution.Cache.fourth (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput) (fourthInput := fourthInput) execution).seam.owner

/-- The SAME actual fourth paid path ends at the original first source point and its actual returned Owner. -/
@[expose] def Fourth := OwnerPath (Paths.polynomial parameter)
  (coordinate site parameter 2 .fourth (of_decide_eq_true rfl) fourthInput.sourceEndpoint.parameter)
    execution.fourth.seam.owner
  (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)
    execution.returnOwner

/-- The same-base actual path retains both the supplied original source and literal returned full-cubic Owners. -/
@[expose] def Path := OwnerPath (Paths.polynomial parameter)
  (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter) sourceOwner
  (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)
    execution.returnOwner

/-- Retain the four SAME original endpoint-transported paid traces and their actual ordered append.

Only the original castEndpoints and append factories run here. All input
paths, source/finish Owners and stationary/moving links are the actual
stored paid realization objects. No vertex-list replacement is used.
-/
@[expose] def Cache :=
  Σ first : { retained : First execution //
      retained = Transport.Seam.Receipt.trace (left := circuit.first) (right := circuit.second) execution.second.seam
        (Input.Realization.trace (leg := circuit.first) (input := firstInput) execution.first) },
    Σ second : { retained : Second execution //
        retained = Transport.Seam.Receipt.trace (left := circuit.second) (right := circuit.third) execution.third.seam
          (Input.Realization.trace (leg := circuit.second) (input := secondInput) execution.second.paid) },
      Σ third : { retained : Third execution //
          retained = Transport.Seam.Receipt.trace (left := circuit.third) (right := circuit.fourth)
            execution.fourth.seam (Input.Realization.trace (leg := circuit.third) (input := thirdInput)
              execution.third.paid) },
        Σ fourth : { retained : Fourth execution //
            retained = Transport.Seam.Receipt.trace (left := circuit.fourth) (right := circuit.first)
              execution.closing (Input.Realization.trace (leg := circuit.fourth) (input := fourthInput)
                execution.fourth.paid) },
          { path : Path execution // path = first.val.append (second.val.append (third.val.append fourth.val)) }

namespace Cache

/-- Cache each actual original seam path transport once and append those identical whole paths in circuit order. -/
def build : Cache (site := site) (parameter := parameter) (circuit := circuit)
    (firstInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
    (secondInput := secondInput) (thirdInput := thirdInput) (fourthInput := fourthInput) execution :=
  let first : First execution := Transport.Seam.Receipt.trace (left := circuit.first) (right := circuit.second)
    execution.second.seam (Input.Realization.trace (leg := circuit.first) (input := firstInput) execution.first)
  let second : Second execution := Transport.Seam.Receipt.trace (left := circuit.second) (right := circuit.third)
    execution.third.seam (Input.Realization.trace (leg := circuit.second) (input := secondInput)
      execution.second.paid)
  let third : Third execution := Transport.Seam.Receipt.trace (left := circuit.third) (right := circuit.fourth)
    execution.fourth.seam (Input.Realization.trace (leg := circuit.third) (input := thirdInput) execution.third.paid)
  let fourth : Fourth execution := Transport.Seam.Receipt.trace (left := circuit.fourth) (right := circuit.first)
    execution.closing (Input.Realization.trace (leg := circuit.fourth) (input := fourthInput) execution.fourth.paid)
  let path : Path execution := first.append (second.append (third.append fourth))
  by
    refine ⟨⟨first, ?_⟩, ?_⟩
    · rfl
    · refine ⟨⟨second, ?_⟩, ?_⟩
      · rfl
      · refine ⟨⟨third, ?_⟩, ?_⟩
        · rfl
        · refine ⟨⟨fourth, ?_⟩, ?_⟩
          · rfl
          · refine ⟨path, ?_⟩
            rfl

variable (cache : Cache (site := site) (parameter := parameter) (circuit := circuit)
  (firstInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
  (secondInput := secondInput) (thirdInput := thirdInput) (fourthInput := fourthInput) execution)

/-- Read the SAME complete first actual transported path. -/
@[expose] def first : First execution := cache.1.val

/-- Read the SAME complete second actual transported path. -/
@[expose] def second : Second execution := cache.2.1.val

/-- Read the SAME complete third actual transported path. -/
@[expose] def third : Third execution := cache.2.2.1.val

/-- Read the SAME complete fourth actual transported path. -/
@[expose] def fourth : Fourth execution := cache.2.2.2.1.val

/-- Read the SAME complete ordered append, including every original stationary Owner link. -/
@[expose] def path : Path execution := cache.2.2.2.2.val

/-- The first stored path is exactly the original seam transport of the SAME actual first paid trace. -/
theorem first_eq : cache.first = Transport.Seam.Receipt.trace (left := circuit.first) (right := circuit.second)
    execution.second.seam (Input.Realization.trace (leg := circuit.first) (input := firstInput) execution.first) :=
  cache.1.property

/-- The second stored path is exactly the original seam transport of the SAME actual second paid trace. -/
theorem second_eq : cache.second = Transport.Seam.Receipt.trace (left := circuit.second) (right := circuit.third)
    execution.third.seam (Input.Realization.trace (leg := circuit.second) (input := secondInput)
      execution.second.paid) := cache.2.1.property

/-- The third stored path is exactly the original seam transport of the SAME actual third paid trace. -/
theorem third_eq : cache.third = Transport.Seam.Receipt.trace (left := circuit.third) (right := circuit.fourth)
    execution.fourth.seam (Input.Realization.trace (leg := circuit.third) (input := thirdInput)
      execution.third.paid) :=
  cache.2.2.1.property

/-- The fourth stored path is exactly the original seam transport of the SAME actual fourth paid trace. -/
theorem fourth_eq : cache.fourth = Transport.Seam.Receipt.trace (left := circuit.fourth) (right := circuit.first)
    execution.closing (Input.Realization.trace (leg := circuit.fourth) (input := fourthInput)
      execution.fourth.paid) :=
  cache.2.2.2.1.property

/-- The whole stored path is exactly the original append factory on those SAME four retained paths. -/
theorem path_eq : cache.path = cache.first.append (cache.second.append (cache.third.append cache.fourth)) :=
  cache.2.2.2.2.property

/-- The complete actual trace preserves all four original ordered signed vertex lists. -/
theorem vertices_eq : cache.path.vertices =
    (Input.Realization.trace (leg := circuit.first) (input := firstInput) execution.first).vertices ++
    ((Input.Realization.trace (leg := circuit.second) (input := secondInput) execution.second.paid).vertices ++
      ((Input.Realization.trace (leg := circuit.third) (input := thirdInput) execution.third.paid).vertices ++
        (Input.Realization.trace (leg := circuit.fourth) (input := fourthInput) execution.fourth.paid).vertices)) := by
  have firstVertices := (congrArg (fun path : First execution => path.vertices)
    cache.first_eq).trans (Transport.Seam.Receipt.trace_vertices (left := circuit.first) (right := circuit.second)
      execution.second.seam (Input.Realization.trace (leg := circuit.first) (input := firstInput) execution.first))
  have secondVertices := (congrArg (fun path : Second execution => path.vertices)
    cache.second_eq).trans (Transport.Seam.Receipt.trace_vertices (left := circuit.second) (right := circuit.third)
      execution.third.seam (Input.Realization.trace (leg := circuit.second) (input := secondInput)
        execution.second.paid))
  have thirdVertices := (congrArg (fun path : Third execution => path.vertices)
    cache.third_eq).trans (Transport.Seam.Receipt.trace_vertices (left := circuit.third) (right := circuit.fourth)
      execution.fourth.seam (Input.Realization.trace (leg := circuit.third) (input := thirdInput)
        execution.third.paid))
  have fourthVertices := (congrArg (fun path : Fourth execution => path.vertices)
    cache.fourth_eq).trans (Transport.Seam.Receipt.trace_vertices (left := circuit.fourth) (right := circuit.first)
      execution.closing (Input.Realization.trace (leg := circuit.fourth) (input := fourthInput)
        execution.fourth.paid))
  have lastPair := OwnerPath.append_vertices cache.third cache.fourth
  have lastThree := (OwnerPath.append_vertices cache.second
    (cache.third.append cache.fourth)).trans
      (congrArg (fun vertices => cache.second.vertices ++ vertices) lastPair)
  have allFour := (OwnerPath.append_vertices cache.first
    (cache.second.append (cache.third.append cache.fourth))).trans
      (congrArg (fun vertices => cache.first.vertices ++ vertices) lastThree)
  have appendCongr {left nextLeft right nextRight : List Canonical}
      (leftEq : left = nextLeft) (rightEq : right = nextRight) :
      left ++ right = nextLeft ++ nextRight :=
    (congrArg (fun vertices => vertices ++ right) leftEq).trans
      (congrArg (fun vertices => nextLeft ++ vertices) rightEq)
  exact ((congrArg (fun path : Path execution => path.vertices) cache.path_eq).trans allFour).trans
    (appendCongr firstVertices (appendCongr secondVertices (appendCongr thirdVertices fourthVertices)))

/-- The SAME complete appended actual path ends at its original initial physical point. -/
theorem terminal_eq : Geometry.Rational.Polygon.Chain.terminal
    (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)
    cache.path.vertices =
      coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter :=
  cache.path.vertices_terminal

end Cache

end Trace.Result

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

namespace Trace

/-- The original first paid trace with its actual final Owner indexed at the second quarter's identical source point. -/
@[expose] def First :=
  Result.First (firstInput := Input.ofSteps firstOriginal rfl) execution

/-- The original second paid trace with its same supplied source Owner and its final index at the third source. -/
@[expose] def Second :=
  Result.Second (firstInput := Input.ofSteps firstOriginal rfl) execution

/-- The original third paid trace with its same supplied source Owner and its final index at the fourth source. -/
@[expose] def Third :=
  Result.Third (firstInput := Input.ofSteps firstOriginal rfl) execution

/-- The original fourth paid trace with its same source Owner and actual final Owner at the original first base. -/
@[expose] def Fourth :=
  Result.Fourth (firstInput := Input.ofSteps firstOriginal rfl) execution

/-- The exact same-base OwnerPath type retaining the original source and actual returned final Owner. -/
@[expose] def Path :=
  Result.Path (firstInput := Input.ofSteps firstOriginal rfl) execution

/-- Four same-owner transported paid paths and their exact ordered append, retaining every complete factory result. -/
@[expose] def Result :=
  Result.Cache (firstInput := Input.ofSteps firstOriginal rfl) execution

namespace Result

/-- Retain the four identical paid trace transports once and append those same cached paths in geometric order. -/
def build : Result execution :=
  Trace.Result.Cache.build (firstInput := Input.ofSteps firstOriginal rfl) execution

/-- The old trace entry is exactly the shared append factory on this SAME original retained execution. -/
theorem build_eq :
    build execution = Trace.Result.Cache.build (firstInput := Input.ofSteps firstOriginal rfl) execution := by
  unfold build
  rfl

variable (result : Result execution)

/-- Read the identical first actual paid path after its certified physical endpoint transport. -/
@[expose] def first : First execution := result.1.val

/-- Read the identical second actual paid path after its certified physical endpoint transport. -/
@[expose] def second : Second execution := result.2.1.val

/-- Read the identical third actual paid path after its certified physical endpoint transport. -/
@[expose] def third : Third execution := result.2.2.1.val

/-- Read the identical fourth actual paid path after its certified physical endpoint transport. -/
@[expose] def fourth : Fourth execution := result.2.2.2.1.val

/-- Read the same cached ordered append of the four retained actual paid paths. -/
@[expose] def path : Path execution := result.2.2.2.2.val

/-- The first stored path is the original certified endpoint cast of the same actual first paid trace. -/
theorem first_eq : result.first = execution.second.seam.trace :=
  (Trace.Result.Cache.first_eq (firstInput := Input.ofSteps firstOriginal rfl)
      (execution := execution) result).trans
    (Seam.Receipt.trace_shared (left := circuit.first) (right := circuit.second)
      (previous := execution.first) (previousInitial := rfl) (nextInitial := rfl)
      execution.second.seam).symm

/-- The second stored path is the original certified endpoint cast of the same actual second paid trace. -/
theorem second_eq : result.second = execution.third.seam.trace :=
  (Trace.Result.Cache.second_eq (firstInput := Input.ofSteps firstOriginal rfl)
      (execution := execution) result).trans
    (Seam.Receipt.trace_shared (left := circuit.second) (right := circuit.third)
      (previous := execution.second.paid) (previousInitial := rfl) (nextInitial := rfl)
      execution.third.seam).symm

/-- The third stored path is the original certified endpoint cast of the same actual third paid trace. -/
theorem third_eq : result.third = execution.fourth.seam.trace :=
  (Trace.Result.Cache.third_eq (firstInput := Input.ofSteps firstOriginal rfl)
      (execution := execution) result).trans
    (Seam.Receipt.trace_shared (left := circuit.third) (right := circuit.fourth)
      (previous := execution.third.paid) (previousInitial := rfl) (nextInitial := rfl)
      execution.fourth.seam).symm

/-- The fourth stored path is the original certified endpoint cast of the same actual fourth paid trace. -/
theorem fourth_eq : result.fourth = execution.closing.trace :=
  (Trace.Result.Cache.fourth_eq (firstInput := Input.ofSteps firstOriginal rfl)
      (execution := execution) result).trans
    (Seam.Receipt.trace_shared (left := circuit.fourth) (right := circuit.first)
      (previous := execution.fourth.paid) (previousInitial := rfl) (nextInitial := rfl)
      execution.closing).symm

/-- The whole stored path is exactly the original append operation on these same four retained paths. -/
theorem path_eq : result.path = result.first.append (result.second.append (result.third.append result.fourth)) :=
  result.2.2.2.2.property

/-- The retained whole path preserves exactly the ordered vertices of the same original four actual paid traces. -/
theorem vertices_eq : result.path.vertices = execution.first.receipt.trace.vertices ++
    (execution.second.paid.receipt.trace.vertices ++
      (execution.third.paid.receipt.trace.vertices ++ execution.fourth.paid.receipt.trace.vertices)) :=
  Trace.Result.Cache.vertices_eq (firstInput := Input.ofSteps firstOriginal rfl)
    (execution := execution) result

/-- The actual retained ordered base vertices end at their identical original initial physical point. -/
theorem terminal_eq : Geometry.Rational.Polygon.Chain.terminal
    (coordinate site parameter 2 .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint.parameter)
    result.path.vertices =
      coordinate site parameter 2 .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint.parameter :=
  result.path.vertices_terminal

end Result

end Trace

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
