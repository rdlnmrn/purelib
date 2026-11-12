module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained.Transport
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Topology.PreparedRefinementRootChains

/-! # Completed stage families of one actual shifted source request

The actual request retains its original covered-stage factory. One genuine
completion of that same attempt therefore supplies the selected geometric
payment for its original canonical stage family. The selected attempt,
its acquisitions and its stored Stage are retained as a whole; other
stages keep their own Targets, prepared cells, bank and checking caches.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Request

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)

/-- Extend one genuine completion of this same retained request to its actual canonical stage family.

The original request factory supplies the canonical-preparation evidence.
At the selected stage the entire supplied completion is retained. Other
stages construct their own original attempts and numerical admissions,
using the selected geometric acquisitions and their own ready Commons.
The initial completion remains a genuine input; readiness and signed
agreement are not inferred from point labels or a closed path.
-/
public def completedFamily
    {parameter increment : Canonical} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {point : LiftedPoint 2} {root : Named}
    {geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root}
    {index floor rootStage : Nat} (request : Request geometry index floor rootStage)
    (completed : StageAttempt.Completion request.attempt) : request.attempt.CompletedFamily :=
  let selected : StageAttempt.Completed (parameter := parameter + increment) (frame := target)
      (basis := basis) (count := count) request.covered request.chain index floor rootStage :=
    ⟨request.attempt, completed⟩
  StageAttempt.Completed.family (parameter := parameter + increment) (frame := target)
    (basis := basis) (count := count) (parent := request.shape.val.1) (parents := request.shape.val.2)
    (index := index) (floor := floor) (rootStage := rootStage)
    request.covered request.chain selected request.attempt_eq

/-- The selected family member retains the same whole request and supplied completion.

Every original stored acquisition and Stage belongs to that same Completed
value; equality is not restricted to its attempt or displayed source list.
-/
public theorem completedFamily_at
    {parameter increment : Canonical} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {point : LiftedPoint 2} {root : Named}
    {geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root}
    {index floor rootStage : Nat} (request : Request geometry index floor rootStage)
    (completed : StageAttempt.Completion request.attempt) :
    (request.completedFamily completed index).val =
      (⟨request.attempt, completed⟩ : StageAttempt.Completed (parameter := parameter + increment)
        (frame := target) (basis := basis) (count := count)
        request.covered request.chain index floor rootStage) := by
  unfold completedFamily
  exact StageAttempt.Completed.family_at (parameter := parameter + increment) (frame := target)
    (basis := basis) (count := count) (parent := request.shape.val.1) (parents := request.shape.val.2)
    (index := index) (floor := floor) (rootStage := rootStage)
    request.covered request.chain ⟨request.attempt, completed⟩ request.attempt_eq

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Request
