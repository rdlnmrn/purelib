module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Retained
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

/-! # Automatic positional completion of an actual shifted global request

The joined shifted geometry already retains its genuine closed root chain.
Only its exact parent-list equality transports that chain to the request's
nonempty shape. The same original request and its full old check outcomes
then receive occurrence completion without a Distinct or Ready premise.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Request

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)

variable {parameter increment : Canonical} {target : Paths.Frame (parameter + increment)}
    {basis : Differential 1} {count : Nat} {point : LiftedPoint 2} {root : Named}
    {geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root}
    {index floor rootStage : Nat}

/-- Complete the same selected request and retain it in its positional source-stage family.

The actual root chain comes from the same retained global geometry. Every
occurrence uses its original source bank entry and original Point/Query
owners. New stages execute their own endpoint Common comparisons; the
selected original attempt and all point-only outcomes remain unchanged.
-/
def occurrenceFamily (request : Request geometry index floor rootStage) :
    request.attempt.OccurrenceFamily :=
  let roots := Riemann.Topology.PreparedBankRootChains.RootChain.castChildren
    request.shape.property geometry.roots
  StageAttempt.completeOccurrenceFamily (parameter := parameter + increment) (frame := target)
    (basis := basis) (count := count) (parent := request.shape.val.1) (parents := request.shape.val.2)
    (covered := request.covered) (chain := request.chain) (index := index)
    (floor := floor) (rootStage := rootStage) request.attempt roots

/-- The selected family member keeps the exact original request attempt, including both old checking outcomes. -/
theorem occurrenceFamily_at (request : Request geometry index floor rootStage) :
    (request.occurrenceFamily index).val.1 = request.attempt :=
  StageAttempt.OccurrenceFamily.attempt_at (parameter := parameter + increment) (frame := target)
    (basis := basis) (count := count) (parent := request.shape.val.1) (parents := request.shape.val.2)
    (covered := request.covered) (chain := request.chain) (index := index)
    (floor := floor) (rootStage := rootStage) (attempt := request.attempt) request.occurrenceFamily

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Request

end
