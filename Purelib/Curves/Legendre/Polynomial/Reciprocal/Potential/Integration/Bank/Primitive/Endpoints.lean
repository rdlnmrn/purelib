module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Materialized
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Fold
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Data.Nat.Order

/-! # Original endpoint requests before reciprocal-bank materialization

The same global numerator is supplied to both endpoints of each literal
planned coordinate. Each original Point callback is evaluated once at zero
and once at one, retaining both complete Points and their requested primitive
observations. Their finite stage maximum precedes every reciprocal cell.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point (PrimitiveEndpoint)
open Purelib.Integration.Polynomial.Gaussian.Cell

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

namespace EndpointRequests

/-- Two actual endpoint Points, their same-numerator primitive requests and the literal remaining request bank.

Even coincident endpoints retain their two original callback results. The
complete factory identities identify each original Point without rerunning
its callback when a later cell consumes these requested observations.
-/
@[expose] def Entry {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    (data : ParentData cap sourceDifferential count parent)
    (coordinate : Spatial.Coordinate data.segment.comparison.first data.segment.comparison.last)
    (coefficient : Polynomial)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (coordinate.point input))
    (target : Coordinate) (remaining : Type 3) : Type 3 :=
  (first : {value : Point data.terminal.neighborhood.patch (coordinate.point 0) //
    value = points 0 (by decide +kernel) (by decide +kernel)}) ×
  (last : {value : Point data.terminal.neighborhood.patch (coordinate.point 1) //
    value = points 1 (by decide +kernel) (by decide +kernel)}) ×
  (_first : PrimitiveEndpoint first.val 0 coefficient floor target) ×
  (_last : PrimitiveEndpoint last.val 0 coefficient floor target) × remaining

end EndpointRequests

/-- Every occurrence retains both endpoint requests on its original planned coordinate and Point family. -/
@[expose] def EndpointRequests (coefficient : Polynomial) (target : Coordinate) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (planned : Plan error errorPositive floor bank) → LiftedCells bank planned → Type 3 := by
  intro parents bank
  induction bank with
  | nil => exact fun _ _ => PUnit
  | cons data rest ih =>
      intro planned paths
      exact EndpointRequests.Entry (floor := floor) data planned.2.1 coefficient paths.2.2.2.1 target
        (ih planned.2.2.2 paths.2.2.2.2)

namespace EndpointRequests

/-- Acquire both endpoint requests before invoking the original delayed tail traversal. -/
private def buildStep {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (paths : LiftedCells (.cons data rest) planned)
    (coefficient : Polynomial) (target : Coordinate) (positive : 0 < target)
    (finishTail : Unit → EndpointRequests coefficient target rest planned.2.2.2 paths.2.2.2.2) :
    EndpointRequests coefficient target (.cons data rest) planned paths :=
  let first := paths.2.2.2.1 0 (by decide +kernel) (by decide +kernel)
  let last := paths.2.2.2.1 1 (by decide +kernel) (by decide +kernel)
  let firstRequest := PrimitiveEndpoint.build first 0 coefficient floor target positive
  let lastRequest := PrimitiveEndpoint.build last 0 coefficient floor target positive
  let remaining := finishTail ()
  ⟨⟨first, rfl⟩, ⟨last, rfl⟩, firstRequest, lastRequest, remaining⟩

/-- Select the ordered original endpoint Points and requests without constructing a reciprocal model or cell.

The supplied numerator is reused unchanged at every occurrence. Each head
retains its two actual Point values and observations before the literal tail
is evaluated; the original global regular sample is not rebuilt.
-/
def build (coefficient : Polynomial) (target : Coordinate) (positive : 0 < target) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (planned : Plan error errorPositive floor bank) → (paths : LiftedCells bank planned) →
          EndpointRequests coefficient target bank planned paths := by
  intro parents bank
  refine Bank.fold (motive := fun {_parents} bank =>
    (planned : Plan error errorPositive floor bank) → (paths : LiftedCells bank planned) →
      EndpointRequests coefficient target bank planned paths) ?_ ?_ bank
  · exact fun _ _ => ⟨⟩
  · intro parent parents data rest finishTail planned paths
    exact buildStep data rest planned paths coefficient target positive
      (fun _ => finishTail () planned.2.2.2 paths.2.2.2.2)

/-- Read the maximum original source stage from this same retained request bank, with the original floor at nil. -/
def maximum (coefficient : Polynomial) (target : Coordinate) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (planned : Plan error errorPositive floor bank) → (paths : LiftedCells bank planned) →
          EndpointRequests coefficient target bank planned paths → Nat := by
  intro parents bank
  refine Bank.fold (motive := fun {_parents} bank =>
    (planned : Plan error errorPositive floor bank) → (paths : LiftedCells bank planned) →
      EndpointRequests coefficient target bank planned paths → Nat) ?_ ?_ bank
  · exact fun _ _ _ => floor
  · intro parent parents data rest finishTail planned paths cached
    exact Nat.max (Nat.max cached.2.2.1.source.stage cached.2.2.2.1.source.stage)
      (finishTail () planned.2.2.2 paths.2.2.2.2 cached.2.2.2.2)

/-- A nonempty maximum reads both actual head request stages and the same ordered remaining request bank. -/
theorem maximum_cons (coefficient : Polynomial) (target : Coordinate)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest)) (paths : LiftedCells (.cons data rest) planned)
    (cached : EndpointRequests coefficient target (.cons data rest) planned paths) :
    maximum coefficient target (.cons data rest) planned paths cached =
      Nat.max (Nat.max cached.2.2.1.source.stage cached.2.2.2.1.source.stage)
        (maximum coefficient target rest planned.2.2.2 paths.2.2.2.2 cached.2.2.2.2) := by
  let Family : {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 := fun {_parents} bank =>
    (planned : Plan error errorPositive floor bank) → (paths : LiftedCells bank planned) →
      EndpointRequests coefficient target bank planned paths → Nat
  let empty : Family .nil := fun _ _ _ => floor
  let step : {parent : Parent (Fibre.frameCurve frame) sourceDifferential} →
      {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (data : ParentData cap sourceDifferential count parent) →
      (rest : Bank cap sourceDifferential count parents) →
      (Unit → Family rest) → Family (.cons data rest) :=
    fun {_parent} {_parents} _data _rest finishTail planned paths cached =>
      Nat.max (Nat.max cached.2.2.1.source.stage cached.2.2.2.1.source.stage)
        (finishTail () planned.2.2.2 paths.2.2.2.2 cached.2.2.2.2)
  have folded := Bank.fold_cons (motive := Family) empty step data rest
  exact congrArg (fun next : Family (.cons data rest) => next planned paths cached) folded

/-- Both actual first-head source stages are paid by this same original bank's finite maximum. -/
theorem head_le (coefficient : Polynomial) (target : Coordinate)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest)) (paths : LiftedCells (.cons data rest) planned)
    (cached : EndpointRequests coefficient target (.cons data rest) planned paths) :
    Nat.max cached.2.2.1.source.stage cached.2.2.2.1.source.stage ≤
      maximum coefficient target (.cons data rest) planned paths cached :=
  Eq.mp (congrArg (fun value : Nat =>
    Nat.max cached.2.2.1.source.stage cached.2.2.2.1.source.stage ≤ value)
      (maximum_cons coefficient target data rest planned paths cached).symm) (Data.Nat.Order.le_max_left _ _)

/-- The actual remaining request maximum is no later than the same retained full bank's maximum. -/
theorem tail_le (coefficient : Polynomial) (target : Coordinate)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest)) (paths : LiftedCells (.cons data rest) planned)
    (cached : EndpointRequests coefficient target (.cons data rest) planned paths) :
    maximum coefficient target rest planned.2.2.2 paths.2.2.2.2 cached.2.2.2.2 ≤
      maximum coefficient target (.cons data rest) planned paths cached :=
  Eq.mp (congrArg (fun value : Nat =>
    maximum coefficient target rest planned.2.2.2 paths.2.2.2.2 cached.2.2.2.2 ≤ value)
      (maximum_cons coefficient target data rest planned paths cached).symm) (Data.Nat.Order.le_max_right _ _)

end EndpointRequests

/-- Select and retain all endpoint requests before materializing at their genuinely paid enlarged reciprocal floor.

The old regular sample, coefficient and physical request bank remain the
same input caches. Both actual endpoint Points and their original source
requests precede every reciprocal Head. The consumer receives those same
requests, their stage payment and the once-built checked/original bank.
-/
def withEndpoints {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    {target : Coordinate} {positive : 0 < target / 4} {pFloor : Nat} {box : Box}
    (cached : Primitive target positive pFloor box bank planned)
    (endpointTarget : Coordinate) (endpointPositive : 0 < endpointTarget) (paths : LiftedCells bank planned)
    {Result : Type u}
    (consume : (endpoints : EndpointRequests cached.2.2.2.1.val endpointTarget bank planned paths) →
      (common : Nat) → (originalPaid : Plan.commonFloor bank planned ≤ common) →
      Requests.maximum bank planned cached.2.2.2.2 ≤ common →
      EndpointRequests.maximum cached.2.2.2.1.val endpointTarget bank planned paths endpoints ≤ common →
      Materialized cached.2.2.1.val cached.2.2.2.1 (target / 4) positive common
        bank values planned cached.2.2.2.2 paths originalPaid → Result) : Result :=
  let endpoints := EndpointRequests.build cached.2.2.2.1.val endpointTarget endpointPositive bank planned paths
  let endpointStage := EndpointRequests.maximum cached.2.2.2.1.val endpointTarget bank planned paths endpoints
  let previous := commonFloor cached
  let common := Nat.max previous.val endpointStage
  have inherited : previous.val ≤ common := Data.Nat.Order.le_max_left _ _
  have originalPaid : Plan.commonFloor bank planned ≤ common := (original_le cached previous).trans inherited
  have physicalPaid : Requests.maximum bank planned cached.2.2.2.2 ≤ common :=
    (requests_le cached previous).trans inherited
  have endpointPaid : EndpointRequests.maximum cached.2.2.2.1.val endpointTarget bank planned paths endpoints ≤
      common := Data.Nat.Order.le_max_right _ _
  let actual := materialize bank values planned cached common originalPaid physicalPaid paths
  consume endpoints common originalPaid physicalPaid endpointPaid actual

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

end
