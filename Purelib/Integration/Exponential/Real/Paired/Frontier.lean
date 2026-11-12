module

public import Purelib.Integration.Exponential.Real.Paired
import Purelib.Data.List.Attach
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Reverse
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Paired observations of retained numerical frontier cells

Frontier occurrences retain their original numerical owners. A finite bank
keeps the original paired state and origin ball, and a matching real state
can reuse its imaginary coordinate without a new request.
-/

public section

namespace Purelib.Integration.Exponential.Real.Paired.Frontier

open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Process
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Exponential.Real.Observation

set_option genInjectivity false in
/-- A retained paired point with its original numerical owner and unit witness. -/
structure Saved where
  /-- The actual retained original numerical point. -/
  owner : NumericalPoint Horner.Real.source
  /-- The original point lies in the unit interval. -/
  unit : 0 ≤ owner.point ∧ owner.point ≤ 1
  /-- The paired observation remains indexed by that owner. -/
  state : PointState owner unit

constructive_injectivity Saved

/-- Transfer an exact saved pair to another numerical owner only when its tag and real state agree. -/
@[expose] def matchState (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : Saved) : Option (PointState point unit) :=
  if same : tag saved.owner saved.unit = tag point unit then
    let paired : Coordinate.Paired (process (tag point unit)) (0 : Nat) := same ▸ saved.state.paired
    let origin : Coordinate.Observation.Response (process (tag point unit)) (.ball (0 : Nat)) :=
      same ▸ saved.state.originBall
    if realEq : paired.real = Horner.Real.originalState point.point unit point.state then
      some ⟨origin, paired, realEq⟩
    else none
  else none

/-- Find the first retained pair at the exact rational tag and original real state. -/
@[expose] def findState (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1) :
    List Saved → Option (PointState point unit)
  | [] => none
  | saved :: tail => match matchState point unit saved with
    | some matched => some matched
    | none => findState point unit tail

/-- Retain the original origin-ball reply from a saved point at the same rational tag. -/
@[expose] def matchOrigin (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : Saved) : Option (Coordinate.Observation.Response (process (tag point unit)) (.ball (0 : Nat))) :=
  if same : tag saved.owner saved.unit = tag point unit then some (same ▸ saved.state.originBall) else none

/-- Find the first original origin-ball reply owned by the requested rational point. -/
@[expose] def findOrigin (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1) :
    List Saved → Option (Coordinate.Observation.Response (process (tag point unit)) (.ball (0 : Nat)))
  | [] => none
  | saved :: tail => match matchOrigin point unit saved with
    | some observed => some observed
    | none => findOrigin point unit tail

/-- Reuse a retained origin ball to pair an actual real state without another ball readback. -/
@[expose] def fromOrigin (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (origin : Coordinate.Observation.Response (process (tag point unit)) (.ball (0 : Nat))) : PointState point unit :=
  ⟨origin, Coordinate.Paired.fromRealWith (Horner.Real.originalState point.point unit point.state)
      origin.val origin.property,
    Coordinate.Paired.fromRealWith_real _ _ _⟩

/-- A failed paired-point attempt and any state acquired before the failure. -/
abbrev AttemptFailure (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1) :=
  Failure × Option (PointState point unit)

/-- Continue a saved pair and retain it if its imaginary operation fails. -/
@[expose] def requestSaved (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : PointState point unit) (request : AccuracyRequest) :
    Program Query Reply (Except (AttemptFailure point unit) (PointState point unit)) :=
  (requestImaginary point unit saved request).map fun result => match result with
    | .error invalid => .error (invalid, some saved)
    | .ok next => .ok next

/-- Choose the original saved pair, origin ball or fresh attachment for one point.

Both supplied actions operate on the exact point owner. A failed continuation
returns its already attached pair, including the original cached origin ball. -/
@[expose] def observeWith {Question Reply Error : Type}
    (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (bank : List Saved) (attachPoint : Program Question Reply (Except Error (PointState point unit)))
    (advance : PointState point unit →
      Program Question Reply (Except (Error × Option (PointState point unit)) (PointState point unit))) :
    Program Question Reply (Except (Error × Option (PointState point unit)) (PointState point unit)) :=
  match findState point unit bank with
  | some saved => advance saved
  | none => match findOrigin point unit bank with
    | some origin => advance (fromOrigin point unit origin)
    | none => attachPoint.bind fun result =>
        match result with
        | .error invalid => .pure (.error (invalid, none))
        | .ok saved => advance saved

/-- Pair the actual numerical point and meet an imaginary request using its retained bank.

A matching paired state is retained; otherwise a matching origin ball is used
to attach the actual real state. Only a point absent from the bank reads its
origin ball. If the imaginary operation fails after attachment, the returned
failure retains the attached pair and its observed origin ball. -/
@[expose] def observe (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (bank : List Saved) (request : AccuracyRequest) :
    Program Query Reply (Except (AttemptFailure point unit) (PointState point unit)) :=
  observeWith point unit bank (attach point unit) (fun saved => requestSaved point unit saved request)

/-- An adequate matching paired-bank entry makes no Gaussian request. -/
theorem observe_reused (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (bank : List Saved) (saved : PointState point unit) (request : AccuracyRequest)
    (found : findState point unit bank = some saved)
    (adequate : saved.paired.imaginary.interval.width < request.tolerance) (oracle : Query → Reply) :
    ((observe point unit bank request).protocol.run oracle).value = .ok saved ∧
      ((observe point unit bank request).protocol.run oracle).trace = [] := by
  unfold observe observeWith
  rw [found]
  change ((requestSaved point unit saved request).protocol.run oracle).value = .ok saved ∧
    ((requestSaved point unit saved request).protocol.run oracle).trace = []
  have reused := requestImaginary_reused point unit saved request adequate oracle
  unfold requestSaved
  constructor
  · rw [Program.map_execution, Protocol.map_run_value, reused.1]
  · rw [Program.map_execution, Protocol.map_run_trace, reused.2]

/-- Every retained frontier cell has its actual numerical point in the unit interval. -/
theorem pointUnit (frontier : NumericalFrontier Horner.Real.source)
    (cell : IntegrationCell (NumericalPoint Horner.Real.source)) (member : cell ∈ frontier.cells) :
    0 ≤ cell.item.point ∧ cell.item.point ≤ 1 := by
  have mapped : cell.item.interval ∈ frontier.cells.map (fun entry => entry.item.interval) :=
    Purelib.Data.List.Map.mem_map_of_mem member
  have intervalMember : cell.item.interval ∈ frontier.partition.intervals := frontier.domains_eq ▸ mapped
  have valid := frontier.partition.valid cell.item.interval intervalMember
  exact ⟨Fraction.Order.Basic.le_trans _ _ _ valid.1 cell.item.start_le,
    Fraction.Order.Basic.le_trans _ _ _ cell.item.point_le_finish valid.2.2⟩

/-- An ordered original frontier-cell occurrence with its membership certificate. -/
abbrev Occurrence (frontier : NumericalFrontier Horner.Real.source) :=
  {cell : IntegrationCell (NumericalPoint Horner.Real.source) // cell ∈ frontier.cells}

/-- The original ordered frontier occurrences, without another numerical point request. -/
@[expose] def occurrences (frontier : NumericalFrontier Horner.Real.source) : List (Occurrence frontier) :=
  frontier.cells.attach

/-- Erasing occurrence certificates recovers the original ordered frontier cells. -/
theorem occurrences_cells (frontier : NumericalFrontier Horner.Real.source) :
    (occurrences frontier).map Subtype.val = frontier.cells :=
  Purelib.Data.List.attach_map_subtype_val frontier.cells

set_option genInjectivity false in
/-- A paired result for one actual occurrence of the original frontier. -/
structure Completed (frontier : NumericalFrontier Horner.Real.source) where
  /-- The actual original frontier occurrence. -/
  occurrence : Occurrence frontier
  /-- The paired observation remains owned by that occurrence's numerical point. -/
  state : PointState occurrence.val.item (pointUnit frontier occurrence.val occurrence.property)

constructive_injectivity Completed

set_option genInjectivity false in
/-- The retained progress of a finite paired frontier observation. -/
structure Progress (frontier : NumericalFrontier Horner.Real.source) where
  /-- Completed original occurrences in their original order. -/
  completed : List (Completed frontier)
  /-- Original occurrences not yet observed, including the point at a failure. -/
  pending : List (Occurrence frontier)
  /-- The exact retained paired bank after completed observations. -/
  bank : List Saved
  /-- A wrong source point or Gaussian operation, if observation stopped early. -/
  failure : Option Failure

constructive_injectivity Progress

/-- Visit the actual ordered frontier occurrences with the supplied paired-point action.

A failure keeps every prior pair and any pair attached at the failed occurrence;
the caller's two constructors choose how to represent completion and failure. -/
@[expose] def visitWith {Question Reply Error Outcome : Type}
    (frontier : NumericalFrontier Horner.Real.source)
    (observePoint : (point : NumericalPoint Horner.Real.source) →
      (unit : 0 ≤ point.point ∧ point.point ≤ 1) → List Saved →
        Program Question Reply (Except (Error × Option (PointState point unit)) (PointState point unit)))
    (finish : List (Completed frontier) → List Saved → Outcome)
    (failure : List (Completed frontier) → List (Occurrence frontier) → List Saved → Error → Outcome) :
    List (Occurrence frontier) → List (Completed frontier) → List Saved → Program Question Reply Outcome
  | [], completed, bank => .pure (finish completed.reverse bank)
  | occurrence :: rest, completed, bank =>
      let point := occurrence.val.item
      let unit := pointUnit frontier occurrence.val occurrence.property
      (observePoint point unit bank).bind fun result =>
        match result with
        | .error (invalid, acquired) =>
            let retained := match acquired with
              | none => bank
              | some state => ⟨point, unit, state⟩ :: bank
            .pure (failure completed.reverse (occurrence :: rest) retained invalid)
        | .ok state => visitWith frontier observePoint finish failure rest
            (⟨occurrence, state⟩ :: completed) (⟨point, unit, state⟩ :: bank)

/-- Visit original frontier occurrences in order, retaining completed pairs and the stopping point. -/
@[expose] def visit (frontier : NumericalFrontier Horner.Real.source) (request : AccuracyRequest)
    (remaining : List (Occurrence frontier)) (completed : List (Completed frontier)) (bank : List Saved) :
    Program Query Reply (Progress frontier) :=
  visitWith frontier (fun point unit bank => observe point unit bank request)
    (fun completed bank => ⟨completed, [], bank, none⟩)
    (fun completed pending bank invalid => ⟨completed, pending, bank, some invalid⟩)
    remaining completed bank

/-- A successful point visit continues with the exact returned pair and saved bank. -/
theorem visit_cons_value_of_ok (frontier : NumericalFrontier Horner.Real.source) (request : AccuracyRequest)
    (occurrence : Occurrence frontier) (rest : List (Occurrence frontier))
    (completed : List (Completed frontier)) (bank : List Saved) (oracle : Query → Reply)
    (next : PointState occurrence.val.item (pointUnit frontier occurrence.val occurrence.property))
    (returned : ((observe occurrence.val.item (pointUnit frontier occurrence.val occurrence.property) bank
      request).protocol.run oracle).value = .ok next) :
    ((visit frontier request (occurrence :: rest) completed bank).protocol.run oracle).value =
      ((visit frontier request rest (⟨occurrence, next⟩ :: completed)
        (⟨occurrence.val.item, pointUnit frontier occurrence.val occurrence.property, next⟩ :: bank)).protocol.run
          oracle).value := by
  unfold visit
  rw [visitWith, Program.bind_execution, Protocol.bind_run_value, returned]

/-- Observe the actual ordered cells of a retained numerical frontier. -/
@[expose] def observeFrontier (frontier : NumericalFrontier Horner.Real.source) (request : AccuracyRequest)
    (bank : List Saved) : Program Query Reply (Progress frontier) :=
  visit frontier request (occurrences frontier) [] bank

/-- Exact replay returns the same completed pairs, saved bank, pending cells and typed failure. -/
theorem observeFrontier_replay (frontier : NumericalFrontier Horner.Real.source) (request : AccuracyRequest)
    (bank : List Saved) (oracle : Query → Reply) :
    let program := observeFrontier frontier request bank
    program.protocol.replayExact (program.protocol.run oracle).trace = .ok (program.protocol.run oracle).value := by
  exact (observeFrontier frontier request bank).protocol.replayExact_run oracle

/-- Original replies continue a saved pair and satisfy the requested imaginary width. -/
theorem requestSaved_original_accurate (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) (saved : PointState point unit) (request : AccuracyRequest) :
    ∃ next, ((requestSaved point unit saved request).protocol.run original).value = .ok next ∧
      next.paired.imaginary.interval.width < request.tolerance := by
  obtain ⟨next, returned, accurate⟩ := requestImaginary_original_accurate point unit saved request
  refine ⟨next, ?_, accurate⟩
  unfold requestSaved
  rw [Program.map_execution, Protocol.map_run_value, returned]

/-- Original replies successfully pair the actual point and satisfy the imaginary request. -/
theorem observe_original_accurate (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) (bank : List Saved) (request : AccuracyRequest) :
    ∃ next, ((observe point unit bank request).protocol.run original).value = .ok next ∧
      next.paired.imaginary.interval.width < request.tolerance := by
  cases stateFound : findState point unit bank with
  | some saved =>
      unfold observe observeWith
      rw [stateFound]
      exact requestSaved_original_accurate point unit saved request
  | none =>
      cases originFound : findOrigin point unit bank with
      | some origin =>
          unfold observe observeWith
          rw [stateFound, originFound]
          exact requestSaved_original_accurate point unit (fromOrigin point unit origin) request
      | none =>
          obtain ⟨next, returned, accurate⟩ :=
            requestSaved_original_accurate point unit (originalAttached point unit) request
          refine ⟨next, ?_, accurate⟩
          unfold observe observeWith
          rw [stateFound, originFound, Program.bind_execution, Protocol.bind_run_value, attach_original]
          exact returned

/-- Original replies finish the retained finite visit without a paired-source failure. -/
theorem visit_original_finished (frontier : NumericalFrontier Horner.Real.source) (request : AccuracyRequest)
    (remaining : List (Occurrence frontier)) (completed : List (Completed frontier)) (bank : List Saved) :
    let progress := ((visit frontier request remaining completed bank).protocol.run original).value
    progress.pending = [] ∧ progress.failure = none := by
  induction remaining generalizing completed bank with
  | nil => exact ⟨rfl, rfl⟩
  | cons occurrence rest induction =>
      let point := occurrence.val.item
      let unit := pointUnit frontier occurrence.val occurrence.property
      obtain ⟨next, returned, _⟩ := observe_original_accurate point unit bank request
      rw [visit_cons_value_of_ok frontier request occurrence rest completed bank original next returned]
      exact induction (⟨occurrence, next⟩ :: completed) (⟨point, unit, next⟩ :: bank)

/-- Original Gaussian replies complete all actual frontier occurrences. -/
theorem observeFrontier_original_finished (frontier : NumericalFrontier Horner.Real.source)
    (request : AccuracyRequest) (bank : List Saved) :
    let progress := ((observeFrontier frontier request bank).protocol.run original).value
    progress.pending = [] ∧ progress.failure = none :=
  visit_original_finished frontier request (occurrences frontier) [] bank

/-- Original replies preserve every frontier occurrence in its original order. -/
theorem visit_original_order (frontier : NumericalFrontier Horner.Real.source) (request : AccuracyRequest)
    (remaining : List (Occurrence frontier)) (completed : List (Completed frontier)) (bank : List Saved) :
    let progress := ((visit frontier request remaining completed bank).protocol.run original).value
    progress.completed.map (fun entry => entry.occurrence) =
      completed.reverse.map (fun entry => entry.occurrence) ++ remaining := by
  induction remaining generalizing completed bank with
  | nil =>
      change completed.reverse.map (fun entry => entry.occurrence) =
        completed.reverse.map (fun entry => entry.occurrence) ++ []
      exact (Purelib.Data.List.Append.append_nil _).symm
  | cons occurrence rest induction =>
      let point := occurrence.val.item
      let unit := pointUnit frontier occurrence.val occurrence.property
      obtain ⟨next, returned, _⟩ := observe_original_accurate point unit bank request
      rw [visit_cons_value_of_ok frontier request occurrence rest completed bank original next returned]
      dsimp only
      rw [induction (⟨occurrence, next⟩ :: completed) (⟨point, unit, next⟩ :: bank)]
      rw [Purelib.Data.List.Reverse.reverse_cons, Purelib.Data.List.Map.map_append,
        Purelib.Data.List.Append.append_assoc]
      rfl

/-- Original paired observation returns the original ordered frontier-cell occurrences. -/
theorem observeFrontier_original_order (frontier : NumericalFrontier Horner.Real.source)
    (request : AccuracyRequest) (bank : List Saved) :
    let progress := ((observeFrontier frontier request bank).protocol.run original).value
    progress.completed.map (fun entry => entry.occurrence) = occurrences frontier := by
  exact visit_original_order frontier request (occurrences frontier) [] bank

/-- Original replies preserve the requested width for every completed frontier occurrence. -/
theorem visit_original_accurate (frontier : NumericalFrontier Horner.Real.source) (request : AccuracyRequest)
    (remaining : List (Occurrence frontier)) (completed : List (Completed frontier)) (bank : List Saved)
    (prior : ∀ entry ∈ completed, entry.state.paired.imaginary.interval.width < request.tolerance) :
    let progress := ((visit frontier request remaining completed bank).protocol.run original).value
    ∀ entry ∈ progress.completed, entry.state.paired.imaginary.interval.width < request.tolerance := by
  induction remaining generalizing completed bank with
  | nil =>
      dsimp only
      intro entry member
      exact prior entry ((Purelib.Data.List.Reverse.mem_reverse completed).mp member)
  | cons occurrence rest induction =>
      let point := occurrence.val.item
      let unit := pointUnit frontier occurrence.val occurrence.property
      obtain ⟨next, returned, accurate⟩ := observe_original_accurate point unit bank request
      have prior' : ∀ entry ∈ (⟨occurrence, next⟩ : Completed frontier) :: completed,
          entry.state.paired.imaginary.interval.width < request.tolerance := by
        intro entry member
        cases Purelib.Data.List.Membership.mem_cons.mp member with
        | inl same =>
            cases same
            exact accurate
        | inr member => exact prior entry member
      rw [visit_cons_value_of_ok frontier request occurrence rest completed bank original next returned]
      exact induction (⟨occurrence, next⟩ :: completed) (⟨point, unit, next⟩ :: bank) prior'

/-- Every paired observation of an original frontier meets the positive imaginary request. -/
theorem observeFrontier_original_accurate (frontier : NumericalFrontier Horner.Real.source)
    (request : AccuracyRequest) (bank : List Saved) :
    let progress := ((observeFrontier frontier request bank).protocol.run original).value
    ∀ entry ∈ progress.completed, entry.state.paired.imaginary.interval.width < request.tolerance := by
  apply visit_original_accurate frontier request (occurrences frontier) [] bank
  intro entry impossible
  nomatch impossible

end Purelib.Integration.Exponential.Real.Paired.Frontier

end
