module
public import Purelib.Integration.Cell.Source.Initial
public import Purelib.Computation.Query.Program
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing initial-region source replacement

The original frontier, initial endpoint, source agreement and target point
bank are fixed. Unmarked cells reuse the original reading; marked cells reuse
a matching target point or request that exact rational tag. Returned target
points construct the same original replacement frontier and ordered cells.
-/

public section

namespace Purelib.Integration.SourceFrontier.Initial.Observation

open Purelib.Computation.Query
open Purelib.Data.Rat

set_option genInjectivity false in
/-- A target-source reply at a tag other than the requested rational point. -/
structure InvalidTag where
  /-- The rational target point actually requested. -/ requested : Fraction.Rational
  /-- The tag returned by the target source. -/ reported : Fraction.Rational
  /-- The returned point differs from the requested point. -/ different : reported ≠ requested

constructive_injectivity InvalidTag

/-- Read the original target source at a displayed rational point. -/
@[expose] def originalReply (target : Fraction.Rational → Fraction.Rational) (point : Fraction.Rational) :
    SourcePoint target :=
  SourcePoint.observe target ⟨point, point⟩ point le_rfl le_rfl

/-- A returned replacement cell certified as the original cache-aware cell. -/
abbrev CertifiedCell {original target : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint target))
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) :=
  {cell : IntegrationCell (SourcePoint target) // cell = cellCached cached endpoint global agreement retained}

/-- A returned target point supplies the exact original replacement cell. -/
theorem returnedCell_eq {original target : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint target))
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) (reply : SourcePoint target) :
    cellCached [reply] endpoint global agreement retained = cellCached cached endpoint global agreement retained :=
  (cellCached_eq [reply] endpoint global agreement retained).trans
    (cellCached_eq cached endpoint global agreement retained).symm

/-- Replace one original cell using the exact saved reading or one returned target-source point. -/
@[expose] def cell {original target : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint target))
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) :
    Program Fraction.Rational (SourcePoint target)
      (Except InvalidTag (CertifiedCell cached endpoint global agreement retained)) :=
  if _marked : retained.item.interval.start ≤ endpoint then
    match SourcePoint.findCached cached retained.item.point with
    | some _ => .pure (.ok ⟨cellCached cached endpoint global agreement retained, rfl⟩)
    | none => .request retained.item.point fun reply =>
        if same : reply.point = retained.item.point then
          .pure (.ok ⟨cellCached [reply] endpoint global agreement retained,
            returnedCell_eq cached endpoint global agreement retained reply⟩)
        else .pure (.error ⟨retained.item.point, reply.point, same⟩)
  else
    .pure (.ok ⟨cellCached cached endpoint global agreement retained, rfl⟩)

/-- Original target execution returns the original cache-aware replacement cell. -/
theorem cell_original {original target : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint target))
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) :
    ((cell cached endpoint global agreement retained).protocol.run (originalReply target)).value =
      .ok ⟨cellCached cached endpoint global agreement retained, rfl⟩ := by
  unfold cell
  by_cases marked : retained.item.interval.start ≤ endpoint
  · rw [dif_pos marked]
    cases found : SourcePoint.findCached cached retained.item.point with
    | some point => rfl
    | none =>
        change (((if same : (originalReply target retained.item.point).point = retained.item.point then
          (Program.pure (.ok ⟨cellCached [originalReply target retained.item.point] endpoint global agreement retained,
            returnedCell_eq cached endpoint global agreement retained (originalReply target retained.item.point)⟩) :
            Program Fraction.Rational (SourcePoint target)
              (Except InvalidTag (CertifiedCell cached endpoint global agreement retained)))
          else Program.pure (.error ⟨retained.item.point,
            (originalReply target retained.item.point).point, same⟩)).protocol).run
            (originalReply target)).value = _
        have same : (originalReply target retained.item.point).point = retained.item.point := rfl
        rw [dif_pos same]
        apply congrArg Except.ok
        apply Subtype.ext
        exact returnedCell_eq cached endpoint global agreement retained (originalReply target retained.item.point)
  · rw [dif_neg marked]
    rfl

/-- Returned ordered replacement cells certified against the exact original retained cells. -/
abbrev Cells {original target : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint target))
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (retained : List (IntegrationCell (SourcePoint original))) :=
  {cells : List (IntegrationCell (SourcePoint target)) //
    cells = retained.map (cellCached cached endpoint global agreement)}

/-- Prepend one returned replacement cell to the already returned ordered cells. -/
@[expose] def prepend {original target : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint target))
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) (remaining : List (IntegrationCell (SourcePoint original)))
    (cell : CertifiedCell cached endpoint global agreement retained)
    (tail : Cells cached endpoint global agreement remaining) :
    Cells cached endpoint global agreement (retained :: remaining) :=
  ⟨cell.val :: tail.val, congrArg₂ List.cons cell.property tail.property⟩

/-- Observe the ordered original cells, stopping on the first wrong target-source tag. -/
@[expose] def cells {original target : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint target))
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point) :
    (retained : List (IntegrationCell (SourcePoint original))) → Program Fraction.Rational (SourcePoint target)
      (Except InvalidTag (Cells cached endpoint global agreement retained))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | retained :: remaining => (cell cached endpoint global agreement retained).bind fun result =>
      match result with
      | .error invalid => .pure (.error invalid)
      | .ok replacement => (cells cached endpoint global agreement remaining).map fun after =>
          after.map (prepend cached endpoint global agreement retained remaining replacement)

/-- Original target execution returns all original replacement cells in order. -/
theorem cells_original {original target : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint target))
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point) :
    ∀ retained : List (IntegrationCell (SourcePoint original)),
      ((cells cached endpoint global agreement retained).protocol.run (originalReply target)).value =
        .ok ⟨retained.map (cellCached cached endpoint global agreement), rfl⟩
  | [] => rfl
  | retained :: remaining => by
      change (((cell cached endpoint global agreement retained).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok replacement => (cells cached endpoint global agreement remaining).map fun after =>
            after.map (prepend cached endpoint global agreement retained remaining replacement)).protocol.run
              (originalReply target)).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, cell_original]
      rw [Program.map_execution, Protocol.map_run_value, cells_original cached endpoint global agreement remaining]
      rfl

/-- Assemble the target-source frontier from the returned ordered replacement cells. -/
@[expose] def frontierFromCells {original target : Fraction.Rational → Fraction.Rational}
    (cached : List (SourcePoint target)) (retained : SourceFrontier original) (endpoint : Fraction.Rational)
    (global : Purelib.Data.Rat.Interval) (agreement : ∀ point, endpoint < point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point))
    (returned : Cells cached endpoint global agreement retained.cells) : SourceFrontier target := by
  let actual := replaceCached cached retained endpoint global agreement bounded
  have cells_eq : returned.val = actual.cells := returned.property
  exact
    { partition := retained.partition
      cells := returned.val
      domains_eq := (congrArg (List.map (fun cell : IntegrationCell (SourcePoint target) => cell.item.interval))
        cells_eq).trans actual.domains_eq
      weight_eq := by
        intro cell member
        exact actual.weight_eq cell (cells_eq ▸ member)
      source_range := by
        intro cell member point lower upper
        exact actual.source_range cell (cells_eq ▸ member) point lower upper }

/-- The returned replacement cells assemble into the exact original target-source frontier. -/
theorem frontierFromCells_eq {original target : Fraction.Rational → Fraction.Rational}
    (cached : List (SourcePoint target)) (retained : SourceFrontier original) (endpoint : Fraction.Rational)
    (global : Purelib.Data.Rat.Interval) (agreement : ∀ point, endpoint < point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point))
    (returned : Cells cached endpoint global agreement retained.cells) :
    frontierFromCells cached retained endpoint global agreement bounded returned =
      replaceCached cached retained endpoint global agreement bounded :=
  SourceFrontier.ext _ _ rfl returned.property

/-- A returned frontier certified as the original cache-aware source replacement. -/
abbrev CertifiedFrontier {original target : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint target))
    (retained : SourceFrontier original) (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)) :=
  {frontier : SourceFrontier target // frontier = replaceCached cached retained endpoint global agreement bounded}

/-- Observe the original initial-region source replacement and its actual target-source reads. -/
@[expose] def computation {original target : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint target))
    (retained : SourceFrontier original) (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)) :
    Program Fraction.Rational (SourcePoint target) (Except InvalidTag
      (CertifiedFrontier cached retained endpoint global agreement bounded)) :=
  (cells cached endpoint global agreement retained.cells).map fun returned =>
    returned.map fun result => ⟨frontierFromCells cached retained endpoint global agreement bounded result,
      frontierFromCells_eq cached retained endpoint global agreement bounded result⟩

/-- Original target execution returns the complete original cache-aware replacement frontier. -/
theorem computation_original {original target : Fraction.Rational → Fraction.Rational}
    (cached : List (SourcePoint target))
    (retained : SourceFrontier original) (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)) :
    ((computation cached retained endpoint global agreement bounded).protocol.run (originalReply target)).value =
      .ok ⟨replaceCached cached retained endpoint global agreement bounded, rfl⟩ := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_value, cells_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact frontierFromCells_eq cached retained endpoint global agreement bounded _

/-- Exact replay recovers the complete original target frontier without repeating its displayed requests. -/
theorem computation_replay {original target : Fraction.Rational → Fraction.Rational}
    (cached : List (SourcePoint target))
    (retained : SourceFrontier original) (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)) :
    (computation cached retained endpoint global agreement bounded).protocol.replayExact
      ((computation cached retained endpoint global agreement bounded).protocol.run (originalReply target)).trace =
        .ok (.ok ⟨replaceCached cached retained endpoint global agreement bounded, rfl⟩) := by
  rw [(computation cached retained endpoint global agreement bounded).protocol.replayExact_run, computation_original]

/-- Replies outside the actual replacement trace preserve the complete frontier and ordered trace. -/
theorem payload_erasure {original target : Fraction.Rational → Fraction.Rational} (cached : List (SourcePoint target))
    (retained : SourceFrontier original) (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point))
    {Payload : Type} (payload : Payload) (outside : Payload → Fraction.Rational → SourcePoint target) :
    (computation cached retained endpoint global agreement bounded).protocol.run (Boundary.Trace.overlay
      ((computation cached retained endpoint global agreement bounded).protocol.run (originalReply target)).trace
      (outside payload)) =
      (computation cached retained endpoint global agreement bounded).protocol.run (originalReply target) :=
  (computation cached retained endpoint global agreement bounded).protocol.annotation_erasure
    (originalReply target) payload outside

end Purelib.Integration.SourceFrontier.Initial.Observation

end
