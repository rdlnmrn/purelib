module
public import Purelib.Integration.Cell.Numerical.Common.Operational
public import Purelib.Computation.Query.Program
public import Purelib.Data.List.GetD
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing joint numerical source comparison

The original common refinement, point equivalences, coherence laws and joint
budget are fixed inputs. Each indexed common occurrence requests its own
actual joint scheduler result. Returned joint states and interval readbacks
are retained in the comparison that pays for the two integration answers.
-/

public section

namespace Purelib.Integration.NumericalFrontier.Common.Operational.Observation

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat

/-- An index into the original ordered numerical common-point observations. -/
abbrev Query {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) := Fin common.readings.length

/-- The original common-point reading selected by its exact occurrence index. -/
@[expose] def reading {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (index : Query common) : CommonReading left right request :=
  common.readings.get index

/-- The actual original joint scheduler result for an indexed common-point observation. -/
@[expose] def joint {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (index : Query common) : JointReading left right request budget :=
  jointForReading budget equivalent leftCoherent rightCoherent (reading common index)

/-- One returned joint state certified as the actual original scheduler result at its occurrence. -/
abbrev Selected {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) (index : Query common) :=
  {result : JointReading left right request budget //
    result = joint common budget equivalent leftCoherent rightCoherent index}

set_option genInjectivity false in
/-- A returned joint scheduler result and its original common-occurrence index. -/
structure Reply {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) where
  /-- The indexed original common-point occurrence. -/ index : Query common
  /-- The actual joint state and its two cached interval readbacks. -/ result :
    Selected common budget equivalent leftCoherent rightCoherent index

constructive_injectivity Reply

set_option genInjectivity false in
/-- A joint reply for a different original common-point occurrence. -/
structure Invalid {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) where
  /-- The requested original occurrence. -/ requested : Query common
  /-- The reported original occurrence. -/ reported : Query common
  /-- The returned occurrence differs from the request. -/ different : reported ≠ requested

constructive_injectivity Invalid

/-- Execute the original joint scheduler once for the displayed occurrence. -/
@[expose] def originalReply {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) (index : Query common) :
    Reply common budget equivalent leftCoherent rightCoherent :=
  ⟨index, ⟨joint common budget equivalent leftCoherent rightCoherent index, rfl⟩⟩

/-- Ordered returned joint results certified against the original indexed scheduler calls. -/
abbrev Batch {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) (indices : List (Query common)) :=
  {results : List (JointReading left right request budget) //
    results = indices.map (joint common budget equivalent leftCoherent rightCoherent)}

/-- Prepend the returned joint state to the already returned indexed results. -/
@[expose] def prepend {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (index : Query common) (remaining : List (Query common))
    (result : Selected common budget equivalent leftCoherent rightCoherent index)
    (tail : Batch common budget equivalent leftCoherent rightCoherent remaining) :
    Batch common budget equivalent leftCoherent rightCoherent (index :: remaining) :=
  ⟨result.val :: tail.val, congrArg₂ List.cons result.property tail.property⟩

/-- Observe every original joint request in order, stopping at the first wrong occurrence. -/
@[expose] def batch {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    (indices : List (Query common)) → Program (Query common) (Reply common budget equivalent leftCoherent rightCoherent)
      (Except (Invalid common) (Batch common budget equivalent leftCoherent rightCoherent indices))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | index :: remaining => .request index fun reply =>
      if same : reply.index = index then
        (batch common budget equivalent leftCoherent rightCoherent remaining).map fun after =>
          after.map (prepend common budget equivalent leftCoherent rightCoherent index remaining (same ▸ reply.result))
      else .pure (.error ⟨index, reply.index, same⟩)

/-- Original execution retains every actual joint result in the original indexed order. -/
theorem batch_original {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    ∀ indices : List (Query common),
      ((batch common budget equivalent leftCoherent rightCoherent indices).protocol.run
        (originalReply common budget equivalent leftCoherent rightCoherent)).value =
          .ok ⟨indices.map (joint common budget equivalent leftCoherent rightCoherent), rfl⟩
  | [] => rfl
  | index :: remaining => by
      change (((if same : (originalReply common budget equivalent leftCoherent rightCoherent index).index = index then
        (batch common budget equivalent leftCoherent rightCoherent remaining).map fun after =>
          after.map (prepend common budget equivalent leftCoherent rightCoherent index remaining
            (same ▸ (originalReply common budget equivalent leftCoherent rightCoherent index).result))
        else Program.pure (.error ⟨index,
          (originalReply common budget equivalent leftCoherent rightCoherent index).index, same⟩)).protocol).run
            (originalReply common budget equivalent leftCoherent rightCoherent)).value = _
      have same : (originalReply common budget equivalent leftCoherent rightCoherent index).index = index := rfl
      rw [dif_pos same, Program.map_execution, Protocol.map_run_value,
        batch_original common budget equivalent leftCoherent rightCoherent remaining]
      rfl

/-- Original execution requests the indexed joint scheduler results in their exact supplied order. -/
theorem batch_original_trace {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    ∀ indices : List (Query common),
      ((batch common budget equivalent leftCoherent rightCoherent indices).protocol.run
        (originalReply common budget equivalent leftCoherent rightCoherent)).trace =
          indices.map (fun index => ⟨index, originalReply common budget equivalent leftCoherent rightCoherent index⟩)
  | [] => rfl
  | index :: remaining => by
      change ⟨index, originalReply common budget equivalent leftCoherent rightCoherent index⟩ ::
        (((if same : (originalReply common budget equivalent leftCoherent rightCoherent index).index = index then
          (batch common budget equivalent leftCoherent rightCoherent remaining).map fun after =>
            after.map (prepend common budget equivalent leftCoherent rightCoherent index remaining
              (same ▸ (originalReply common budget equivalent leftCoherent rightCoherent index).result))
          else Program.pure (.error ⟨index,
            (originalReply common budget equivalent leftCoherent rightCoherent index).index, same⟩)).protocol).run
              (originalReply common budget equivalent leftCoherent rightCoherent)).trace = _
      have same : (originalReply common budget equivalent leftCoherent rightCoherent index).index = index := rfl
      rw [dif_pos same, Program.map_execution, Protocol.map_run_trace,
        batch_original_trace common budget equivalent leftCoherent rightCoherent remaining]
      rfl

/-- Assemble joint scheduler results in their exact original common-point order. -/
@[expose] def assemble {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (returned : Batch common budget equivalent leftCoherent rightCoherent (Purelib.Data.List.indices common.readings)) :
    JointReadings common budget := by
  have readings_eq : returned.val.map JointReading.reading = common.readings := by
    rw [returned.property, Purelib.Data.List.Map.map_map]
    change (Purelib.Data.List.indices common.readings).map common.readings.get = common.readings
    exact Purelib.Data.List.indices_get common.readings
  exact ⟨returned.val, readings_eq⟩

/-- The returned joint results are the exact original joint comparison. -/
theorem assemble_eq {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (returned : Batch common budget equivalent leftCoherent rightCoherent (Purelib.Data.List.indices common.readings)) :
    assemble common budget equivalent leftCoherent rightCoherent returned =
      requestJointReadings common budget equivalent leftCoherent rightCoherent := by
  have same : returned.val = (requestJointReadings common budget equivalent leftCoherent rightCoherent).readings := by
    rw [returned.property]
    change (Purelib.Data.List.indices common.readings).map
      (fun index => jointForReading budget equivalent leftCoherent rightCoherent (common.readings.get index)) =
        common.readings.map (jointForReading budget equivalent leftCoherent rightCoherent)
    change (Purelib.Data.List.indices common.readings).map
      ((jointForReading budget equivalent leftCoherent rightCoherent) ∘ common.readings.get) = _
    rw [← Purelib.Data.List.Map.map_map, Purelib.Data.List.indices_get]
  cases returned with
  | mk values property =>
    cases same
    rfl

/-- Observe the original operational source comparison and retain the returned joint scheduler states. -/
@[expose] def computation {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    Program (Query common) (Reply common budget equivalent leftCoherent rightCoherent)
      (Except (Invalid common) (JointReadings common budget)) :=
  (batch common budget equivalent leftCoherent rightCoherent (Purelib.Data.List.indices common.readings)).map
    fun returned =>
    returned.map (assemble common budget equivalent leftCoherent rightCoherent)

/-- Original execution returns the original complete joint scheduler comparison. -/
theorem computation_original {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    ((computation common budget equivalent leftCoherent rightCoherent).protocol.run
      (originalReply common budget equivalent leftCoherent rightCoherent)).value =
        .ok (requestJointReadings common budget equivalent leftCoherent rightCoherent) := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_value, batch_original]
  apply congrArg Except.ok
  exact assemble_eq common budget equivalent leftCoherent rightCoherent _

/-- Exact replay recovers the complete original joint comparison without repeating the joint requests. -/
theorem computation_replay {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    let program := computation common budget equivalent leftCoherent rightCoherent
    let oracle := originalReply common budget equivalent leftCoherent rightCoherent
    program.protocol.replayExact (program.protocol.run oracle).trace =
      .ok (.ok (requestJointReadings common budget equivalent leftCoherent rightCoherent)) := by
  let program := computation common budget equivalent leftCoherent rightCoherent
  let oracle := originalReply common budget equivalent leftCoherent rightCoherent
  change program.protocol.replayExact (program.protocol.run oracle).trace = _
  rw [program.protocol.replayExact_run, computation_original]

/-- Replies outside the actual joint request trace preserve its complete comparison and ordered trace. -/
theorem payload_erasure {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) {Payload : Type} (payload : Payload)
    (outside : Payload → Query common → Reply common budget equivalent leftCoherent rightCoherent) :
    let program := computation common budget equivalent leftCoherent rightCoherent
    let oracle := originalReply common budget equivalent leftCoherent rightCoherent
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  (computation common budget equivalent leftCoherent rightCoherent).protocol.annotation_erasure
    (originalReply common budget equivalent leftCoherent rightCoherent) payload outside

end Purelib.Integration.NumericalFrontier.Common.Operational.Observation

end
