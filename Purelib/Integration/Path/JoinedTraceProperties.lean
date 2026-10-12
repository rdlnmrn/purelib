module
import Purelib.Data.List.Membership
import Purelib.Data.List.OfFn.Basic

public import Purelib.Integration.Path.JoinedTrace

public section

/-! Pointwise geometric properties survive concatenation, including every
retained duplicate junction vertex. -/
namespace Purelib.Integration.Path.JoinedTraceProperties
open Purelib.Integration.Path

open Purelib.Data.List

variable {Vertex : Type} {predicate : Vertex → Prop}

/-- A predicate holds at the original trace's initial vertex and every retained remaining vertex. -/
@[expose] def All (trace : JoinedTrace.VertexTrace Vertex) (predicate : Vertex → Prop) : Prop :=
  predicate trace.first ∧ ∀ vertex ∈ trace.rest, predicate vertex

/-- A pointwise predicate on the original indexed vertices holds throughout their retained vertex trace.

Every retained tail member has its original bounded materialization index. That finite witness supplies the same
original vertex predicate. -/
theorem ofIndexed_all {count : Nat} (vertices : Fin (count + 1) → Vertex)
    (valid : ∀ index, predicate (vertices index)) : JoinedTraceProperties.All (JoinedTrace.VertexTrace.ofIndexed
      vertices) predicate := by
  refine ⟨valid 0, ?_⟩
  intro vertex member
  obtain ⟨index, equal⟩ := OfFn.Basic.mem_ofFn.mp member
  cases equal
  exact valid index.succ

/-- Joining two original traces preserves a predicate established on both inputs.

Membership distinguishes the unchanged left tail from the original right head and tail. Each case uses the corresponding
retained predicate certificate. -/
theorem All.join {first last : JoinedTrace.VertexTrace Vertex} (left : JoinedTraceProperties.All first predicate) (right
  : JoinedTraceProperties.All last predicate) :
    JoinedTraceProperties.All (first.join last) predicate := by
  refine ⟨left.1, ?_⟩
  intro vertex member
  rcases Membership.mem_append.mp member with member | member
  · exact left.2 vertex member
  · rcases Membership.mem_cons.mp member with equal | member
    · exact equal ▸ right.1
    · exact right.2 vertex member

/-- Gluing an original first trace to a retained list preserves a predicate established on every input trace. -/
private theorem glue_all (first : JoinedTrace.VertexTrace Vertex) (rest : List (JoinedTrace.VertexTrace Vertex))
    (start : JoinedTraceProperties.All first predicate) (valid : ∀ trace ∈ rest, JoinedTraceProperties.All trace
      predicate) :
    JoinedTraceProperties.All (first.glue rest) predicate := by
  induction rest generalizing first with
  | nil => exact start
  | cons next rest ih =>
      exact JoinedTraceProperties.All.join start (ih next (valid next (List.mem_cons_self ..))
        (fun trace member => valid trace (List.mem_cons_of_mem _ member)))

/-- Concatenating the original nonempty indexed trace family preserves a common vertex predicate.

The exact finite materialization witnesses each retained trace occurrence. Structural gluing then preserves the
predicate at every original vertex. -/
theorem concatenate_all {count : Nat} (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex)
    (valid : ∀ index, JoinedTraceProperties.All (traces index) predicate) : JoinedTraceProperties.All
      (JoinedTrace.VertexTrace.concatenate traces) predicate := by
  apply JoinedTraceProperties.glue_all _ _ (valid 0)
  intro trace member
  obtain ⟨index, equal⟩ := OfFn.Basic.mem_ofFn.mp member
  cases equal
  exact valid index.succ

/-- A predicate valid throughout the original trace holds at every retained bounded vertex index.

The bounded read has membership in the original head-and-tail list. Its head or tail occurrence supplies the retained
pointwise certificate. -/
theorem All.indexed {trace : JoinedTrace.VertexTrace Vertex} (valid : JoinedTraceProperties.All trace predicate)
    (index : Fin (trace.rest.length + 1)) : predicate (trace.indexed index) := by
  have member : trace.indexed index ∈ trace.first :: trace.rest := List.getElem_mem index.isLt
  rcases Membership.mem_cons.mp member with equal | member
  · exact equal ▸ valid.1
  · exact valid.2 _ member

end Purelib.Integration.Path.JoinedTraceProperties

end
