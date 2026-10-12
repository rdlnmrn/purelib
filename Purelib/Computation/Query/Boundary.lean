module

import Purelib.Computation.Query.Basic
import Purelib.Data.List.Membership
public import Purelib.Computation.Query.Computation
import Mathlib.Tactic.Linter.Lint

/-!
# Finite query boundaries and annotation erasure

The finite trace retains its first reply for every displayed query. Replies at
repeated occurrences agree when the trace records one oracle's answers. Overlay
uses those retained replies and calls an arbitrary fallback only outside the
trace. The computation's agreement law preserves its complete execution under
that overlay, including a fallback indexed by an arbitrary payload.
-/

public section

namespace Purelib.Computation.Query

-- Retain the established Boundary.Computation theorem namespace.

open Purelib.Computation.Query
open Purelib.Data.List

universe u v w x

namespace Boundary.Trace

variable {Query : Type u} {Reply : Type v}

/-- Find the first recorded reply to a query.

The search scans the finite trace in order using decidable query equality. Later occurrences do not override the first
reply. -/
@[expose] def lookup [DecidableEq Query] : Basic.Trace Query Reply → Query → Option Reply
  | [], _ => none
  | entry :: rest, query =>
      if query = entry.query then some entry.reply else lookup rest query

/-- Use the trace's first reply when present, and the supplied fallback otherwise.

The finite lookup retains the earliest matching exchange. Only an absent query invokes the supplied fallback at that
same query. -/
@[expose] def overlay [DecidableEq Query] (trace : Basic.Trace Query Reply) (fallback : Query → Reply) (query : Query) :
  Reply :=
  match lookup trace query with
  | some reply => reply
  | none => fallback query

/-- Lookup recovers the reply of any entry in an oracle-consistent trace.

Although lookup chooses the first occurrence, the agreement hypothesis forces every occurrence of that query to have the
same reply. -/
theorem lookup_of_answers [DecidableEq Query] (oracle : Query → Reply) (trace : Basic.Trace Query Reply)
    (answers : Basic.Answers oracle trace) (entry : Basic.Exchange Query Reply) (member : entry ∈ trace) :
    lookup trace entry.query = some entry.reply := by
  induction trace with
  | nil => nomatch member
  | cons head rest induction =>
      unfold lookup
      by_cases same : entry.query = head.query
      · rw [if_pos same]
        apply congrArg some
        exact (answers head (List.Mem.head rest)).symm.trans
          ((congrArg oracle same.symm).trans (answers entry member))
      · rw [if_neg same]
        have tailMember : entry ∈ rest := by
          rcases Membership.mem_cons.mp member with equal | tail
          · exact (same (congrArg Basic.Exchange.query equal)).elim
          · exact tail
        exact induction (fun item inside => answers item (List.Mem.tail head inside)) tailMember

/-- Overlaying an oracle-consistent trace preserves all its recorded replies.

Each occurrence has the reply supplied by the same oracle, including repeated queries. The first-match lookup therefore
supplies that reply independently of the fallback. -/
theorem overlay_answers [DecidableEq Query] (oracle fallback : Query → Reply) (trace : Basic.Trace Query Reply)
    (answers : Basic.Answers oracle trace) : Basic.Answers (overlay trace fallback) trace := by
  intro entry member
  unfold overlay
  rw [lookup_of_answers oracle trace answers entry member]

end Boundary.Trace

namespace Protocol

variable {Query : Type u} {Reply : Type v} {Value : Type w}

open _root_.Purelib.Computation.Query renaming Protocol -> Protocol
/-- Replacing unqueried oracle values preserves the entire recorded execution.

Overlaying the first run's finite trace with any fallback supplies the same observed replies; the computation's
agreement law then determines both value and trace. -/
theorem run_overlay [DecidableEq Query] (computation : Protocol Query Reply Value)
    (oracle fallback : Query → Reply) :
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace fallback) = computation.run oracle :=
  computation.run_of_answers oracle _
    (Boundary.Trace.overlay_answers oracle fallback _ (computation.answers_run oracle))

/-- A payload-dependent fallback has no effect on replaying a recorded query boundary.

The payload and its type are arbitrary. Overlay supplies the retained replies at every query reached by the computation,
preserving its whole execution. -/
theorem annotation_erasure [DecidableEq Query] {Payload : Type x}
    (computation : Protocol Query Reply Value) (oracle : Query → Reply)
    (payload : Payload) (outside : Payload → Query → Reply) :
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) = computation.run oracle
      :=
  run_overlay computation oracle (outside payload)

end Protocol

end Purelib.Computation.Query
