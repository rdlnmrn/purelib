module

import Init.Data.List.Lemmas
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Recorded query exchanges and executions

An exchange retains one displayed query and its reply. An execution retains its
returned value and complete ordered trace, including repeated query occurrences.
The oracle agreement predicate constrains exactly those recorded replies.
-/

public section

namespace Purelib.Computation.Query.Basic

universe u v w

set_option genInjectivity false in
/-- One query and its recorded reply.

The two fields retain their supplied carrier types and values. Their constructor
certificates compare the query and reply separately without changing the record. -/
structure Exchange (Query : Type u) (Reply : Type v) where
  /-- The query issued at this position. -/ query : Query
  /-- The reply recorded for this query occurrence. -/ reply : Reply

constructive_injectivity Exchange

/-- An ordered finite list of query-and-reply exchanges.

The list retains the original occurrence order and repeated queries. Each entry
keeps its query and reply in the same nominal exchange carrier. -/
abbrev Trace (Query : Type u) (Reply : Type v) := List (Exchange Query Reply)

set_option genInjectivity false in
/-- A returned value together with the finite trace that produced it.

The value and ordered trace are retained directly. Constructor certificates
compare these same fields without dropping any recorded query occurrence. -/
structure Execution (Query : Type u) (Reply : Type v) (Value : Type w) where
  /-- The returned value. -/ value : Value
  /-- The complete ordered trace of recorded exchanges. -/ trace : Trace Query Reply

constructive_injectivity Execution

/-- An oracle agrees with every recorded reply in a finite trace.

Only query occurrences in the trace constrain the oracle. Repeated occurrences
must all receive their recorded replies; unqueried inputs remain unrestricted. -/
@[expose] def Answers {Query : Type u} {Reply : Type v} (oracle : Query → Reply)
    (trace : Trace Query Reply) : Prop :=
  ∀ entry ∈ trace, oracle entry.query = entry.reply

end Purelib.Computation.Query.Basic
