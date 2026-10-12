module

import Init.Data.List.Lemmas
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Concrete finite query replay discrepancies

Replay errors retain the exact missing query, unequal expected and actual
queries, or first trailing query. The mismatch constructor includes its actual
inequality witness, and decidable equality keeps the supplied query dictionary.
-/

public section

namespace Purelib.Computation.Query.Replay

universe u

-- The original datatype and derived equality helpers are executable public
-- bodies needed by clients reducing finite replay decisions.
@[expose] public section

set_option genInjectivity false in
/-- A concrete discrepancy between a replay and its supplied finite trace.

An error identifies the missing query, unequal expected and actual queries, or
first trailing query. Mismatch errors retain the supplied inequality proof. -/
inductive ReplayError (Query : Type u) where
  /-- Replay requires the displayed query but the trace has ended. -/ | missing (expected : Query)
  /-- The next recorded query differs from the expected query. -/ | mismatch (expected actual : Query) (different :
    actual ≠ expected)
  /-- A query remains after the replayed computation has completed. -/ | trailing (actual : Query)
deriving DecidableEq

constructive_injectivity ReplayError

end

end Purelib.Computation.Query.Replay
