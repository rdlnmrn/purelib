module

-- The exposed search retains the original entry-membership certificate.
public import Purelib.Data.List.Membership

import Purelib.Data.Vector.Boolean.Basic
public import Purelib.LinearAlgebra.Span.Boolean.Basic
import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Finite Boolean spans with retained word witnesses

This module incrementally spans one supplied finite list of fixed-length
Boolean vectors under XOR.  It never forms a function space or an ambient
infinite vector space.  Every distinct image vector retains a Boolean word
witness; the result also caches closure, completeness, duplicate-freeness,
rank, and the exact power-of-two length formula.
-/

namespace Purelib.LinearAlgebra.Span.Boolean

open Purelib
open Purelib.LinearAlgebra.Span

set_option genInjectivity false in
/-- A finite search outcome retaining a matching span entry or a proof of absence.

The result is indexed by the exact target vector and original entry list. -/
inductive Search {width : Nat} {generators : List (Data.Vector.Boolean width)}
    (target : Data.Vector.Boolean width) : List (Boolean.Basic.Entry generators) → Type
  /-- Retain a matching original entry, its list membership and its equality to the target. -/ | found (entry :
    Boolean.Basic.Entry generators) (member : entry ∈ entries)
      (vector_eq : entry.vector = target) : Search target entries
  /-- Certify that every original entry differs from the target vector. -/ | absent (notFound : ∀ entry ∈ entries,
    entry.vector ≠ target) :
      Search target entries

constructive_injectivity Search

namespace Search.found

end Search.found
namespace Search

/-- Scan the retained span entries for the target Boolean vector.

Success retains its original list membership and vector equality; exhaustion proves that every original entry differs.
-/
@[expose] def search {width : Nat} {generators : List (Data.Vector.Boolean width)}
    (target : Data.Vector.Boolean width) :
    (entries : List (Boolean.Basic.Entry generators)) → Search target entries
  | [] => absent fun _entry impossible => by nomatch impossible
  | head :: tail =>
      if bitsEqual : head.vector.bits = target.bits then
        found head List.mem_cons_self (Data.Vector.Boolean.ext bitsEqual)
      else
        match Purelib.LinearAlgebra.Span.Boolean.Search.search target tail with
        | found entry member equal =>
            found entry (List.mem_cons_of_mem head member) equal
        | absent notFound => absent fun entry member => by
            rcases Data.List.Membership.mem_cons.mp member with headEqual | tailMember
            · subst entry
              intro same
              exact bitsEqual (congrArg Data.Vector.Boolean.bits same)
            · exact notFound entry tailMember

end Search
end Purelib.LinearAlgebra.Span.Boolean
