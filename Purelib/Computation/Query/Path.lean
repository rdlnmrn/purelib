module

import Purelib.Data.List.Append

/-!
# Questions on retained finite request paths

A question records the original chronological requests and the next request.
Order and repetitions belong to its numerical identity.
-/

public section

namespace Purelib.Computation.Query.Path

universe u

set_option genInjectivity false in
/-- One request following its exact retained chronological request path. -/
structure Question (Request : Type u) where
  /-- The preceding requests in their original order, including repetitions. -/ previous : List Request
  /-- The next request on this same path. -/ request : Request

namespace Question

/-- Construct the first question on an empty request path. -/
@[expose] def initial {Request : Type u} (request : Request) : Question Request := ⟨[], request⟩

/-- Read the complete path after this question has been consumed. -/
@[expose] def path {Request : Type u} (question : Question Request) : List Request :=
  question.previous ++ [question.request]

/-- Extend the exact earlier question's path by the supplied next request. -/
@[expose] def next {Request : Type u} (question : Question Request) (request : Request) : Question Request :=
  ⟨question.path, request⟩

/-- Compare the preceding path first and then its next request. -/
instance {Request : Type u} [DecidableEq Request] : DecidableEq (Question Request) := fun left right =>
  if previousEq : left.previous = right.previous then
    if requestEq : left.request = right.request then
      .isTrue (by cases left; cases right; cases previousEq; cases requestEq; rfl)
    else .isFalse (fun same => requestEq (congrArg Question.request same))
  else .isFalse (fun same => previousEq (congrArg Question.previous same))

end Question

end Purelib.Computation.Query.Path

end
