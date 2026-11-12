module

import Purelib.Data.List.Append
import Purelib.Data.List.Reverse

/-!
# Readback of the original finite list split

The original one-pass split retains its input when the count exhausts the
list. Its accumulator invariant identifies both actual output lists with
the requested prefix and remaining suffix.
-/

namespace Purelib.Data.List.Split

open Purelib.Data.List

/-- The original split accumulator retains the same completed prefix and suffix.

The reversed accumulator followed by the remaining spine is the original
input. Structural recursion preserves that identity, including the original
input returned when the remaining spine is exhausted. -/
private theorem go_eq {Alpha : Type u} (original : List Alpha) :
    (remaining : List Alpha) → (count : Nat) → (accumulated : List Alpha) →
    accumulated.reverse ++ remaining = original →
      List.splitAt.go original remaining count accumulated =
        (accumulated.reverse ++ remaining.take count, remaining.drop count)
  | [], 0, _, retained => congrArg (fun entries => (entries, [])) retained.symm
  | [], _ + 1, _, retained => congrArg (fun entries => (entries, [])) retained.symm
  | head :: tail, 0, accumulated, _ =>
      congrArg (fun entries => (entries, head :: tail))
        (Append.append_nil accumulated.reverse).symm
  | head :: tail, count + 1, accumulated, retained => by
      have advanced : (head :: accumulated).reverse ++ tail = original := by
        rewrite [Reverse.reverse_cons, Append.append_assoc]
        exact retained
      have scanned := go_eq original tail count (head :: accumulated) advanced
      apply scanned.trans
      apply congrArg (fun entries => (entries, tail.drop count))
      rewrite [Reverse.reverse_cons, Append.append_assoc]
      exact Eq.refl _

/-- Splitting at a count returns the original requested prefix and remaining suffix. -/
public theorem at_eq {Alpha : Type u} {count : Nat} {entries : List Alpha} :
    entries.splitAt count = (entries.take count, entries.drop count) :=
  go_eq entries entries count [] rfl

/-- Concatenating the original split's two outputs recovers every input occurrence. -/
public theorem append_parts {Alpha : Type u} (entries : List Alpha) (count : Nat) :
    (entries.splitAt count).1 ++ (entries.splitAt count).2 = entries :=
  (congrArg (fun pair : List Alpha × List Alpha => pair.1 ++ pair.2)
    (at_eq (entries := entries) (count := count))).trans (List.take_append_drop count entries)

end Purelib.Data.List.Split
