module

meta import Purelib.Elab.Deriving.Repr
public import Purelib.Data.List.BinaryPrefix.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.List.BinaryPrefix

open Purelib.Data.List.BinaryPrefix renaming CCLMeasureWord -> Word

section
@[expose] public section

/-!
# A finite Boolean algebra of raw-prefix decisions

`RawEvent` is a finite binary decision tree.  Its valuation is computed by
finite recursion, assigning half of the current symbolic weight to each raw
bit branch.  It is deliberately not a set of completed bit streams and does
not assert that the CCL decoder preserves this symbolic valuation.
-/

namespace Purelib.Data.List.BinaryPrefix

set_option genInjectivity false in
/-- A finite binary decision tree for accepting or rejecting raw prefix continuations.

Empty and full terminate with rejection and acceptance; a branch retains the
false-bit and true-bit subtrees. Equality is executable by finite constructor
comparison. -/
inductive RawEvent where
  /-- Reject every continuation at this leaf. -/ | empty
  /-- Accept every continuation at this leaf. -/ | full
  /-- Select the retained false-bit or true-bit subtree according to the next bit. -/ | branch (falseChild trueChild :
    RawEvent)
deriving DecidableEq

constructive_injectivity RawEvent

derive_exposed_repr RawEvent

namespace RawEvent

/-- Complement a finite binary decision tree.

Exchange the empty and full leaves and recursively complement both children of each
retained branch. -/
def complement : RawEvent → RawEvent
  | .empty => .full
  | .full => .empty
  | .branch falseChild trueChild =>
      .branch falseChild.complement trueChild.complement

/-- Intersect two finite binary decision trees by aligning their displayed branches.

An empty input rejects immediately, and a full input leaves the other event
unchanged. When both inputs branch, intersect corresponding children recursively. -/
def inter : RawEvent → RawEvent → RawEvent
  | .empty, _ => .empty
  | .full, right => right
  | .branch _ _, .empty => .empty
  | .branch falseChild trueChild, .full =>
      .branch falseChild trueChild
  | .branch falseChild trueChild, .branch falseRight trueRight =>
      .branch (inter falseChild falseRight)
        (inter trueChild trueRight)

/-- Unite two finite binary decision trees by aligning their displayed branches.

A full input accepts immediately, and an empty input leaves the other event
unchanged. When both inputs branch, unite corresponding children recursively. -/
def union : RawEvent → RawEvent → RawEvent
  | .empty, right => right
  | .full, _ => .full
  | .branch falseChild trueChild, .empty =>
      .branch falseChild trueChild
  | .branch _ _, .full => .full
  | .branch falseChild trueChild, .branch falseRight trueRight =>
      .branch (union falseChild falseRight)
        (union trueChild trueRight)

/-- Complementing a finite binary decision tree twice recovers the exact original tree. -/
theorem complement_complement : ∀ event : RawEvent,
    event.complement.complement = event
  | .empty => rfl
  | .full => rfl
  | .branch falseChild trueChild => by
      simp only [complement]
      rw [complement_complement falseChild,
        complement_complement trueChild]

/-- Build the finite decision tree that accepts after matching a displayed Boolean
prefix.

Follow each retained bit and reject its sibling branch. After the last bit, the full
leaf accepts every continuation. -/
def ofPrefix : Word → RawEvent
  | [] => .full
  | false :: remaining => .branch (ofPrefix remaining) .empty
  | true :: remaining => .branch .empty (ofPrefix remaining)
end RawEvent

end Purelib.Data.List.BinaryPrefix

end
