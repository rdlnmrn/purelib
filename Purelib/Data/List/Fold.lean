module
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Structural certificates for finite folds

Concatenation, mapped entries, pointwise scalar steps and the original reversal
accumulator transport the retained fold result. Structural recursion follows
the same list spines and accumulator values without identifying step functions.
-/

namespace Purelib.Data.List.Fold

universe u v w

variable {Alpha : Type u} {Beta : Type v} {Gamma : Type w}

/-- A left fold over concatenation first folds the left list, then the right list.

The original left spine supplies each accumulator update before its unchanged
right suffix is consumed. Structural recursion retains that exact ordering. -/
public theorem foldl_append (function : Beta → Alpha → Beta) :
    ∀ (left right : List Alpha) (initial : Beta),
      (left ++ right).foldl function initial =
        right.foldl function (left.foldl function initial)
  | [], _, _ => rfl
  | value :: values, right, initial =>
      foldl_append function values right (function initial value)

/-- Mapping retained entries before a left fold transports its accumulator step.

The fold consumes the same original finite spine. Each entry is mapped only
at its original step, and the supplied accumulator is passed unchanged into
the remaining tail. -/
public theorem foldl_map
    (mapper : Alpha → Gamma) (function : Beta → Gamma → Beta) :
    ∀ (values : List Alpha) (initial : Beta),
      (values.map mapper).foldl function initial =
        values.foldl (fun state value => function state (mapper value)) initial
  | [], _ => rfl
  | head :: tail, initial =>
      foldl_map mapper function tail (function initial (mapper head))

/-- Pointwise equal accumulator steps produce equal left folds.

For every retained accumulator and list entry, the two step functions must agree. The
theorem compares the finite fold results without equating the step functions. -/
public theorem foldl_congr (left right : Beta → Alpha → Beta)
    (pointwise : ∀ accumulator value,
      left accumulator value = right accumulator value) :
    ∀ (values : List Alpha) (initial : Beta),
      values.foldl left initial = values.foldl right initial
  | [], _ => rfl
  | value :: values, initial => by
      change values.foldl left (left initial value) =
        values.foldl right (right initial value)
      rw [pointwise initial value]
      exact foldl_congr left right pointwise values (right initial value)

/-- A right fold over concatenation first folds the right list, then the left list.

The original right suffix supplies the accumulator for the retained left
spine. Each unchanged left entry then applies its original right-fold step. -/
public theorem foldr_append (function : Alpha → Beta → Beta) :
    ∀ (left right : List Alpha) (initial : Beta),
      (left ++ right).foldr function initial =
        left.foldr function (right.foldr function initial)
  | [], _, _ => rfl
  | value :: values, right, initial => by
      change function value ((values ++ right).foldr function initial) =
        function value (values.foldr function (right.foldr function initial))
      rw [foldr_append function values right initial]

/-- Folding a retained reversal suffix first folds the reversed original list.

The original reversal accumulator retains the suffix unchanged. Structural
recursion transfers each original head to that accumulator, matching the next
right-fold step before the same suffix is consumed. -/
private theorem foldl_reverseAux {Alpha : Type u} {Beta : Type v}
    (function : Beta → Alpha → Beta) :
    ∀ (values suffix : List Alpha) (initial : Beta),
      (List.reverseAux values suffix).foldl function initial =
        suffix.foldl function (values.foldr (fun value state => function state value) initial)
  | [], _, _ => rfl
  | head :: tail, suffix, initial =>
      foldl_reverseAux function tail (head :: suffix) initial

/-- A left fold over the reversed list equals the corresponding right fold over the
original.

The right-fold step presents the list value before the accumulator, exchanging their
positions in the supplied left-fold function. -/
public theorem foldl_reverse {Alpha : Type u} {Beta : Type v} (function : Beta → Alpha → Beta)
    (initial : Beta) : forall values : List Alpha,
      values.reverse.foldl function initial = values.foldr (fun value state => function state value) initial :=
  fun values => foldl_reverseAux function values [] initial

/-- Summing a retained concatenation adds its two original finite sums.

The original right fold uses the supplied addition and zero operations.
Explicit left-identity and associativity certificates transport each
retained left entry without introducing any extra operation dictionary. -/
public theorem sum_append [Add Alpha] [Zero Alpha]
    (zeroAdd : ∀ value : Alpha, 0 + value = value)
    (addAssoc : ∀ first second third : Alpha,
      (first + second) + third = first + (second + third)) :
    ∀ left right : List Alpha, (left ++ right).sum = left.sum + right.sum
  | [], right => (zeroAdd right.sum).symm
  | head :: tail, right => by
      change head + (tail ++ right).sum = (head + tail.sum) + right.sum
      rw [sum_append zeroAdd addAssoc tail right]
      exact (addAssoc head tail.sum right.sum).symm

/-- Multiplying a concatenation multiplies its two ordered finite products.

The supplied multiplication and unit are the original fold operations.
Their explicit left identity and associativity certificates transport each
retained left entry while leaving the right product unchanged. -/
public theorem prod_append [Mul Alpha] [One Alpha]
    (oneMul : ∀ value : Alpha, 1 * value = value)
    (mulAssoc : ∀ first second third : Alpha,
      (first * second) * third = first * (second * third)) :
    ∀ left right : List Alpha, (left ++ right).prod = left.prod * right.prod
  | [], right => (oneMul right.prod).symm
  | head :: tail, right => by
      change head * (tail ++ right).prod = (head * tail.prod) * right.prod
      rw [prod_append oneMul mulAssoc tail right]
      exact (mulAssoc head tail.prod right.prod).symm

end Purelib.Data.List.Fold

namespace Purelib.Data.List.Fold

open Purelib.Data.List

/-- Summing a finite list of zero natural values gives zero. -/
public theorem foldr_add_map_zero {Alpha : Type*} (values : List Alpha) :
    (values.map fun _ => 0).foldr Nat.add 0 = 0 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.foldr_cons, inductionHypothesis]

/-- A finite natural sum distributes over the pointwise sum of two value functions.

The same retained list supplies both scalar readings. Structural induction combines
each pair of head values while preserving both original tail sums. -/
public theorem foldr_add_map_pointwise_add {Alpha : Type*}
    (values : List Alpha) (left right : Alpha → Nat) :
    (values.map fun value => left value + right value).foldr Nat.add 0 =
      (values.map left).foldr Nat.add 0 +
        (values.map right).foldr Nat.add 0 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.map_cons, List.map_cons,
        List.foldr_cons, List.foldr_cons, List.foldr_cons,
        inductionHypothesis]
      calc
        (left head + right head) +
            ((tail.map left).foldr Nat.add 0 +
              (tail.map right).foldr Nat.add 0) =
          left head + (right head +
            ((tail.map left).foldr Nat.add 0 +
              (tail.map right).foldr Nat.add 0)) :=
            Nat.add_assoc _ _ _
        _ = left head + ((right head +
              (tail.map left).foldr Nat.add 0) +
            (tail.map right).foldr Nat.add 0) :=
          congrArg (Nat.add (left head))
            (Nat.add_assoc _ _ _).symm
        _ = left head + (((tail.map left).foldr Nat.add 0 +
              right head) +
            (tail.map right).foldr Nat.add 0) := by
          rw [Nat.add_comm (right head) ((tail.map left).foldr Nat.add 0)]
        _ = (left head + (tail.map left).foldr Nat.add 0) +
            (right head + (tail.map right).foldr Nat.add 0) := by
          rw [Nat.add_assoc (left head) ((tail.map left).foldr Nat.add 0)
            (right head + (tail.map right).foldr Nat.add 0),
            Nat.add_assoc ((tail.map left).foldr Nat.add 0) (right head)
              ((tail.map right).foldr Nat.add 0)]

end Purelib.Data.List.Fold
