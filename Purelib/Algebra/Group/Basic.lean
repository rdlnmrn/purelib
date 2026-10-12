module

public import Mathlib.Algebra.Group.Defs

namespace Purelib.Algebra.Group

/-- Build an additive group from associativity, a left identity and left inverses.

The right inverse and right identity follow by scalar reassociation.
Natural and integer scalar multiplication retain the standard recursive
operations of the original minimal-axiom constructor. Subtraction retains
the class default, addition followed by negation. -/
@[expose, reducible] public def addGroupOfLeftAxioms {G : Type*}
    [Add G] [Neg G] [Zero G]
    (assoc : ∀ first second third : G,
      first + second + third = first + (second + third))
    (zeroAdd : ∀ value : G, 0 + value = value)
    (negAddCancel : ∀ value : G, -value + value = 0) : AddGroup G := by
  have addNegCancel : ∀ value : G, value + -value = 0 := by
    intro value
    calc
      value + -value = 0 + (value + -value) := (zeroAdd _).symm
      _ = (-(value + -value) + (value + -value)) + (value + -value) :=
        congrArg (· + (value + -value)) (negAddCancel _).symm
      _ = -(value + -value) + (value + ((-value + value) + -value)) := by
        rw [assoc (-(value + -value)) (value + -value) (value + -value),
          assoc value (-value) (value + -value), ← assoc (-value) value (-value)]
      _ = 0 := by rw [negAddCancel value, zeroAdd (-value), negAddCancel]
  have addZero : ∀ value : G, value + 0 = value := by
    intro value
    rw [← negAddCancel value, ← assoc, addNegCancel value, zeroAdd]
  exact {
    add_assoc := assoc
    zero_add := zeroAdd
    add_zero := addZero
    neg_add_cancel := negAddCancel
    nsmul := @nsmulRecAuto G { toAdd := inferInstance, add_assoc := assoc } inferInstance
    zsmul := zsmulRec nsmulRec }

/-- Equality follows from zero subtraction in the retained additive group.

Adding the same right operand restores the original left operand through the
supplied subtraction, associativity and inverse fields, preserving both
original operands. -/
public theorem eq_of_sub_eq_zero {G : Type*} [AddGroup G] {left right : G}
    (difference : left - right = 0) : left = right := by
  have restored : (left - right) + right = left :=
    calc
      (left - right) + right = (left + -right) + right :=
        congrArg (fun value => value + right) (SubNegMonoid.sub_eq_add_neg left right)
      _ = left + (-right + right) := AddSemigroup.add_assoc _ _ _
      _ = left + 0 := congrArg (fun value => left + value) (AddGroup.neg_add_cancel right)
      _ = left := AddZeroClass.add_zero left
  exact restored.symm.trans
    ((congrArg (fun value => value + right) difference).trans
      (AddZeroClass.zero_add right))

/-- Subtracting a retained leading summand leaves the original second summand.

Commutativity moves the retained summand beside its inverse; associativity and
its original inverse certificate then preserve the remaining operand. -/
public theorem add_sub_cancel_left {G : Type*} [AddCommGroup G] (first second : G) :
    first + second - first = second := by
  have inverse : first + -first = 0 :=
    (AddCommMagma.add_comm first (-first)).trans (AddGroup.neg_add_cancel first)
  rewrite [SubNegMonoid.sub_eq_add_neg, AddCommMagma.add_comm first second,
    AddSemigroup.add_assoc, inverse, AddZeroClass.add_zero]
  rfl

/-- Subtracting two sums cancels their common retained right summand.

Both differences recover their original first sum on addition of the subtracted
sum. Translation by its inverse preserves the equality without changing any operand. -/
public theorem add_sub_add_right_eq_sub {G : Type*} [AddCommGroup G]
    (first second common : G) : (first + common) - (second + common) = first - second := by
  let factor := second + common
  have inverse : factor + -factor = 0 :=
    (AddCommMagma.add_comm factor (-factor)).trans (AddGroup.neg_add_cancel factor)
  have leftRestored : ((first + common) - factor) + factor = first + common := by
    rewrite [SubNegMonoid.sub_eq_add_neg, AddSemigroup.add_assoc,
      AddGroup.neg_add_cancel, AddZeroClass.add_zero]
    rfl
  have rightRestored : (first - second) + factor = first + common := by
    change (first - second) + (second + common) = first + common
    rewrite [← AddSemigroup.add_assoc, SubNegMonoid.sub_eq_add_neg,
      AddSemigroup.add_assoc first (-second) second, AddGroup.neg_add_cancel,
      AddZeroClass.add_zero]
    rfl
  have transported := congrArg (fun value => value + -factor) (leftRestored.trans rightRestored.symm)
  rewrite [AddSemigroup.add_assoc ((first + common) - factor) factor (-factor),
    AddSemigroup.add_assoc (first - second) factor (-factor), inverse,
    AddZeroClass.add_zero, AddZeroClass.add_zero] at transported
  exact transported

/-- Subtracting two sums cancels their common retained left summand.

Commutativity moves that summand to the right of both original operands, where
the retained right-summand cancellation certificate applies. -/
public theorem add_sub_add_left_eq_sub {G : Type*} [AddCommGroup G]
    (common first second : G) : (common + first) - (common + second) = first - second := by
  rewrite [AddCommMagma.add_comm common first, AddCommMagma.add_comm common second]
  exact add_sub_add_right_eq_sub first second common

/-- Negation preserves nonzeroness in the retained additive group.

The original left-inverse certificate recovers the nonzero scalar if its
negation is zero; no logical equivalence or derived subtraction adapter is needed. -/
public theorem neg_ne_zero {G : Type*} [AddGroup G] {value : G}
    (nonzero : value ≠ 0) : -value ≠ 0 := by
  intro zero
  apply nonzero
  exact (AddZeroClass.zero_add value).symm.trans
    ((congrArg (fun scalar : G => scalar + value) zero.symm).trans
      (AddGroup.neg_add_cancel value))

/-- A zero negation forces the original additive-group scalar to vanish. -/
public theorem eq_zero_of_neg_eq_zero {G : Type*} [AddGroup G] {value : G}
    (vanishes : -value = 0) : value = 0 :=
  (AddZeroClass.zero_add value).symm.trans
    ((congrArg (fun scalar : G => scalar + value) vanishes.symm).trans
      (AddGroup.neg_add_cancel value))

/-- Adding one retained left scalar preserves equality of the two right operands. -/
public theorem add_left_cancel {G : Type*} [AddGroup G]
    {common left right : G} (equal : common + left = common + right) : left = right := by
  have canceled := congrArg (fun value : G => -common + value) equal
  rw [← AddSemigroup.add_assoc, ← AddSemigroup.add_assoc,
    AddGroup.neg_add_cancel, AddZeroClass.zero_add, AddZeroClass.zero_add] at canceled
  exact canceled

end Purelib.Algebra.Group
