module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Minimum of displayed rational lists

A right fold of the original rational minimum operation starts at one.
Membership supplies upper bounds, while bounds on all entries and the initial
one supply lower bounds. Every computation retains the original finite list.
-/

namespace Purelib.Data.Rat.List.Minimum

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction

/-- Compute the minimum of a displayed rational list with initial bound one.

The right fold retains the original decidable rational minimum and list order.
Its initial value also bounds the result when the supplied list is empty. -/
@[expose] public def positiveMinimum (values : List Fraction.Rational) : Fraction.Rational :=
  values.foldr min 1

/-- The folded rational minimum is bounded by every displayed list member.

A head occurrence uses the left bound for the retained minimum. A tail
occurrence composes its induction bound with the minimum's right bound. -/
public theorem positiveMinimum_le_of_mem
    {values : List Fraction.Rational} {value : Fraction.Rational}
    (member : value ∈ values) : positiveMinimum values ≤ value := by
  induction values with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      change min head (positiveMinimum tail) ≤ value
      cases member with
      | head => exact Order.Basic.min_le_left _ _
      | tail _ tailMember =>
          exact Fraction.Order.Basic.le_trans _ _ _
            (Order.Basic.min_le_right _ _)
            (inductionHypothesis tailMember)

/-- Positive displayed entries give a positive folded rational minimum.

The initial value one is positive. Each cons step supplies positivity for
its head and inherited tail before applying the rational minimum bound. -/
public theorem positiveMinimum_pos (values : List Fraction.Rational)
    (positive : ∀ value ∈ values, 0 < value) :
    0 < positiveMinimum values := by
  induction values with
  | nil => exact (by decide)
  | cons head tail inductionHypothesis =>
      change 0 < min head (positiveMinimum tail)
      exact Order.Basic.lt_min
        (positive head (List.Mem.head tail))
        (inductionHypothesis fun value member =>
          positive value (List.Mem.tail head member))

namespace BoxEventPartition

/-- Compute the minimum of a displayed rational list with initial bound one.

The right fold retains the original decidable rational minimum and list order.
Its initial value also bounds the result when the supplied list is empty. -/
@[expose] public def positiveMinimum (values : List Fraction.Rational) : Fraction.Rational :=
  values.foldr min 1

/-- The folded rational minimum is bounded by every displayed list member.

A head occurrence uses the left bound for the retained minimum. A tail
occurrence composes its induction bound with the minimum's right bound. -/
public theorem positiveMinimum_le_of_mem
    {values : List Fraction.Rational} {value : Fraction.Rational}
    (member : value ∈ values) : positiveMinimum values ≤ value := by
  induction values with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      change min head (positiveMinimum tail) ≤ value
      cases member with
      | head => exact Order.Basic.min_le_left _ _
      | tail _ tailMember =>
          exact Fraction.Order.Basic.le_trans _ _ _
            (Order.Basic.min_le_right _ _)
            (inductionHypothesis tailMember)

/-- Positive displayed entries give a positive folded rational minimum.

The initial value one is positive. Each cons step supplies positivity for
its head and inherited tail before applying the rational minimum bound. -/
public theorem positiveMinimum_pos (values : List Fraction.Rational)
    (positive : ∀ value ∈ values, 0 < value) :
    0 < positiveMinimum values := by
  induction values with
  | nil => exact (by decide)
  | cons head tail inductionHypothesis =>
      change 0 < min head (positiveMinimum tail)
      exact Order.Basic.lt_min
        (positive head (List.Mem.head tail))
        (inductionHypothesis fun value member =>
          positive value (List.Mem.tail head member))

end BoxEventPartition

namespace Maximality

/-- Compute the minimum of a displayed rational list with initial bound one.

The right fold retains the original decidable rational minimum and list order.
Its initial value also bounds the result when the supplied list is empty. -/
@[expose] public def positiveMinimum (values : List Fraction.Rational) : Fraction.Rational :=
  values.foldr min 1

/-- The folded rational minimum is bounded by every displayed list member.

A head occurrence uses the left bound for the retained minimum. A tail
occurrence composes its induction bound with the minimum's right bound. -/
public theorem positiveMinimum_le_of_mem
    {values : List Fraction.Rational} {value : Fraction.Rational}
    (member : value ∈ values) : positiveMinimum values ≤ value := by
  induction values with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      change min head (positiveMinimum tail) ≤ value
      cases member with
      | head => exact Order.Basic.min_le_left _ _
      | tail _ tailMember =>
          exact Fraction.Order.Basic.le_trans _ _ _
            (Order.Basic.min_le_right _ _)
            (inductionHypothesis tailMember)

/-- Positive displayed entries give a positive folded rational minimum.

The initial value one is positive. Each cons step supplies positivity for
its head and inherited tail before applying the rational minimum bound. -/
public theorem positiveMinimum_pos (values : List Fraction.Rational)
    (positive : ∀ value ∈ values, 0 < value) :
    0 < positiveMinimum values := by
  induction values with
  | nil => exact (by decide)
  | cons head tail inductionHypothesis =>
      change 0 < min head (positiveMinimum tail)
      exact Order.Basic.lt_min
        (positive head (List.Mem.head tail))
        (inductionHypothesis fun value member =>
          positive value (List.Mem.tail head member))

end Maximality

namespace RegionOwnership

/-- Compute the minimum of a displayed rational list with initial bound one.

The right fold retains the original decidable rational minimum and list order.
Its initial value also bounds the result when the supplied list is empty. -/
@[expose] public def positiveMinimum (values : List Fraction.Rational) : Fraction.Rational :=
  values.foldr min 1

/-- The folded rational minimum is bounded by every displayed list member.

A head occurrence uses the left bound for the retained minimum. A tail
occurrence composes its induction bound with the minimum's right bound. -/
public theorem positiveMinimum_le_of_mem
    {values : List Fraction.Rational} {value : Fraction.Rational}
    (member : value ∈ values) : positiveMinimum values ≤ value := by
  induction values with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      change min head (positiveMinimum tail) ≤ value
      cases member with
      | head => exact Order.Basic.min_le_left _ _
      | tail _ tailMember =>
          exact Fraction.Order.Basic.le_trans _ _ _
            (Order.Basic.min_le_right _ _)
            (inductionHypothesis tailMember)

/-- Positive displayed entries give a positive folded rational minimum.

The initial value one is positive. Each cons step supplies positivity for
its head and inherited tail before applying the rational minimum bound. -/
public theorem positiveMinimum_pos (values : List Fraction.Rational)
    (positive : ∀ value ∈ values, 0 < value) :
    0 < positiveMinimum values := by
  induction values with
  | nil => exact (by decide)
  | cons head tail inductionHypothesis =>
      change 0 < min head (positiveMinimum tail)
      exact Order.Basic.lt_min
        (positive head (List.Mem.head tail))
        (inductionHypothesis fun value member =>
          positive value (List.Mem.tail head member))

end RegionOwnership

/-- A rational below one and all displayed entries bounds their folded minimum.

The empty list retains the initial bound one. Each cons step combines the
supplied head bound and the recursively retained tail bound. -/
public theorem le_positiveMinimum
    {lower : Fraction.Rational} (values : List Fraction.Rational)
    (lowerOne : lower ≤ 1)
    (lowerValues : ∀ value ∈ values, lower ≤ value) :
    lower ≤ positiveMinimum values := by
  induction values with
  | nil => exact lowerOne
  | cons head tail inductionHypothesis =>
      change lower ≤ min head (positiveMinimum tail)
      exact le_min (lowerValues head (List.Mem.head tail))
        (inductionHypothesis fun value member =>
          lowerValues value (List.Mem.tail head member))

end Purelib.Data.Rat.List.Minimum
