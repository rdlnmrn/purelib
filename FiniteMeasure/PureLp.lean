import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.NaturalLp
import FiniteMeasure.EssentialMaximum
import FiniteMeasure.Stochastic

/-!
# Lp quantities of one-point finite distributions

The one-point distribution is the base constructor for finite bind and
sampling.  All powered and essential-maximum quantities reduce exactly to
the displayed rational value at that point.
-/

namespace FiniteMeasure

namespace Distribution

@[simp] theorem pure_poweredLp {α : Type} (item : α)
    (exponent : Nat) (value : α → Coordinate) :
    (Distribution.pure item).poweredLp exponent value =
      rationalSeparation (value item) 0 ^ exponent := by
  change (Distribution.pure item).expectation (fun point =>
    rationalSeparation (value point) 0 ^ exponent) = _
  rw [Distribution.pure_expectation]

@[simp] theorem pure_poweredLpDistance {α : Type} (item : α)
    (exponent : Nat) (left right : α → Coordinate) :
    (Distribution.pure item).poweredLpDistance exponent left right =
      rationalSeparation (left item) (right item) ^ exponent := by
  change (Distribution.pure item).expectation (fun point =>
    rationalSeparation (left point) (right point) ^ exponent) = _
  rw [Distribution.pure_expectation]

@[simp] theorem pure_poweredL1 {α : Type} (item : α)
    (value : α → Coordinate) :
    (Distribution.pure item).poweredL1 value =
      rationalSeparation (value item) 0 := by
  rw [← (Distribution.pure item).poweredLp_one value,
    Distribution.pure_poweredLp, pow_one]

@[simp] theorem pure_l1Distance {α : Type} (item : α)
    (left right : α → Coordinate) :
    (Distribution.pure item).l1Distance left right =
      rationalSeparation (left item) (right item) := by
  rw [← (Distribution.pure item).poweredLpDistance_one left right,
    Distribution.pure_poweredLpDistance, pow_one]

@[simp] theorem pure_poweredL2 {α : Type} (item : α)
    (value : α → Coordinate) :
    (Distribution.pure item).poweredL2 value = value item ^ 2 := by
  rw [← (Distribution.pure item).poweredLp_two value,
    Distribution.pure_poweredLp, rationalSeparation_sq]
  ring1

@[simp] theorem pure_poweredL2Distance {α : Type} (item : α)
    (left right : α → Coordinate) :
    (Distribution.pure item).poweredL2Distance left right =
      (left item - right item) ^ 2 := by
  rw [← (Distribution.pure item).poweredLpDistance_two left right,
    Distribution.pure_poweredLpDistance, rationalSeparation_sq]

@[simp] theorem pure_essentialMaximumMagnitude {α : Type} (item : α)
    (value : α → Coordinate) :
    (Distribution.pure item).essentialMaximumMagnitude value =
      rationalSeparation (value item) 0 := by
  unfold Distribution.essentialMaximumMagnitude
    FiniteContent.essentialMaximumMagnitude Distribution.toFiniteContent
    Distribution.pure
  have oneNonzero : (1 : Coordinate) ≠ 0 := by decide
  simp only [essentialMaximumMagnitudeOn, oneNonzero, ↓reduceIte]
  exact max_eq_left (rationalSeparation_nonneg _ _)

@[simp] theorem pure_essentialMaximumDistance {α : Type} (item : α)
    (left right : α → Coordinate) :
    (Distribution.pure item).essentialMaximumDistance left right =
      rationalSeparation (left item) (right item) := by
  change (Distribution.pure item).essentialMaximumMagnitude
    (fun point => left point - right point) = _
  rw [Distribution.pure_essentialMaximumMagnitude]
  exact (rationalSeparation_eq_sub_zero (left item) (right item)).symm

end Distribution

end FiniteMeasure
