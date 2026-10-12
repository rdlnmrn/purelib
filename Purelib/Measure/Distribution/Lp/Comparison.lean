module
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Content
public import Purelib.Measure.Distribution.EssentialBound.Basic
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Content.Lp.Comparison
import Purelib.Measure.Distribution.Convergence.Bounded
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Mathlib.Order.Basic

section
/-!
# Root-free finite Lp comparison

An explicit essential magnitude ceiling converts a higher natural-powered
integral into a lower one with the expected ceiling factor.  The formulation
uses only rational powers and finite sums, avoiding roots and completed normed
spaces.
-/

public section

namespace Purelib.Measure

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- The square of the magnitude expectation is bounded by the squared-observable expectation. -/
theorem poweredL1_sq_le_poweredL2 {α : Type}
    (distribution : Measure.Distribution α) (value : α → Fraction.Rational) :
    distribution.poweredL1 value ^ 2 ≤
      distribution.poweredL2 value := by
  have bound := distribution.toContent
    |>.poweredL1_sq_le_total_mul_poweredL2 value
  rw [distribution.toContent_total, one_mul] at bound
  exact bound

/-- Squared integrated distance is bounded by squared-distance expectation. -/
theorem l1Distance_sq_le_poweredL2Distance {α : Type}
    (distribution : Measure.Distribution α) (left right : α → Fraction.Rational) :
    distribution.l1Distance left right ^ 2 ≤
      distribution.poweredL2Distance left right := by
  have bound := distribution.toContent
    |>.l1Distance_sq_le_total_mul_poweredL2Distance left right
  rw [distribution.toContent_total, one_mul] at bound
  exact bound

/-- Squared separation of two expectations is bounded by the squared-distance expectation of their observables. -/
theorem expectation_separation_sq_le_poweredL2Distance {α : Type}
    (distribution : Measure.Distribution α) (left right : α → Fraction.Rational) :
    Distance.rationalSeparation (distribution.expectation left)
        (distribution.expectation right) ^ 2 ≤
      distribution.poweredL2Distance left right := by
  have separationLe := distribution.expectation_separation_le_l1Distance
    left right
  have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
    (Distance.rationalSeparation_nonneg
      (distribution.expectation left) (distribution.expectation right))
    separationLe 2
  exact powered.trans
    (distribution.l1Distance_sq_le_poweredL2Distance left right)

/-- A squared-distance expectation below a positive tolerance squared makes the expectation separation smaller than that
tolerance. -/
theorem expectation_separation_lt_of_poweredL2Distance_lt_sq {α : Type}
    (distribution : Measure.Distribution α) (left right : α → Fraction.Rational)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (small : distribution.poweredL2Distance left right < epsilon ^ 2) :
    Distance.rationalSeparation (distribution.expectation left)
        (distribution.expectation right) < epsilon := by
  have squares :=
    (distribution.expectation_separation_sq_le_poweredL2Distance
      left right).trans_lt small
  exact Bounds.Square.lt_of_sq_lt_sq_of_nonneg positive.le squares

/-- An essential magnitude ceiling bounds an added exponent by the corresponding ceiling power times the original
powered expectation. -/
theorem poweredLp_add_le_of_essentialBound {α : Type}
    (distribution : Measure.Distribution α) (exponent extra : Nat)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : distribution.EssentiallyBoundedBy value ceiling) :
    distribution.poweredLp (exponent + extra) value ≤
      ceiling ^ extra * distribution.poweredLp exponent value :=
  distribution.toContent.poweredLp_add_le_of_essentialBound
    exponent extra value ceiling bounded

/-- Adding a natural exponent increases the powered expectation by at most the matching power of essential maximum
magnitude. -/
theorem poweredLp_add_le_essentialMaximum {α : Type}
    (distribution : Measure.Distribution α) (exponent extra : Nat)
    (value : α → Fraction.Rational) :
    distribution.poweredLp (exponent + extra) value ≤
      distribution.essentialMaximumMagnitude value ^ extra *
        distribution.poweredLp exponent value :=
  distribution.toContent.poweredLp_add_le_essentialMaximum
    exponent extra value

/-- Squared-observable expectation is bounded by essential maximum magnitude times magnitude expectation. -/
theorem poweredL2_le_essentialMaximum_mul_poweredL1 {α : Type}
    (distribution : Measure.Distribution α) (value : α → Fraction.Rational) :
    distribution.poweredL2 value ≤
      distribution.essentialMaximumMagnitude value *
        distribution.poweredL1 value :=
  distribution.toContent
    |>.poweredL2_le_essentialMaximum_mul_poweredL1 value

/-- An essential separation ceiling bounds a higher powered distance expectation by the original powered expectation
times the extra ceiling power. -/
theorem poweredLpDistance_add_le_of_essentialBound {α : Type}
    (distribution : Measure.Distribution α) (exponent extra : Nat)
    (left right : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      atom.weight = 0 ∨
        Distance.rationalSeparation (left atom.item) (right atom.item) ≤ ceiling) :
    distribution.poweredLpDistance (exponent + extra) left right ≤
      ceiling ^ extra *
        distribution.poweredLpDistance exponent left right :=
  distribution.toContent
    |>.poweredLpDistance_add_le_of_essentialBound exponent extra
      left right ceiling bounded

/-- Squared-distance expectation is bounded by the difference's essential maximum magnitude times integrated distance.
-/
theorem poweredL2Distance_le_essentialMaximumDifference_mul_l1Distance
    {α : Type} (distribution : Measure.Distribution α)
    (left right : α → Fraction.Rational) :
    distribution.poweredL2Distance left right ≤
      distribution.essentialMaximumMagnitude
          (fun item => left item - right item) *
        distribution.l1Distance left right :=
  distribution.toContent
    |>.poweredL2Distance_le_essentialMaximumDifference_mul_l1Distance
      left right

/-- A nonnegative essential separation ceiling and an integrated-distance bound give their product as a squared-distance
bound. -/
theorem poweredL2Distance_le_mul_of_l1Distance_le_and_essentialBound
    {α : Type} (distribution : Measure.Distribution α)
    (left right : α → Fraction.Rational) (ceiling epsilon : Fraction.Rational)
    (ceilingNonnegative : 0 ≤ ceiling)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      atom.weight = 0 ∨
        Distance.rationalSeparation (left atom.item) (right atom.item) ≤ ceiling)
    (l1Bound : distribution.l1Distance left right ≤ epsilon) :
    distribution.poweredL2Distance left right ≤ ceiling * epsilon :=
  distribution.toContent
    |>.poweredL2Distance_le_mul_of_l1Distance_le_and_essentialBound
      left right ceiling epsilon ceilingNonnegative bounded l1Bound

end

end Distribution

end Purelib.Measure

end
