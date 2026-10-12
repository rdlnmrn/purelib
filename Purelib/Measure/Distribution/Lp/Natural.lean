module
public import Purelib.Measure.Content.Lp.Natural
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Lp.L1
public import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Event.RationalDistance
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Natural-powered finite Lp quantities

Natural powers of rational separation remain rational.  They provide exact
finite powered-Lp quantities and tail estimates without selecting roots or
constructing completed normed spaces.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib.Data.Rat
/-- Take the expectation of a natural power of the observable's magnitude in the original finite distribution. -/
def poweredLp {α : Type} (distribution : Distribution α) (exponent : Nat)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  distribution.toContent.poweredLp exponent value

/-- Take the expectation of a natural power of the two observables' pointwise rational separation. -/
def poweredLpDistance {α : Type} (distribution : Distribution α)
    (exponent : Nat) (left right : α → Fraction.Rational) : Fraction.Rational :=
  distribution.toContent.poweredLpDistance exponent left right

/-- Every natural-powered magnitude expectation is nonnegative. -/
theorem poweredLp_nonnegative {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (value : α → Fraction.Rational) :
    0 ≤ distribution.poweredLp exponent value :=
  distribution.toContent.poweredLp_nonnegative exponent value

/-- Every natural-powered separation expectation is nonnegative. -/
theorem poweredLpDistance_nonnegative {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    0 ≤ distribution.poweredLpDistance exponent left right :=
  distribution.toContent.poweredLpDistance_nonnegative
    exponent left right

/-- Scaling an observable multiplies its powered expectation by the same power of the factor's magnitude. -/
theorem poweredLp_scale {α : Type} (distribution : Distribution α)
    (exponent : Nat) (factor : Fraction.Rational)
    (value : α → Fraction.Rational) :
    distribution.poweredLp exponent (fun item => factor * value item) =
      Distance.rationalSeparation factor 0 ^ exponent *
        distribution.poweredLp exponent value :=
  distribution.toContent.poweredLp_scale exponent factor value

/-- Scaling both observables multiplies their powered distance by the same power of the factor's magnitude. -/
theorem poweredLpDistance_scale {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (factor : Fraction.Rational) (left right : α → Fraction.Rational) :
    distribution.poweredLpDistance exponent
        (fun item => factor * left item)
        (fun item => factor * right item) =
      Distance.rationalSeparation factor 0 ^ exponent *
        distribution.poweredLpDistance exponent left right :=
  distribution.toContent.poweredLpDistance_scale
    exponent factor left right

/-- Every positive natural-powered distance from an observable to itself vanishes. -/
@[simp] theorem poweredLpDistance_refl {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (value : α → Fraction.Rational) :
    distribution.poweredLpDistance (exponent + 1) value value = 0 :=
  distribution.toContent.poweredLpDistance_refl exponent value

/-- Exchanging the two observables preserves their natural-powered distance. -/
theorem poweredLpDistance_symm {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    distribution.poweredLpDistance exponent left right =
      distribution.poweredLpDistance exponent right left :=
  distribution.toContent.poweredLpDistance_symm exponent left right

/-- The zero exponent gives one for every observable in the retained unit-mass distribution. -/
theorem poweredLp_zero {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) :
    distribution.poweredLp 0 value = 1 := by
  change distribution.toContent.poweredLp 0 value = 1
  rw [distribution.toContent.poweredLp_zero,
    distribution.toContent_total]

/-- A constant observable's powered expectation equals the same power of its magnitude. -/
theorem poweredLp_constant {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (constant : Fraction.Rational) :
    distribution.poweredLp exponent (fun _ => constant) =
      Distance.rationalSeparation constant 0 ^ exponent := by
  change distribution.toContent.poweredLp exponent
      (fun _ => constant) = _
  rw [distribution.toContent.poweredLp_constant,
    distribution.toContent_total, one_mul]

/-- Exponent one gives expected magnitude. -/
theorem poweredLp_one {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) :
    distribution.poweredLp 1 value = distribution.poweredL1 value :=
  distribution.toContent.poweredLp_one value

/-- Exponent two gives expected square. -/
theorem poweredLp_two {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) :
    distribution.poweredLp 2 value = distribution.poweredL2 value :=
  distribution.toContent.poweredLp_two value

/-- Distance exponent one gives expected rational separation. -/
theorem poweredLpDistance_one {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.poweredLpDistance 1 left right =
      distribution.l1Distance left right :=
  distribution.toContent.poweredLpDistance_one left right

/-- Distance exponent two gives expected squared distance. -/
theorem poweredLpDistance_two {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.poweredLpDistance 2 left right =
      distribution.poweredL2Distance left right :=
  distribution.toContent.poweredLpDistance_two left right

/-- Powered magnitude of the pointwise difference equals powered distance of the original observables. -/
theorem poweredLp_sub_eq_poweredLpDistance {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    distribution.poweredLp exponent (fun item => left item - right item) =
      distribution.poweredLpDistance exponent left right :=
  distribution.toContent.poweredLp_sub_eq_poweredLpDistance
    exponent left right

/-- For a positive threshold, its exceedance probability is at most the powered distance divided by the same natural
power of the threshold. -/
theorem probability_separationAtLeast_le_poweredLpDistance
    {α : Type} (distribution : Distribution α) (exponent : Nat)
    (threshold : Fraction.Rational) (positive : 0 < threshold)
    (left right : α → Fraction.Rational) :
    distribution.probability (separationAtLeast threshold left right) ≤
      distribution.poweredLpDistance exponent left right /
        threshold ^ exponent := by
  apply distribution.markov_bound
    (separationAtLeast threshold left right)
    (fun item => Distance.rationalSeparation (left item) (right item) ^ exponent)
    (threshold ^ exponent)
    (Fraction.Order.Arithmetic.pow_pos_direct positive exponent)
  · intro atom member
    exact Fraction.Order.Arithmetic.pow_nonneg_direct
      (Distance.rationalSeparation_nonneg _ _) exponent
  · intro atom member selected
    have thresholdLe : threshold ≤
        Distance.rationalSeparation (left atom.item) (right atom.item) :=
      of_decide_eq_true selected
    exact Fraction.Order.Arithmetic.pow_le_pow_direct positive.le
      thresholdLe exponent

end

end Distribution

end Purelib.Measure

end
