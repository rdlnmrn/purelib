module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Dyadic.Grid.EightBit
import Purelib.Data.Rat.Dyadic.Power
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.NatCast
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

open Purelib.Data.Rat.Dyadic

open Purelib.Data.Rat.Dyadic.Grid

section
@[expose] public section

/-!
# Explicit finite geometric refinement

This module turns a positive rational accuracy request into a finite natural
index at which a displayed quarter-power allowance is small enough.  The
search has a coefficient-computed finite fuel certificate.  It stops at the
first successful comparison, and neither its definition nor its proof refers
to a limit, an infinite sequence as an object, or an Archimedean existence
principle.
-/

namespace Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic

/-! ## Finite dyadic square-root under-approximations -/

/-- A positive dyadic rational whose square is found by the bounded quarter-radius scan. This is an executable finite
substitute for extracting a real square root when only a rational radius below a positive target is needed. -/
def Geometric.dyadicSquareRadius (target :
  Fraction.Rational) : Fraction.Rational :=
  (1 / 2 : Fraction.Rational) ^ Search.firstQuarterBelow 1 0 target

/-- The dyadic square-radius selector always returns a strictly positive rational. -/
theorem Geometric.dyadicSquareRadius_positive (target :
  Fraction.Rational) :
    0 < Geometric.dyadicSquareRadius target := by
  unfold Geometric.dyadicSquareRadius
  exact Fraction.Order.Arithmetic.pow_pos_direct (by decide) _

/-- The selected dyadic radius squared equals the quarter-radius at its retained search stage. -/
theorem dyadicSquareRadius_sq_eq (target :
  Fraction.Rational) :
    Geometric.dyadicSquareRadius target ^ 2 =
      Geometric.Basic.quarterRadius 1 (Search.firstQuarterBelow 1 0 target) := by
  unfold Geometric.dyadicSquareRadius
  rw [Geometric.Basic.quarterRadius_eq_mul_pow]
  simp only [_root_.one_mul]
  rw [← pow_mul, Nat.mul_comm (Search.firstQuarterBelow 1 0 target) 2,
    pow_mul, show (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 by decide]

/-- For a positive target, the selected dyadic radius has square strictly below the target. -/
theorem Geometric.dyadicSquareRadius_sq_lt {target :
  Fraction.Rational}
    (positive : 0 < target) :
    Geometric.dyadicSquareRadius target ^ 2 < target := by
  rw [dyadicSquareRadius_sq_eq]
  exact Search.firstQuarterBelow_accurate 1 (by decide) 0 target positive

/-- Every selected dyadic square-radius is at most one. -/
theorem dyadicSquareRadius_le_one (target :
  Fraction.Rational) :
    Geometric.dyadicSquareRadius target <= 1 := by
  unfold Geometric.dyadicSquareRadius
  have bound := Fraction.Order.Arithmetic.pow_le_pow_direct
    (by decide : (0 : Fraction.Rational) <= 1 / 2)
    (by decide : (1 / 2 : Fraction.Rational) <= 1)
    (Search.firstQuarterBelow 1 0 target)
  simpa only [one_pow] using bound

end Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic

end

end

section
/-!
# Rounded, checked finite square-root proposals

Round each speculative Newton point to a dyadic grid before checking it and
before computing the next point.  This avoids carrying the exact Newton
orbit's rapidly growing denominators into an accepted root sample.

The predicate, not Newton convergence or a rounding estimate, certifies the
returned point.  A finite unsuccessful search returns `none`; callers retain
their independently proved total fallback.  No floating-point arithmetic or
external certificate producer is involved.
-/

@[expose] public section

namespace Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic.CheckedSquareRootNewton

/-- Start at the square-root scale of a squared residual request. The grid is dyadic, so its denominator does not
inherit the request's coefficient complexity. Rejected proposals refine it; this initial scale alone is not asserted to
guarantee acceptance. -/
def gridFor (target :
  Fraction.Rational) : Fraction.Rational :=
  Approximation.Rational.SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius target

/-- The initial checked square-root grid is strictly positive. -/
theorem gridFor_positive (target
  : Fraction.Rational) : 0 < gridFor target :=
  Approximation.Rational.SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_positive target

/-- For a positive target, the initial grid size squared is strictly below that target. -/
theorem gridFor_sq_lt {target :
  Fraction.Rational} (positive : 0 < target) :
    gridFor target ^ 2 < target :=
  Approximation.Rational.SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_sq_lt positive
end Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic.CheckedSquareRootNewton

end

end

section
@[expose] public section

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

namespace Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic

/-- A positive target at most one over 2304 gives a dyadic square-radius at most one over 64. -/
public theorem dyadicSquareRadius_le_oneSixtyFour
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (targetUpper : target ≤ (1 / 2304 : Fraction.Rational)) :
    Geometric.dyadicSquareRadius target ≤ (1 / 64 : Fraction.Rational)
      := by
  let exponent := Search.firstQuarterBelow 1 0 target
  have radiusEq : Geometric.dyadicSquareRadius target =
      (1 / 2 : Fraction.Rational) ^ exponent := rfl
  have squareLt : ((1 / 2 : Fraction.Rational) ^ exponent) ^ 2 < target := by
    rw [← radiusEq]
    exact Geometric.dyadicSquareRadius_sq_lt targetPositive
  have sixLe : 6 ≤ exponent := by
    by_cases order : 6 ≤ exponent
    · exact order
    · have exponentLe : exponent ≤ 5 := by omega
      have fifthLe := Power.halfPow_antitone exponentLe
      have fifthNonnegative : (0 : Fraction.Rational) ≤ (1 / 2 : Fraction.Rational) ^ 5 :=
        Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) 5
      have fifthSquareLe : ((1 / 2 : Fraction.Rational) ^ 5) ^ 2 ≤
          ((1 / 2 : Fraction.Rational) ^ exponent) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct fifthNonnegative fifthLe 2
      have oneOver1024Le : (1 / 1024 : Fraction.Rational) ≤
          ((1 / 2 : Fraction.Rational) ^ exponent) ^ 2 := by
        calc
          (1 / 1024 : Fraction.Rational) = ((1 / 2 : Fraction.Rational) ^ 5) ^ 2 := by
            have thirtySecondUnit : (1 / 32 : Fraction.Rational) = 8 * EightBit.unit :=
              EightBit.scaledUnit 1 8 32 (by decide) (by ring1)
            rw [EightBit.halfPowFive, EightBit.oneOver1024_eq_sixtyFourUnitSquare,
              thirtySecondUnit, pow_two]
            ring1
          _ ≤ ((1 / 2 : Fraction.Rational) ^ exponent) ^ 2 := fifthSquareLe
      have squareUpper : ((1 / 2 : Fraction.Rational) ^ exponent) ^ 2 ≤ 1 / 2304 :=
        squareLt.le.trans targetUpper
      have strictConstant : (1 / 2304 : Fraction.Rational) < 1 / 1024 := by
        have productPositive : (0 : Fraction.Rational) < 2304 * 1024 :=
          Fraction.Order.Arithmetic.mul_pos_direct
            (Fraction.Order.NatCast.natCast_pos_direct 2304 (by omega)) (Fraction.Order.NatCast.natCast_pos_direct 1024
              (by omega))
        apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
          (c := (2304 : Fraction.Rational) * 1024) _ productPositive
        calc
          (1 / 2304 : Fraction.Rational) * (2304 * 1024) = 1024 := by
            rw [show (1 / 2304 : Fraction.Rational) * (2304 * 1024) =
              ((1 / 2304 : Fraction.Rational) * 2304) * 1024 by ring1]
            have cancel2304 : (1 / 2304 : Fraction.Rational) * 2304 = 1 :=
              Fraction.Field.div_mul_cancel_of_ne _ _
                (Fraction.Order.NatCast.natCast_pos_direct 2304 (by omega)).ne'
            rw [cancel2304]
            ring1
          _ < 2304 := Fraction.Cast.Order.natCast_lt_direct
            (m := 1024) (n := 2304) (by omega)
          _ = (1 / 1024 : Fraction.Rational) * (2304 * 1024) := by
            rw [show (1 / 1024 : Fraction.Rational) * (2304 * 1024) =
              2304 * ((1 / 1024 : Fraction.Rational) * 1024) by ring1]
            have cancel1024 : (1 / 1024 : Fraction.Rational) * 1024 = 1 :=
              Fraction.Field.div_mul_cancel_of_ne _ _
                (Fraction.Order.NatCast.natCast_pos_direct 1024 (by omega)).ne'
            rw [cancel1024]
            ring1
      have impossible : (1 / 1024 : Fraction.Rational) < 1 / 1024 := by
        calc
          (1 / 1024 : Fraction.Rational) ≤ ((1 / 2 : Fraction.Rational) ^ exponent) ^ 2 :=
            oneOver1024Le
          _ ≤ 1 / 2304 := squareUpper
          _ < 1 / 1024 := strictConstant
      exact (lt_irrefl _ impossible).elim
  calc
    Geometric.dyadicSquareRadius target =
        (1 / 2 : Fraction.Rational) ^ exponent := radiusEq
    _ ≤ (1 / 2 : Fraction.Rational) ^ 6 := Power.halfPow_antitone sixLe
    _ = (1 / 64 : Fraction.Rational) := EightBit.halfPowSix

end Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic

end
