module
import Purelib.Algebra.Field.Ratio
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
@[expose] public section

/-!
# Polynomial stationarity and Snell's law
-/

namespace Purelib.Physics.Optics.Snell.Polynomial

variable {K : Type*} [ExplicitField K]

/-- The squared length a² + x² of the upper path segment. -/
def snellUpperPathQuadrance (a x : K) : K := a ^ 2 + x ^ 2

/-- The squared length (c − x)² + b² of the lower path segment. -/
def snellLowerPathQuadrance (b c x : K) : K :=
  (c - x) ^ 2 + b ^ 2

section
open Purelib.Physics.Optics.Snell
/-- The horizontal squared displacement divided by the upper path quadrance. -/
def snellUpperSpread (a x : K) : K :=
  x ^ 2 / Polynomial.snellUpperPathQuadrance a x

/-- The horizontal squared displacement divided by the lower path quadrance. -/
def snellLowerSpread (b c x : K) : K :=
  (c - x) ^ 2 / Polynomial.snellLowerPathQuadrance b c x

end

open Purelib.Algebra.Field in
open Purelib.Physics.Optics.Snell in
/-- A cleared stationary-path equation implies the polynomial form of Snell's law.

Nonzero path quadrances allow cancellation to obtain the speed-square and spread cross-product. Nonzero first
speed-square and upper spread additionally yield equality of the two ratios. -/
theorem problem_16
    (a b c x firstSpeedSquare secondSpeedSquare : K)
    (upperNonzero : Polynomial.snellUpperPathQuadrance a x ≠ 0)
    (lowerNonzero : Polynomial.snellLowerPathQuadrance b c x ≠ 0)
    (firstSpeedNonzero : firstSpeedSquare ≠ 0)
    (upperSpreadNonzero : Polynomial.snellUpperSpread a x ≠ 0)
    (stationaryCleared :
      Polynomial.snellLowerPathQuadrance b c x * x ^ 2 * secondSpeedSquare =
        Polynomial.snellUpperPathQuadrance a x * (c - x) ^ 2 * firstSpeedSquare) :
    secondSpeedSquare * Polynomial.snellUpperSpread a x =
        firstSpeedSquare * Polynomial.snellLowerSpread b c x ∧
      secondSpeedSquare / firstSpeedSquare =
        Polynomial.snellLowerSpread b c x / Polynomial.snellUpperSpread a x := by
  let upper := Polynomial.snellUpperPathQuadrance a x
  let lower := Polynomial.snellLowerPathQuadrance b c x
  let firstSpread := Polynomial.snellUpperSpread a x
  let secondSpread := Polynomial.snellLowerSpread b c x
  have upperSpreadCleared : firstSpread * upper = x ^ 2 := by
    unfold firstSpread Polynomial.snellUpperSpread upper
    exact ExplicitField.div_mul_cancel (x ^ 2) upperNonzero
  have lowerSpreadCleared : secondSpread * lower = (c - x) ^ 2 := by
    unfold secondSpread Polynomial.snellLowerSpread lower
    exact ExplicitField.div_mul_cancel ((c - x) ^ 2) lowerNonzero
  have metricProductNonzero : upper * lower ≠ 0 :=
    ExplicitField.mul_ne_zero upperNonzero lowerNonzero
  have speedSpreadRelation :
      secondSpeedSquare * firstSpread = firstSpeedSquare * secondSpread := by
    apply ExplicitField.eq_of_mul_eq_mul_right metricProductNonzero
    calc
      (secondSpeedSquare * firstSpread) * (upper * lower) =
          lower * x ^ 2 * secondSpeedSquare := by
            rw [← upperSpreadCleared]
            ring1
      _ = upper * (c - x) ^ 2 * firstSpeedSquare := stationaryCleared
      _ = (firstSpeedSquare * secondSpread) * (upper * lower) := by
        rw [← lowerSpreadCleared]
        ring1
  constructor
  · exact speedSpreadRelation
  · apply Ratio.ratio_eq_of_cross_product
      firstSpeedNonzero upperSpreadNonzero
    calc
      secondSpeedSquare * firstSpread =
          firstSpeedSquare * secondSpread := speedSpreadRelation
      _ = secondSpread * firstSpeedSquare := by ring1
end Purelib.Physics.Optics.Snell.Polynomial

end
