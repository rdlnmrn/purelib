module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter
import Purelib.Geometry.Rational.Box.Outside
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Geometry.Rational.Box.Square.Centered.Separation.Sum
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Tactic.Ring

/-! # Original fixed-point parameter windows and uniform root bounds

The actual retained signed seed square gives a half-gap-dependent candidate
floor and a same-sheet sum floor. The identical increment budget preserves
regularity at both labelled collisions and admits the changed parameter to
the original parameter patch. These statements retain the original source
lift and the actual accepted normalized target owner.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {site : Fin 2} {parameter : Canonical} {original : UnitVertex}
variable {unit : Owner ((unitPolynomial site).eval (sourcePoint site parameter original).base)}
variable {source : Lift (sourcePoint site parameter original) unit}

namespace Anchor

open Purelib.Data.Rat.Fraction.Order

/-- The retained signed-square radius has an intrinsic positive half-gap-dependent squared lower bound. -/
theorem radius_lower (anchor : Anchor source) :
    (9 / 128) * Norm.Basic.normSq (halfGap site parameter) ≤ anchor.seed.separation.radius ^ 2 := by
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := 8) _ (by decide +kernel)
  calc
    _ = ((9 / 128) * 8) * Norm.Basic.normSq (halfGap site parameter) := by ring1
    _ = (9 / 16) * Norm.Basic.normSq (halfGap site parameter) :=
      congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter))
        (by decide +kernel : ((9 / 128) * 8 : Fraction.Rational) = 9 / 16)
    _ ≤ Norm.Basic.normSq (sourcePoint site parameter original).ordinate :=
      parallel_ordinate_lower site parameter original
    _ ≤ 8 * anchor.seed.separation.radius ^ 2 := anchor.seed.separation.norm_le
    _ = _ := Fraction.Field.mul_comm _ _

/-- A paid same-quarter chart displacement stays within the retained source Seed's signed-window budget.

The original quarter ordinate estimate and the same half-gap-dependent
source radius bound pay the center distance. The source lift and complete
known-root Seed remain the original inputs, independent of the target time.
-/
theorem ordinate_near {quarter : UnitCircuitQuarter} {reference target : Fraction.Rational}
    {unit : Owner ((unitPolynomial site).eval
      (sourcePoint site parameter (Waist.direction quarter reference)).base)}
    {source : Lift (sourcePoint site parameter (Waist.direction quarter reference)) unit}
    (anchor : Anchor source) (distance : (target - reference) ^ 2 ≤ 1 / Fraction.Cast.fromInt 65536) :
    Norm.Basic.normSq
      ((sourcePoint site parameter (Waist.direction quarter target)).ordinate -
        (sourcePoint site parameter (Waist.direction quarter reference)).ordinate) ≤
      anchor.seed.separation.radius ^ 2 / Fraction.Cast.fromInt 256 := by
  have movement := quarter_ordinate_distance_le site parameter 2 quarter
    (by decide +kernel) (by decide +kernel) (by decide +kernel) target reference
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct distance
    (Arithmetic.mul_nonneg_direct
      (show (0 : Fraction.Rational) ≤ 25 / 4 by decide +kernel)
      (Norm.Basic.normSq_nonneg (halfGap site parameter)))
  have coefficient : (25 / 4 : Fraction.Rational) * (1 / Fraction.Cast.fromInt 65536) ≤
      (1 / Fraction.Cast.fromInt 256) * (9 / 128) := by decide +kernel
  calc
    _ ≤ (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (target - reference) ^ 2 := movement
    _ ≤ (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (1 / Fraction.Cast.fromInt 65536) := paid
    _ = ((25 / 4) * (1 / Fraction.Cast.fromInt 65536)) * Norm.Basic.normSq (halfGap site parameter) := by ring1
    _ ≤ ((1 / Fraction.Cast.fromInt 256) * (9 / 128)) * Norm.Basic.normSq (halfGap site parameter) :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient (Norm.Basic.normSq_nonneg _)
    _ = (1 / Fraction.Cast.fromInt 256) * ((9 / 128) * Norm.Basic.normSq (halfGap site parameter)) := by ring1
    _ ≤ (1 / Fraction.Cast.fromInt 256) * anchor.seed.separation.radius ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct anchor.radius_lower (by decide +kernel)
    _ = _ := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct 1 (Fraction.Cast.fromInt 256),
        Fraction.Field.div_eq_mul_inv_direct (anchor.seed.separation.radius ^ 2) (Fraction.Cast.fromInt 256)]
      ring1

/-- The actual source signed square supplies the uniform same-sheet sum floor. -/
theorem sumFloor_lower (anchor : Anchor source) :
    (9 / 32) * Norm.Basic.normSq (halfGap site parameter) ≤ 4 * anchor.seed.separation.radius ^ 2 := by
  calc
    _ = (4 * (9 / 128)) * Norm.Basic.normSq (halfGap site parameter) :=
      congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter))
        (by decide +kernel : (4 * (9 / 128) : Fraction.Rational) = 9 / 32).symm
    _ = 4 * ((9 / 128) * Norm.Basic.normSq (halfGap site parameter)) := by ring1
    _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_left_direct anchor.radius_lower (by decide +kernel)

/-- The exact source center supplies the sharper nine-radius same-sheet sum floor. -/
theorem exactSumFloor_lower (anchor : Anchor source) :
    (81 / 128) * Norm.Basic.normSq (halfGap site parameter) ≤ 9 * anchor.seed.separation.radius ^ 2 := by
  calc
    _ = (9 * (9 / 128)) * Norm.Basic.normSq (halfGap site parameter) :=
      congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter))
        (by decide +kernel : (9 * (9 / 128) : Fraction.Rational) = 81 / 128).symm
    _ = 9 * ((9 / 128) * Norm.Basic.normSq (halfGap site parameter)) := by ring1
    _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_left_direct anchor.radius_lower (by decide +kernel)

/-- Every admitted changed parameter remains distinct from the original labelled collision. -/
theorem target_regular (anchor : Anchor source) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) : parameter + increment ≠ criticalValue site := by
  have displacement := Polynomial.Quadratic.Split.halfGap_mul_two (criticalValue site) parameter
    (by decide +kernel : (2 : Canonical) ≠ 0)
  change halfGap site parameter * 2 = parameter - criticalValue site at displacement
  have strict := Arithmetic.mul_lt_mul_of_pos_right_direct
    (by decide +kernel : (1 / 256 : Fraction.Rational) < 4) anchor.gapNorm_positive
  intro equal
  have incrementEq : increment = -(halfGap site parameter * 2) := by
    calc
      increment = (parameter + increment) - parameter := by ring1
      _ = criticalValue site - parameter := congrArg (fun value : Canonical => value - parameter) equal
      _ = -(halfGap site parameter * 2) := by
        rewrite [displacement]
        ring1
  have normEq : Norm.Basic.normSq increment = 4 * Norm.Basic.normSq (halfGap site parameter) := by
    rewrite [incrementEq, Norm.Basic.normSq_neg, Norm.Basic.normSq_mul,
      show Norm.Basic.normSq (2 : Canonical) = 4 by decide +kernel]
    exact Fraction.Field.mul_comm _ _
  change Norm.Basic.normSq increment ≤ _ at admitted
  rewrite [normEq] at admitted
  exact strict.2 admitted

/-- Every admitted changed parameter pays the same original parameter-square admission. -/
theorem target_inside (anchor : Anchor source) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) : (parameterBox site).Contains (parameter + increment) := by
  have movement : Norm.Basic.normSq increment ≤ (1 / Fraction.Cast.fromInt 65536 : Fraction.Rational) :=
    admitted.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (halfGap_bound site parameter anchor.bound) (by decide +kernel)).trans_eq
        (by decide +kernel : ((1 / 256) * (1 / 256) : Fraction.Rational) = 1 / Fraction.Cast.fromInt 65536))
  apply Waist.parameter_inside site (parameter + increment)
  have shifted : parameter + increment - criticalValue site = (parameter - criticalValue site) + increment := by
    ring1
  rewrite [shifted]
  exact ((Norm.Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct anchor.bound movement) (by decide +kernel))).trans
        (by decide +kernel : (2 * (1 / 64 + 1 / Fraction.Cast.fromInt 65536) : Fraction.Rational) ≤ 1 / 16)

/-- Every admitted changed parameter remains distinct from the other original fixed branch value. -/
theorem target_ne_remaining (anchor : Anchor source) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) : parameter + increment ≠ remainingValue site :=
  parameter_ne_remaining site (anchor.target_inside increment admitted)

end Anchor

namespace Step

variable {anchor : Anchor source} {increment : Canonical}

/-- Every actual target-root candidate inherits the original signed-window norm floor. -/
theorem candidate_normSq_lower (step : Step anchor increment) {candidate : Canonical}
    {state : step.root.value.name.process.State} (possible : step.root.value.name.process.Possible state candidate) :
    (9 / 128) * Norm.Basic.normSq (halfGap site parameter) ≤ Norm.Basic.normSq candidate := by
  have lower := anchor.seed.separation.zero.margin_le_normSq_sub (step.target_candidate_inside possible)
  rewrite [anchor.seed.separation.zero_margin, Basic.sub_zero] at lower
  exact anchor.radius_lower.trans lower

/-- Independently possible source and target normalized readings have the uniform original half-gap sum floor. -/
theorem sum_normSq_uniform (step : Step anchor increment) {first last : Canonical}
    {sourceState : anchor.seed.certificate.value.name.process.State} {targetState : step.root.value.name.process.State}
    (sourcePossible : anchor.seed.certificate.value.name.process.Possible sourceState first)
    (targetPossible : step.root.value.name.process.Possible targetState last) :
    (9 / 32) * Norm.Basic.normSq (halfGap site parameter) ≤ Norm.Basic.normSq (first + last) :=
  anchor.sumFloor_lower.trans (step.sum_normSq_lower sourcePossible targetPossible)

/-- The exact original source ordinate and every actual target reading retain the same uniform sum floor. -/
theorem exact_source_sum_normSq_lower (step : Step anchor increment) {last : Canonical}
    {state : step.root.value.name.process.State} (possible : step.root.value.name.process.Possible state last) :
    (81 / 128) * Norm.Basic.normSq (halfGap site parameter) ≤
      Norm.Basic.normSq ((sourcePoint site parameter original).ordinate + last) :=
  anchor.exactSumFloor_lower.trans
    (anchor.seed.separation.center_sum_normSq_lower (step.target_candidate_inside possible))

/-- Every actual target candidate retains the upper norm bound of its same original signed seed square. -/
theorem candidate_normSq_upper (step : Step anchor increment) {candidate : Canonical}
    {state : step.root.value.name.process.State} (possible : step.root.value.name.process.Possible state candidate) :
    Norm.Basic.normSq candidate ≤ 20 * anchor.seed.separation.radius ^ 2 :=
  anchor.seed.separation.candidate_normSq_upper (step.target_candidate_inside possible)

end Step

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter
