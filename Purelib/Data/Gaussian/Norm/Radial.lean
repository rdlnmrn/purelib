module

public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Paid transfer of a rational radial collar

The request depends only on fixed quadrance bounds, a leading-inverse
quadrance and a positive collar width. Its residual cap transfers an actual
candidate's strict unit-circle collar to the same displaced read root.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Radial

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat

set_option genInjectivity false in
/-- Fixed rational data sufficient to preserve half an original radial collar.

The coefficient and denominator are computed once before either endpoint
is observed. The cap pays a displacement bounded by residual times the
leading-inverse quadrance, with the two endpoint quadrances bounded separately.
-/
structure Request (candidateBound readBound beta width : Rational) where
  /-- The candidate quadrance bound is nonnegative. -/
  candidateBoundNonnegative : 0 ≤ candidateBound
  /-- The read-root quadrance bound is nonnegative. -/
  readBoundNonnegative : 0 ≤ readBound
  /-- The leading-inverse quadrance is nonnegative. -/
  betaNonnegative : 0 ≤ beta
  /-- The prescribed collar width is positive. -/
  widthPositive : 0 < width
  /-- The retained coefficient multiplying the residual. -/
  coefficient : Rational
  /-- The coefficient uses the original two endpoint bounds and inverse norm. -/
  coefficient_eq : coefficient = 2 * (candidateBound + readBound) * beta
  /-- The retained positive residual denominator. -/
  denominator : Rational
  /-- The denominator leaves a fixed factor-eight collar reserve. -/
  denominator_eq : denominator = 8 * (1 + coefficient)
  /-- The sufficient residual cap. -/
  cap : Rational
  /-- The cap uses the same retained denominator. -/
  cap_eq : cap = width ^ 2 / denominator
  /-- Half the prescribed collar, shared by the two radial endpoints. -/
  halfWidth : Rational
  /-- The retained half width is computed from the original width. -/
  halfWidth_eq : halfWidth = width / 2
  /-- The nonnegative inside quadrance ceiling. -/
  ceiling : Rational
  /-- The ceiling retains half the original inside collar. -/
  ceiling_eq : ceiling = max 0 (1 - halfWidth)
  /-- The outside quadrance floor. -/
  floor : Rational
  /-- The floor retains half the original outside collar. -/
  floor_eq : floor = 1 + halfWidth

constructive_injectivity Request

namespace Request

/-- Compute the radial residual request from fixed bounds before observing either endpoint. -/
@[expose] def prepare (candidateBound readBound beta width : Rational)
    (candidateBoundNonnegative : 0 ≤ candidateBound) (readBoundNonnegative : 0 ≤ readBound)
    (betaNonnegative : 0 ≤ beta) (widthPositive : 0 < width) :
    Request candidateBound readBound beta width :=
  let coefficient := 2 * (candidateBound + readBound) * beta
  let denominator := 8 * (1 + coefficient)
  let halfWidth := width / 2
  { candidateBoundNonnegative, readBoundNonnegative, betaNonnegative, widthPositive,
    coefficient, coefficient_eq := rfl, denominator, denominator_eq := rfl,
    cap := width ^ 2 / denominator, cap_eq := rfl, halfWidth, halfWidth_eq := rfl,
    ceiling := max 0 (1 - halfWidth), ceiling_eq := rfl,
    floor := 1 + halfWidth, floor_eq := rfl }

variable {candidateBound readBound beta width : Rational}
    (request : Request candidateBound readBound beta width)

/-- The fixed residual coefficient is nonnegative. -/
theorem coefficient_nonnegative : 0 ≤ request.coefficient := by
  have sum := Arithmetic.add_le_add_direct request.candidateBoundNonnegative request.readBoundNonnegative
  rewrite [_root_.zero_add] at sum
  rewrite [request.coefficient_eq]
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2) sum) request.betaNonnegative

/-- The retained denominator is strictly positive, including zero inverse norm. -/
theorem denominator_positive : 0 < request.denominator := by
  rewrite [request.denominator_eq]
  exact Arithmetic.mul_pos_direct (by decide : (0 : Rational) < 8)
    (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide : (0 : Rational) < 1)
      request.coefficient_nonnegative)

/-- The residual cap is strictly positive. -/
theorem cap_positive : 0 < request.cap := by
  rewrite [request.cap_eq]
  exact Field.div_pos_direct (Arithmetic.pow_pos_direct request.widthPositive 2) request.denominator_positive

/-- Half the retained positive collar is positive. -/
theorem halfWidth_positive : 0 < request.halfWidth := by
  rewrite [request.halfWidth_eq]
  exact Field.div_pos_direct request.widthPositive (by decide : (0 : Rational) < 2)

/-- The retained half width doubles to the original collar. -/
theorem halfWidth_double : request.halfWidth * 2 = width := by
  rewrite [request.halfWidth_eq]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)

/-- The inside ceiling is nonnegative. -/
theorem ceiling_nonnegative : 0 ≤ request.ceiling := by
  rewrite [request.ceiling_eq]
  exact Basic.le_max_left _ _

/-- The inside ceiling is strictly below unit quadrance. -/
theorem ceiling_lt_one : request.ceiling < 1 := by
  have shifted := Arithmetic.add_lt_add_right_direct request.halfWidth_positive (1 - request.halfWidth)
  have below : 1 - request.halfWidth < 1 := by
    calc
      _ = 0 + (1 - request.halfWidth) := by ring1
      _ < request.halfWidth + (1 - request.halfWidth) := shifted
      _ = 1 := by ring1
  rewrite [request.ceiling_eq]
  exact Basic.max_lt (by decide +kernel) below

/-- The outside floor lies strictly beyond unit quadrance. -/
theorem one_lt_floor : 1 < request.floor := by
  rewrite [request.floor_eq]
  have shifted := Arithmetic.add_lt_add_right_direct request.halfWidth_positive 1
  calc
    _ = 0 + 1 := by ring1
    _ < request.halfWidth + 1 := shifted
    _ = 1 + request.halfWidth := by ring1

/-- Paying the residual cap bounds the squared quadrance change by the squared half collar. -/
private theorem paid_square {residual : Rational} (paid : residual ≤ request.cap) :
    residual * request.coefficient ≤ request.halfWidth ^ 2 := by
  have reserve : 4 * request.coefficient ≤ request.denominator := by
    apply Arithmetic.le_of_sub_nonneg_direct
    have sum := Arithmetic.add_le_add_direct (by decide : (0 : Rational) ≤ 8)
      (Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 4) request.coefficient_nonnegative)
    calc
      0 = 0 + 0 := by ring1
      _ ≤ 8 + 4 * request.coefficient := sum
      _ = request.denominator - 4 * request.coefficient := by rewrite [request.denominator_eq]; ring1
  have capProduct : request.cap * request.denominator = width ^ 2 := by
    rewrite [request.cap_eq]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ request.denominator_positive.ne'
  have widthSquare : width ^ 2 = request.halfWidth ^ 2 * 4 := by
    calc
      _ = (request.halfWidth * 2) ^ 2 := congrArg (fun value => value ^ 2) request.halfWidth_double.symm
      _ = request.halfWidth ^ 2 * 4 := by ring1
  have capBound : request.cap * request.coefficient ≤ request.halfWidth ^ 2 := by
    apply Arithmetic.le_of_mul_le_mul_right_direct (c := request.denominator) _ request.denominator_positive
    calc
      request.cap * request.coefficient * request.denominator =
          (request.cap * request.denominator) * request.coefficient := by ring1
      _ = request.halfWidth ^ 2 * (4 * request.coefficient) := by rewrite [capProduct, widthSquare]; ring1
      _ ≤ request.halfWidth ^ 2 * request.denominator :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct reserve (Arithmetic.sq_nonneg_direct _)
  exact (Arithmetic.mul_le_mul_of_nonneg_right_direct paid request.coefficient_nonnegative).trans capBound

/-- The same paid displacement bounds the signed quadrance difference in both directions.

Only the original endpoint norm bound, original squared-displacement payment
and fixed request are used; the constructor does not scan either point.
-/
theorem difference_bound (candidate readRoot : Canonical) {residual : Rational}
    (candidateBounded : Norm.Basic.normSq candidate ≤ candidateBound)
    (readBounded : Norm.Basic.normSq readRoot ≤ readBound)
    (displacement : Norm.Basic.normSq (candidate - readRoot) ≤ residual * beta)
    (paid : residual ≤ request.cap) :
    -request.halfWidth ≤ Norm.Basic.normSq candidate - Norm.Basic.normSq readRoot ∧
      Norm.Basic.normSq candidate - Norm.Basic.normSq readRoot ≤ request.halfWidth := by
  have sumBound := Arithmetic.add_le_add_direct candidateBounded readBounded
  have displacementBound := Arithmetic.mul_le_mul_of_nonneg_left_direct displacement
    (by decide : (0 : Rational) ≤ 2)
  have combined := Arithmetic.mul_le_mul_direct displacementBound sumBound
    (Arithmetic.add_le_add_direct (Norm.Basic.normSq_nonneg candidate) (Norm.Basic.normSq_nonneg readRoot))
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2)
      ((Norm.Basic.normSq_nonneg _).trans displacement))
  have squares : (Norm.Basic.normSq candidate - Norm.Basic.normSq readRoot) ^ 2 ≤ request.halfWidth ^ 2 := by
    calc
      _ ≤ 2 * Norm.Basic.normSq (candidate - readRoot) *
          (Norm.Basic.normSq candidate + Norm.Basic.normSq readRoot) := normSq_difference_sq_le_two_mul _ _
      _ ≤ (2 * (residual * beta)) * (candidateBound + readBound) := combined
      _ = residual * request.coefficient := by rewrite [request.coefficient_eq]; ring1
      _ ≤ request.halfWidth ^ 2 := request.paid_square paid
  exact ⟨Arithmetic.neg_le_of_sq_le_sq_direct request.halfWidth_positive.le squares,
    Arithmetic.le_of_sq_le_sq_direct request.halfWidth_positive.le squares⟩

/-- A strict squared collar and original inside sign give a strict linear inside collar. -/
private theorem inside_collar {quadrance : Rational} (inside : quadrance < 1)
    (collar : width ^ 2 < (quadrance - 1) ^ 2) : width < 1 - quadrance := by
  by_cases separated : width < 1 - quadrance
  · exact separated
  · have reverse := Arithmetic.le_of_not_gt_direct separated
    have squares := Arithmetic.pow_le_pow_direct (Arithmetic.sub_pos_direct inside).le reverse 2
    have identity : (1 - quadrance) ^ 2 = (quadrance - 1) ^ 2 := by ring1
    rewrite [identity] at squares
    exact ((not_lt_of_ge squares) collar).elim

/-- A strict squared collar and original outside sign give a strict linear outside collar. -/
private theorem outside_collar {quadrance : Rational} (outside : 1 < quadrance)
    (collar : width ^ 2 < (quadrance - 1) ^ 2) : width < quadrance - 1 := by
  by_cases separated : width < quadrance - 1
  · exact separated
  · have reverse := Arithmetic.le_of_not_gt_direct separated
    have squares := Arithmetic.pow_le_pow_direct (Arithmetic.sub_pos_direct outside).le reverse 2
    exact ((not_lt_of_ge squares) collar).elim

/-- A paid perturbation of the original inside candidate remains below the retained inside ceiling. -/
theorem inside (candidate readRoot : Canonical) {residual : Rational}
    (candidateBounded : Norm.Basic.normSq candidate ≤ candidateBound)
    (readBounded : Norm.Basic.normSq readRoot ≤ readBound)
    (collar : width ^ 2 < (Norm.Basic.normSq candidate - 1) ^ 2)
    (inside : Norm.Basic.normSq candidate < 1)
    (displacement : Norm.Basic.normSq (candidate - readRoot) ≤ residual * beta)
    (paid : residual ≤ request.cap) : Norm.Basic.normSq readRoot ≤ request.ceiling := by
  have difference := (request.difference_bound candidate readRoot candidateBounded readBounded displacement paid).1
  have separated := inside_collar inside collar
  have candidateLess : Norm.Basic.normSq candidate < 1 - width := by
    have shifted := Arithmetic.add_lt_add_right_direct separated (Norm.Basic.normSq candidate - width)
    calc
      _ = width + (Norm.Basic.normSq candidate - width) := by ring1
      _ < (1 - Norm.Basic.normSq candidate) + (Norm.Basic.normSq candidate - width) := shifted
      _ = 1 - width := by ring1
  have upper : Norm.Basic.normSq readRoot ≤ Norm.Basic.normSq candidate + request.halfWidth := by
    have shifted := Arithmetic.add_le_add_right_direct difference (Norm.Basic.normSq readRoot + request.halfWidth)
    calc
      _ = -request.halfWidth + (Norm.Basic.normSq readRoot + request.halfWidth) := by ring1
      _ ≤ (Norm.Basic.normSq candidate - Norm.Basic.normSq readRoot) +
          (Norm.Basic.normSq readRoot + request.halfWidth) := shifted
      _ = Norm.Basic.normSq candidate + request.halfWidth := by ring1
  have separatedRead := Arithmetic.add_lt_add_right_direct candidateLess request.halfWidth
  have endpoint : 1 - width + request.halfWidth = 1 - request.halfWidth := by
    calc
      _ = 1 - request.halfWidth * 2 + request.halfWidth :=
        congrArg (fun value => 1 - value + request.halfWidth) request.halfWidth_double.symm
      _ = 1 - request.halfWidth := by ring1
  rewrite [endpoint] at separatedRead
  rewrite [request.ceiling_eq]
  exact (upper.trans_lt separatedRead).le.trans (Basic.le_max_right _ _)

/-- A paid perturbation of the original outside candidate remains above the retained outside floor. -/
theorem outside (candidate readRoot : Canonical) {residual : Rational}
    (candidateBounded : Norm.Basic.normSq candidate ≤ candidateBound)
    (readBounded : Norm.Basic.normSq readRoot ≤ readBound)
    (collar : width ^ 2 < (Norm.Basic.normSq candidate - 1) ^ 2)
    (outside : 1 < Norm.Basic.normSq candidate)
    (displacement : Norm.Basic.normSq (candidate - readRoot) ≤ residual * beta)
    (paid : residual ≤ request.cap) : request.floor ≤ Norm.Basic.normSq readRoot := by
  have difference := (request.difference_bound candidate readRoot candidateBounded readBounded displacement paid).2
  have separated := outside_collar outside collar
  have candidateLess : 1 + width < Norm.Basic.normSq candidate := by
    have shifted := Arithmetic.add_lt_add_right_direct separated 1
    calc
      _ = width + 1 := by ring1
      _ < (Norm.Basic.normSq candidate - 1) + 1 := shifted
      _ = Norm.Basic.normSq candidate := by ring1
  have lower : Norm.Basic.normSq candidate - request.halfWidth ≤ Norm.Basic.normSq readRoot := by
    have shifted := Arithmetic.add_le_add_right_direct difference (Norm.Basic.normSq readRoot - request.halfWidth)
    calc
      _ = (Norm.Basic.normSq candidate - Norm.Basic.normSq readRoot) +
          (Norm.Basic.normSq readRoot - request.halfWidth) := by ring1
      _ ≤ request.halfWidth + (Norm.Basic.normSq readRoot - request.halfWidth) := shifted
      _ = Norm.Basic.normSq readRoot := by ring1
  have separatedRead := Arithmetic.add_lt_add_right_direct candidateLess (-request.halfWidth)
  have endpoint : (1 + width) + -request.halfWidth = request.floor := by
    calc
      _ = (1 + request.halfWidth * 2) + -request.halfWidth :=
        congrArg (fun value => (1 + value) + -request.halfWidth) request.halfWidth_double.symm
      _ = 1 + request.halfWidth := by ring1
      _ = request.floor := request.floor_eq.symm
  rewrite [endpoint] at separatedRead
  have endIdentity : Norm.Basic.normSq candidate + -request.halfWidth =
      Norm.Basic.normSq candidate - request.halfWidth :=
    rfl
  rewrite [endIdentity] at separatedRead
  exact separatedRead.le.trans lower

end Request
end Purelib.Data.Gaussian.Norm.Radial

end
