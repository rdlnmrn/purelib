module

public import Purelib.Polynomial.Recurrence.Mode
public import Purelib.Approximation.Rational.Contraction
import Purelib.Algebra.Binomial.Bounds
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Power
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite quantitative bounds for original generalized modes

The original binomial coordinates have explicit rational inside envelopes
and finite requested thresholds. Original zero-root modes remain exact
transients. An outside bound gives an individual-mode growth witness; it
does not assert that several outside modes cannot cancel.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Nat.Choose
open Purelib.Algebra
open Purelib.Data.Rat.Rounding
open Purelib.Approximation.Rational

/-- Above startup, mode quadrance is its squared Pascal coefficient times the root quadrance power. -/
theorem normSq_entry (point : Canonical) (order index : Nat) (afterStartup : order ≤ index) :
    Norm.Basic.normSq (entry point order index) =
      (Pascal.choose index order : Rational) ^ 2 * Norm.Basic.normSq point ^ (index - order) := by
  rw [entry, if_pos afterStartup, Norm.Basic.normSq_mul, Power.normSq_pow]
  rw [Purelib.Data.Gaussian.Cast.natCast_normSq]

/-- A nonnegative radius and positive radius gap give a finite binomial envelope for the original mode.

The original finite binomial expansion bounds its single nonnegative term.
Squaring that scalar bound controls the same Gaussian coordinate, without a
square root, root inverse or infinite sum.
-/
theorem entry_envelope {point : Canonical} {radius rate : Rational}
    (radiusNonnegative : 0 ≤ radius) (gap : radius < rate)
    (pointBound : Norm.Basic.normSq point ≤ radius ^ 2) (order index : Nat) :
    Norm.Basic.normSq (entry point order index) ≤
      (1 / (rate - radius) ^ order) ^ 2 * (rate ^ 2) ^ index := by
  have gapPositive := Order.Arithmetic.sub_pos_direct gap
  have denominatorPositive := Order.Arithmetic.pow_pos_direct gapPositive order
  have coefficientNonnegative := Cast.Order.natCast_le_direct (Nat.zero_le (Pascal.choose index order))
  by_cases afterStartup : order ≤ index
  · have pointPower := Order.Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg point) pointBound (index - order)
    have first := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct pointPower
      (Order.Arithmetic.sq_nonneg_direct (Pascal.choose index order : Rational))
    have binomial := Binomial.term_le radiusNonnegative gapPositive.le index order afterStartup
    have sum : radius + (rate - radius) = rate := by ring1
    rewrite [sum] at binomial
    have amplitude : (Pascal.choose index order : Rational) * radius ^ (index - order) ≤
        rate ^ index / (rate - radius) ^ order :=
      (Order.Field.le_div_iff_pos denominatorPositive).mpr binomial
    have amplitudeNonnegative := Order.Arithmetic.mul_nonneg_direct coefficientNonnegative
      (Order.Arithmetic.pow_nonneg_direct radiusNonnegative (index - order))
    have squared := Order.Arithmetic.pow_le_pow_direct amplitudeNonnegative amplitude 2
    rewrite [normSq_entry point order index afterStartup]
    calc
      _ ≤ (Pascal.choose index order : Rational) ^ 2 * (radius ^ 2) ^ (index - order) := first
      _ = ((Pascal.choose index order : Rational) * radius ^ (index - order)) ^ 2 := by
        rewrite [Semiring.Normalization.product_pow, ← pow_mul, ← pow_mul]
        exact congrArg (fun exponent => (Pascal.choose index order : Rational) ^ 2 * radius ^ exponent)
          (Nat.mul_comm 2 (index - order))
      _ ≤ (rate ^ index / (rate - radius) ^ order) ^ 2 := squared
      _ = _ := by
        change (rate ^ index * ((rate - radius) ^ order)⁻¹) ^ 2 =
          (1 * ((rate - radius) ^ order)⁻¹) ^ 2 * (rate ^ 2) ^ index
        rewrite [_root_.one_mul, Semiring.Normalization.product_pow, ← pow_mul, ← pow_mul]
        have powers : rate ^ (index * 2) = rate ^ (2 * index) := congrArg (fun exponent => rate ^ exponent)
          (Nat.mul_comm index 2)
        rewrite [powers]
        exact Field.mul_comm _ _
  · rewrite [entry, if_neg afterStartup, Norm.Basic.normSq_zero]
    exact Order.Arithmetic.mul_nonneg_direct (Order.Arithmetic.sq_nonneg_direct _)
      (Order.Arithmetic.pow_nonneg_direct (Order.Arithmetic.sq_nonneg_direct rate) index)

/-- The rational radius strictly between a nonnegative squared-norm ceiling and one. -/
@[expose] def quadranceRadius (ceiling : Rational) : Rational := (ceiling + 1) / 2

/-- A nonnegative squared-norm ceiling gives a nonnegative original rational radius. -/
theorem quadranceRadius_nonnegative {ceiling : Rational} (nonnegative : 0 ≤ ceiling) :
    0 ≤ quadranceRadius ceiling :=
  Order.Field.div_nonneg_direct
    (Order.Arithmetic.add_le_add_direct nonnegative (by decide : (0 : Rational) ≤ 1)) (by decide)

/-- A squared-norm ceiling below one gives a rational radius below one. -/
theorem quadranceRadius_lt_one {ceiling : Rational} (lessOne : ceiling < 1) : quadranceRadius ceiling < 1 := by
  apply (Order.Field.div_lt_iff_pos (by decide : (0 : Rational) < 2)).mpr
  have translated := Order.Arithmetic.add_lt_add_right_direct lessOne 1
  exact translated.trans_eq (by decide +kernel : (1 : Rational) + 1 = 1 * 2)

/-- The square of the computed rational radius bounds its original quadrance ceiling. -/
theorem quadranceRadius_square (ceiling : Rational) : ceiling ≤ quadranceRadius ceiling ^ 2 := by
  have doubled : quadranceRadius ceiling * 2 = ceiling + 1 :=
    Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  apply Order.Arithmetic.le_of_mul_le_mul_right_direct (c := (4 : Rational)) _ (by decide)
  calc
    ceiling * 4 ≤ (ceiling + 1) ^ 2 := by
      apply Order.Arithmetic.le_of_sub_nonneg_direct
      exact (Order.Arithmetic.sq_nonneg_direct (ceiling - 1)).trans_eq (by ring1)
    _ = (quadranceRadius ceiling * 2) ^ 2 := congrArg (fun value : Rational => value ^ 2) doubled.symm
    _ = quadranceRadius ceiling ^ 2 * 4 := by ring1

/-- The computed radius is larger than its original strict-inside argument. -/
theorem lt_quadranceRadius {ceiling : Rational} (lessOne : ceiling < 1) : ceiling < quadranceRadius ceiling := by
  apply (Order.Field.lt_div_iff_pos (by decide : (0 : Rational) < 2)).mpr
  have translated := Order.Arithmetic.add_lt_add_right_direct lessOne ceiling
  exact (show ceiling * 2 = ceiling + ceiling by ring1).trans_lt
    (translated.trans_eq (by ring1))

set_option genInjectivity false in
/-- A computed uniform inside-mode request on the same strict rational quadrance ceiling.

The radius, larger rate and gap are retained from the same ceiling. Their
finite coefficient and original contraction depth certify every later finite
reading for any point satisfying that same ceiling, before a point is observed.
-/
structure Inside (ceiling : Rational) (order : Nat) (epsilon : Rational) where
  /-- The retained rational radius above the original squared-norm ceiling. -/
  radius : Rational
  /-- The radius is the original rational midpoint computation. -/
  radius_eq : radius = quadranceRadius ceiling
  /-- The retained larger rational rate strictly below one. -/
  rate : Rational
  /-- The rate is the same midpoint construction on the retained radius. -/
  rate_eq : rate = quadranceRadius radius
  /-- The retained positive difference of those same two radii. -/
  gap : Rational
  /-- The gap comes from the retained rate and radius. -/
  gap_eq : gap = rate - radius
  /-- The original finite squared binomial-envelope coefficient. -/
  coefficient : Rational
  /-- The coefficient uses the same retained gap and original mode order. -/
  coefficient_eq : coefficient = (1 / gap ^ order) ^ 2
  /-- The computed original sufficient finite contraction depth. -/
  index : Nat
  /-- The original bounded contraction search consumes these same retained values. -/
  index_eq : index = Contraction.rateDepth (rate ^ 2) coefficient epsilon
  /-- Every later finite original mode reading pays the same requested quadrance. -/
  bound : ∀ (point : Canonical), Norm.Basic.normSq point ≤ ceiling →
    ∀ later, index ≤ later → Norm.Basic.normSq (entry point order later) ≤ epsilon

constructive_injectivity Inside

namespace Inside

/-- Prepare a uniform finite inside threshold without observing or replacing an original root point. -/
@[expose] def prepare (ceiling : Rational) (nonnegative : 0 ≤ ceiling) (lessOne : ceiling < 1)
    (order : Nat) (epsilon : Rational) (epsilonPositive : 0 < epsilon) : Inside ceiling order epsilon :=
  let radius := quadranceRadius ceiling
  let rate := quadranceRadius radius
  let gap := rate - radius
  let coefficient := (1 / gap ^ order) ^ 2
  let index := Contraction.rateDepth (rate ^ 2) coefficient epsilon
  { radius, radius_eq := rfl, rate, rate_eq := rfl, gap, gap_eq := rfl
    coefficient, coefficient_eq := rfl, index, index_eq := rfl
    bound := by
      intro point pointBound later laterBound
      have radiusNonnegative : 0 ≤ radius := quadranceRadius_nonnegative nonnegative
      have radiusLess : radius < 1 := quadranceRadius_lt_one lessOne
      have rateNonnegative : 0 ≤ rate := quadranceRadius_nonnegative radiusNonnegative
      have rateLess : rate < 1 := quadranceRadius_lt_one radiusLess
      have gapPositive : radius < rate := lt_quadranceRadius radiusLess
      have pointRadius := pointBound.trans (quadranceRadius_square ceiling)
      have envelope := entry_envelope radiusNonnegative gapPositive pointRadius order later
      have squareLess : rate ^ 2 < 1 := by
        have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rateLess.le rateNonnegative
        have bounded : rate ^ 2 ≤ rate := by
          exact (show rate ^ 2 = rate * rate by ring1).trans_le
            (scaled.trans_eq (Field.mul_one_direct _))
        exact bounded.trans_lt rateLess
      have sufficient := Contraction.rateDepth_tail (Order.Arithmetic.sq_nonneg_direct rate) squareLess
        (Order.Arithmetic.sq_nonneg_direct (1 / gap ^ order)) epsilonPositive later laterBound
      exact envelope.trans ((Field.mul_comm _ _).trans_le sufficient) }

/-- Every retained finite window entry after the computed threshold has the same requested quadrance bound. -/
theorem window_bound {ceiling epsilon : Rational} {order : Nat} (request : Inside ceiling order epsilon)
    {point : Canonical} (pointBound : Norm.Basic.normSq point ≤ ceiling) (count : Nat) (index : Fin count)
    (later : request.index ≤ index.val) : Norm.Basic.normSq (window point order count index) ≤ epsilon := by
  rewrite [window_at]
  exact request.bound point pointBound index.val later

end Inside

/-- The original zero-root mode vanishes at every finite index strictly after its own startup coordinate. -/
theorem zero_after (order index : Nat) (later : order < index) : entry (0 : Canonical) order index = 0 := by
  rewrite [entry_zero_root, if_neg (Nat.ne_of_gt later)]
  rfl

/-- Exact zero-root windows retain their same single startup coordinate and vanish afterward. -/
theorem zero_window_after (order count : Nat) (index : Fin count) (later : order < index.val) :
    window (0 : Canonical) order count index = 0 :=
  (window_at _ _ _ _).trans (zero_after order index.val later)

/-- An individual outside generalized mode has an explicit finite quadrance lower bound.

The coefficient has an explicit positive Gaussian quadrance lower bound.
Finite Bernoulli growth and the original positive Pascal coefficient suffice;
no cancellation statement about several modes follows from this bound.
-/
theorem outside_lower {point coefficient : Canonical} {gap floor : Rational}
    (gapPositive : 0 < gap) (floorPositive : 0 < floor)
    (pointBound : 1 + gap ≤ Norm.Basic.normSq point) (coefficientBound : floor ≤ Norm.Basic.normSq coefficient)
    (order extra : Nat) :
    floor * (1 + (extra : Rational) * gap) ≤ Norm.Basic.normSq (coefficient * entry point order (order + extra)) := by
  have afterStartup : order ≤ order + extra := Nat.le_add_right _ _
  have chooseOne : (1 : Rational) ≤ (Pascal.choose (order + extra) order : Rational) := by
    have natural := Nat.succ_le_of_lt (Pascal.positive (order + extra) order afterStartup)
    have cast := Cast.Order.natCast_le_direct natural
    rewrite [Nat.cast_one] at cast
    exact cast
  have chooseSquared := Order.Arithmetic.pow_le_pow_direct (by decide : (0 : Rational) ≤ 1) chooseOne 2
  rewrite [one_pow] at chooseSquared
  have gapNonnegative : 0 ≤ gap := gapPositive.le
  have oneLe : (1 : Rational) ≤ 1 + gap := by
    exact (show (1 : Rational) = 1 + 0 by ring1).trans_le
      (Order.Arithmetic.add_le_add_direct (le_refl _) gapNonnegative)
  have growth := Contraction.power_linear_lower oneLe extra
  rewrite [show (1 + gap) - 1 = gap by ring1] at growth
  have oneGapNonnegative : 0 ≤ (1 : Rational) + gap := (by decide : (0 : Rational) ≤ 1).trans oneLe
  have powers := Order.Arithmetic.pow_le_pow_direct oneGapNonnegative pointBound extra
  have coefficientNonnegative := Norm.Basic.normSq_nonneg coefficient
  rewrite [Norm.Basic.normSq_mul, normSq_entry point order (order + extra) afterStartup, Nat.add_sub_cancel_left]
  calc
    _ ≤ floor * ((1 + gap) ^ extra) :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct growth floorPositive.le
    _ ≤ Norm.Basic.normSq coefficient * (Norm.Basic.normSq point ^ extra) :=
      Order.Arithmetic.mul_le_mul_direct coefficientBound powers
        (Order.Arithmetic.pow_nonneg_direct oneGapNonnegative extra) coefficientNonnegative
    _ ≤ _ := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      ((show Norm.Basic.normSq point ^ extra = 1 * Norm.Basic.normSq point ^ extra from
        (_root_.one_mul _).symm).trans_le
          (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct chooseSquared
            (Order.Arithmetic.pow_nonneg_direct (Norm.Basic.normSq_nonneg point) extra))) coefficientNonnegative

set_option genInjectivity false in
/-- A computed finite individual-mode growth witness from explicit outside and coefficient quadrance gaps. -/
structure Outside (gap floor : Rational) (order : Nat) (target : Rational) where
  /-- The original natural ceiling of the finite growth request. -/
  extra : Nat
  /-- The ceiling consumes the same displayed target and positive growth coefficient. -/
  extra_eq : extra = Floor.ceilNat (target / (floor * gap))
  /-- The original observation index includes the mode's exact startup offset. -/
  index : Nat
  /-- The retained index is the same original mode order plus computed growth allowance. -/
  index_eq : index = order + extra
  /-- Every actual point and coefficient satisfying these same bounds exhibits the requested finite growth. -/
  bound : ∀ (point coefficient : Canonical), 1 + gap ≤ Norm.Basic.normSq point →
    floor ≤ Norm.Basic.normSq coefficient → target ≤ Norm.Basic.normSq (coefficient * entry point order index)

constructive_injectivity Outside

namespace Outside

/-- Compute a genuine finite individual outside-mode witness without any formal-algebra inverse premise. -/
@[expose] def prepare (gap floor : Rational) (gapPositive : 0 < gap) (floorPositive : 0 < floor)
    (order : Nat) (target : Rational) (targetPositive : 0 < target) : Outside gap floor order target :=
  let extra := Floor.ceilNat (target / (floor * gap))
  { extra, extra_eq := rfl, index := order + extra, index_eq := rfl
    bound := by
      intro point coefficient pointBound coefficientBound
      have productPositive := Order.Arithmetic.mul_pos_direct floorPositive gapPositive
      have ratioPositive := Order.Field.div_pos_direct targetPositive productPositive
      have ceiling : target / (floor * gap) ≤ (extra : Rational) :=
        Floor.le_natCast_ceilNat_of_nonneg ratioPositive.le
      have scaled := (Order.Field.div_le_iff_pos productPositive).mp ceiling
      have withUnit : (extra : Rational) * gap ≤ 1 + (extra : Rational) * gap := by
        exact (show (extra : Rational) * gap = 0 + (extra : Rational) * gap by ring1).trans_le
          (Order.Arithmetic.add_le_add_direct (by decide : (0 : Rational) ≤ 1) (le_refl _))
      calc
        target ≤ (extra : Rational) * (floor * gap) := scaled
        _ = floor * ((extra : Rational) * gap) := by ring1
        _ ≤ floor * (1 + (extra : Rational) * gap) :=
          Order.Arithmetic.mul_le_mul_of_nonneg_left_direct withUnit floorPositive.le
        _ ≤ _ := outside_lower gapPositive floorPositive pointBound coefficientBound order extra }

end Outside

end Purelib.Polynomial.Recurrence.Mode

end
