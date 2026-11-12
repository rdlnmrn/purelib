module

public import Purelib.Polynomial.Recurrence.Mode.Bounds
public import Purelib.Algebra.Ring.GaussianReading.Power
public import Purelib.Algebra.Ring.GaussianReading.FiniteSum
public import Purelib.Data.Rat.SmallWidth
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Pre-observation error requests for original finite mode readings

The original root and source weight determine a retained finite coefficient
table before any Gaussian reading is selected. Its same total computes a
sufficient endpoint error request. Actual original mode entries and windows
then satisfy that request without exact multiplicative interpretation.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode.Reading

open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Algebra.Ring.GaussianReading
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat
open Purelib.Data.Nat.Choose

variable {K : Type*} [CommRing K] {weight : Weight K} {root : K} {gain : Rational} {order count : Nat}

/-- Read the original mode power's natural index in the same retained source-power horizon. -/
@[expose] def powerIndex (order : Nat) {count : Nat} (index : Fin count) : Fin (count + 1) :=
  ⟨index.val - order, Nat.lt_succ_of_le ((Nat.sub_le _ _).trans (Nat.le_of_lt index.isLt))⟩

/-- Compute one original Pascal-scaled power-error coefficient without observing a Gaussian value. -/
@[expose] def coefficient (powers : Power.Parameters weight root gain count)
    (order : Nat) (index : Fin count) : Rational :=
  if order ≤ index.val then
    (Pascal.choose index.val order : Rational) ^ 2 * (powers.table (powerIndex order index)).2
  else 0

set_option genInjectivity false in
/-- Source-fixed finite error coefficients for the same original root-mode horizon.

The original power-coefficient cache is retained once. Its same stored table
and original Pascal multipliers produce the materialized mode coefficients;
their original finite sum bounds every requested entry before observations.
-/
structure Parameters (weight : Weight K) (root : K) (gain : Rational) (order count : Nat) where
  /-- The same once-prepared original source-power coefficients. -/
  powers : Power.Parameters weight root gain count
  /-- The power cache is the original automatic source-fixed constructor. -/
  powers_eq : powers = Power.Parameters.prepare weight root gain powers.gainNonnegative count
  /-- The materialized original generalized-mode discrepancy coefficients. -/
  coefficients : Vec Rational count
  /-- Every stored coefficient consumes the same original power table and Pascal multiplier. -/
  coefficients_eq : ∀ index, coefficients index = coefficient powers order index
  /-- The once-computed sum of the same retained mode coefficients. -/
  total : Rational
  /-- The total is the original finite sum of those actual stored coefficients. -/
  total_eq : total = sumFin (fun index => coefficients index)

constructive_injectivity Parameters

namespace Parameters

/-- Materialize source-fixed original mode coefficients and their total before any observation. -/
@[expose] def prepare (weight : Weight K) (root : K) (gain : Rational) (gainNonnegative : 0 ≤ gain)
    (order count : Nat) : Parameters weight root gain order count :=
  let powers := Power.Parameters.prepare weight root gain gainNonnegative count
  let coefficients := vectorOfFn (fun index : Fin count => coefficient powers order index)
  let total := sumFin (fun index => coefficients index)
  { powers, powers_eq := rfl, coefficients, coefficients_eq := fun index => vectorOfFn_apply _ index
    total, total_eq := rfl }

variable (parameters : Parameters weight root gain order count)

/-- Every retained original mode coefficient is nonnegative. -/
theorem coefficient_nonnegative (index : Fin count) : 0 ≤ parameters.coefficients index := by
  rewrite [parameters.coefficients_eq, coefficient]
  split
  · exact Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct _)
      (parameters.powers.table_nonnegative _).2
  · exact le_refl _

/-- The retained total of the original mode coefficients is nonnegative, including an empty horizon. -/
theorem total_nonnegative : 0 ≤ parameters.total := by
  rewrite [parameters.total_eq]
  exact weight_sum_nonnegative _ parameters.coefficient_nonnegative

/-- The same retained finite total bounds every actual stored mode coefficient. -/
theorem coefficient_le_total (index : Fin count) : parameters.coefficients index ≤ parameters.total := by
  rewrite [parameters.total_eq]
  exact entry_le_sumFin _ parameters.coefficient_nonnegative index

/-- Compute a source-mode weight bound from its same cached original power table and Pascal multiplier. -/
@[expose] def weightCoefficient (index : Fin count) : Rational :=
  if order ≤ index.val then
    weight.multiplier * weight.value (Pascal.choose index.val order : K) *
      (parameters.powers.table (powerIndex order index)).1
  else 0

/-- Every cached original source-mode weight bound is nonnegative. -/
theorem weightCoefficient_nonnegative (index : Fin count) : 0 ≤ parameters.weightCoefficient index := by
  rewrite [weightCoefficient]
  split
  · exact Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct weight.multiplier_nonnegative (weight.nonnegative _))
      (parameters.powers.table_nonnegative _).1
  · exact le_refl _

/-- The same original mode weight is bounded without reconstructing its formal root power.

The original power table and source Pascal scalar are reused. The weight's
original product law supplies the bound; no homomorphism or Gaussian reading
is selected and no original root power is evaluated by this readback.
-/
theorem weight_bound (index : Fin count) : weight.value (entry root order index.val) ≤
    parameters.weightCoefficient index := by
  rewrite [weightCoefficient, entry]
  split
  · exact (weight.mul_le _ _).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (parameters.powers.weight_bound (powerIndex order index))
        (Arithmetic.mul_nonneg_direct weight.multiplier_nonnegative (weight.nonnegative _)))
  · rewrite [weight.zero]
    exact le_refl _

/-- Each original finite mode entry pays its own retained source-fixed reading discrepancy coefficient. -/
theorem entry_bound {scalar : Canonical → K} (reading : GaussianReading weight scalar)
    (gain_eq : reading.gain = gain) (index : Fin count) :
    Norm.Basic.normSq (reading.read (entry root order index.val) - entry (reading.read root) order index.val) ≤
      reading.error * parameters.coefficients index := by
  rewrite [parameters.coefficients_eq, coefficient]
  by_cases afterStartup : order ≤ index.val
  · rewrite [if_pos afterStartup, entry, if_pos afterStartup, entry, if_pos afterStartup,
      reading.read_natMul]
    have identity : (Pascal.choose index.val order : Canonical) * reading.read (root ^ (index.val - order)) -
        (Pascal.choose index.val order : Canonical) * reading.read root ^ (index.val - order) =
        (Pascal.choose index.val order : Canonical) *
          (reading.read (root ^ (index.val - order)) - reading.read root ^ (index.val - order)) := by ring1
    rewrite [identity, Norm.Basic.normSq_mul, Cast.natCast_normSq]
    have bounded := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (parameters.powers.bound reading gain_eq (powerIndex order index)) (Arithmetic.sq_nonneg_direct
        (Pascal.choose index.val order : Rational))
    exact bounded.trans_eq (by ring1)
  · rewrite [if_neg afterStartup, entry, if_neg afterStartup, entry, if_neg afterStartup,
      reading.mapZero, sub_self, Norm.Basic.normSq_zero, mul_zero]
    exact le_refl _

/-- Each retained original finite window entry pays its same source-fixed mode coefficient. -/
theorem window_bound {scalar : Canonical → K} (reading : GaussianReading weight scalar)
    (gain_eq : reading.gain = gain) (index : Fin count) :
    Norm.Basic.normSq (reading.read (window root order count index) - window (reading.read root) order count index) ≤
      reading.error * parameters.coefficients index := by
  rewrite [window_at, window_at]
  exact parameters.entry_bound reading gain_eq index

/-- The same formal coefficient and original mode pay their actual product and mode-reading errors.

The coefficient is an original ring payload, not an assumed Gaussian scalar.
Its retained source weight and the original product-error law are both paid;
the model uses its actual Gaussian reading and the same read root.
-/
theorem weighted_entry_bound {scalar : Canonical → K} (reading : GaussianReading weight scalar)
    (gain_eq : reading.gain = gain) (coefficient : K) (index : Fin count) :
    Norm.Basic.normSq (reading.read (coefficient * entry root order index.val) -
      reading.read coefficient * entry (reading.read root) order index.val) ≤
        reading.error * (2 * (weight.value coefficient * weight.value (entry root order index.val) +
          gain * weight.value coefficient * parameters.coefficients index)) := by
  have first := reading.productBound coefficient (entry root order index.val)
  have second : Norm.Basic.normSq (reading.read coefficient *
      (reading.read (entry root order index.val) - entry (reading.read root) order index.val)) ≤
      (gain * weight.value coefficient) * (reading.error * parameters.coefficients index) := by
    rewrite [Norm.Basic.normSq_mul]
    have coefficientBound := reading.gainBound coefficient
    rewrite [gain_eq] at coefficientBound
    exact Arithmetic.mul_le_mul_direct coefficientBound (parameters.entry_bound reading gain_eq index)
      (Norm.Basic.normSq_nonneg _) (Arithmetic.mul_nonneg_direct parameters.powers.gainNonnegative
        (weight.nonnegative coefficient))
  have identity : reading.read (coefficient * entry root order index.val) -
      reading.read coefficient * entry (reading.read root) order index.val =
      (reading.read (coefficient * entry root order index.val) -
        reading.read coefficient * reading.read (entry root order index.val)) +
          reading.read coefficient * (reading.read (entry root order index.val) -
            entry (reading.read root) order index.val) := by ring1
  rewrite [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct first second)
      (by decide : (0 : Rational) ≤ 2)).trans_eq (by ring1))

end Parameters

set_option genInjectivity false in
/-- A sufficient endpoint error budget computed from the same original mode parameters and positive request. -/
structure Request (parameters : Parameters weight root gain order count) (target : Rational) where
  /-- The requested mode discrepancy is positive. -/
  targetPositive : 0 < target
  /-- The original sufficient shrinking width, computed before observing a reading. -/
  width : Rational
  /-- The width consumes the same stored coefficient total and requested target. -/
  width_eq : width = SmallWidth.shrinkingWidth parameters.total target
  /-- The sufficient positive endpoint multiplication-error tolerance. -/
  tolerance : Rational
  /-- The tolerance is the square of that same retained shrinking width. -/
  tolerance_eq : tolerance = width ^ 2

constructive_injectivity Request

namespace Request

/-- Compute a sufficient original endpoint tolerance before selecting observations or residuals. -/
@[expose] def prepare (parameters : Parameters weight root gain order count) (target : Rational)
    (targetPositive : 0 < target) : Request parameters target :=
  let width := SmallWidth.shrinkingWidth parameters.total target
  { targetPositive, width, width_eq := rfl, tolerance := width ^ 2, tolerance_eq := rfl }

variable {parameters : Parameters weight root gain order count} {target : Rational}

/-- The same computed endpoint tolerance is positive, including an empty requested horizon. -/
theorem tolerance_positive (request : Request parameters target) : 0 < request.tolerance := by
  rewrite [request.tolerance_eq, request.width_eq]
  exact Arithmetic.pow_pos_direct
    (SmallWidth.shrinkingWidth_pos parameters.total_nonnegative request.targetPositive) 2

/-- A paid actual reading makes every original finite mode entry strictly meet the same requested error. -/
theorem entry_lt (request : Request parameters target) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (paid : reading.error ≤ request.tolerance) (index : Fin count) :
    Norm.Basic.normSq (reading.read (entry root order index.val) - entry (reading.read root) order index.val) <
      target := by
  have bounded := parameters.entry_bound reading gain_eq index
  have uniform := Arithmetic.mul_le_mul_direct paid (parameters.coefficient_le_total index)
    (parameters.coefficient_nonnegative index) request.tolerance_positive.le
  have sufficient := SmallWidth.coefficient_mul_shrinkingWidth_sq_lt parameters.total_nonnegative request.targetPositive
  rewrite [← request.width_eq] at sufficient
  exact (bounded.trans uniform).trans_lt ((by
    rewrite [request.tolerance_eq]
    exact (mul_comm _ _).trans_lt sufficient) : request.tolerance * parameters.total < target)

/-- Every paid original finite window reading strictly meets the same pre-observation request. -/
theorem window_lt (request : Request parameters target) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (paid : reading.error ≤ request.tolerance) (index : Fin count) :
    Norm.Basic.normSq (reading.read (window root order count index) - window (reading.read root) order count index) <
      target := by
  rewrite [window_at, window_at]
  exact request.entry_lt reading gain_eq paid index

/-- A paid mode request and the same actual root-reading ceiling give a genuine finite inside-tail bound.

The actual formal-mode reading is compared with its original Gaussian mode
at that same read root. Both the source-fixed discrepancy budget and the
computed inside threshold are paid; no geometric label implies this premise.
-/
theorem inside_entry_lt {ceiling target : Rational} (request : Request parameters (target / 4))
    (inside : Mode.Inside ceiling order (target / 4)) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (paid : reading.error ≤ request.tolerance) (pointBound : Norm.Basic.normSq (reading.read root) ≤ ceiling)
    (index : Fin count) (later : inside.index ≤ index.val) :
    Norm.Basic.normSq (reading.read (entry root order index.val)) < target := by
  have discrepancy := request.entry_lt reading gain_eq paid index
  have model := inside.bound (reading.read root) pointBound index.val later
  have sumBound := Arithmetic.add_le_add_direct (le_refl
    (Norm.Basic.normSq (reading.read (entry root order index.val) - entry (reading.read root) order index.val))) model
  have sumLess := sumBound.trans_lt (Arithmetic.add_lt_add_right_direct discrepancy (target / 4))
  have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 2) sumLess
  have identity : reading.read (entry root order index.val) =
      (reading.read (entry root order index.val) - entry (reading.read root) order index.val) +
        entry (reading.read root) order index.val := by ring1
  calc
    _ = Norm.Basic.normSq ((reading.read (entry root order index.val) -
        entry (reading.read root) order index.val) + entry (reading.read root) order index.val) :=
      congrArg Norm.Basic.normSq identity
    _ ≤ 2 * (Norm.Basic.normSq (reading.read (entry root order index.val) -
          entry (reading.read root) order index.val) + Norm.Basic.normSq (entry (reading.read root) order index.val)) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ < 2 * (target / 4 + target / 4) := scaled
    _ = target := by
      calc
        _ = (target / 4) * 4 := by ring1
        _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)

/-- The same actual inside reading bound holds for every retained finite window coordinate after the threshold. -/
theorem inside_window_lt {ceiling target : Rational} (request : Request parameters (target / 4))
    (inside : Mode.Inside ceiling order (target / 4)) {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (paid : reading.error ≤ request.tolerance) (pointBound : Norm.Basic.normSq (reading.read root) ≤ ceiling)
    (index : Fin count) (later : inside.index ≤ index.val) :
    Norm.Basic.normSq (reading.read (window root order count index)) < target := by
  rewrite [window_at]
  exact request.inside_entry_lt inside reading gain_eq paid pointBound index later

end Request
end Purelib.Polynomial.Recurrence.Mode.Reading

end
