module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Normalization
import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.SmallWidth
import Purelib.Tactic.Ring

/-! # Radius requests from the actual prepared logarithmic integral -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs.Normalization

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Division
open Purelib.Approximation.Rational.Request
open Purelib.RationalFunctions.Curve.Canonical.Circle

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {jet : InfinityCoefficients.Jet curve} {origin : Owners.Point cap 0}
  {differential : OddPowerDifferential curve.polynomial} {data : Polynomials differential}
  {base : Canonical} {nonzero : base ≠ 0}
  {retained : jet.Principal data.1.val differential.scale}

/-- The quotient sensitivity computed from the same origin floor, finite pivot and actual logarithmic guard.

The original circuit has centre bound 288 and one radius-independent
positive apartness floor. The displayed expression uses only the supplied
origin certificate and pivot, so it can be computed before choosing the
circle base or constructing any of its quarter programmes.
-/
def quotientCoefficient (origin : Owners.Point cap 0) (pivot : Canonical) : Fraction.Rational :=
  (2 * (2 * (1 + 288) +
    2 * (1 + (1 / origin.certificate.apart.certificate.lowerSq) * (Norm.Basic.normSq pivot * 288)))) /
    (Integral.logarithmicLower * Integral.logarithmicLower)

/-- The retained origin floor and actual positive logarithmic floor make the fixed sensitivity nonnegative. -/
theorem quotientCoefficient_nonnegative (origin : Owners.Point cap 0) (pivot : Canonical) :
    0 ≤ quotientCoefficient origin pivot := by
  have reciprocalNonnegative : 0 ≤ 1 / origin.certificate.apart.certificate.lowerSq :=
    Fraction.Order.Field.div_nonneg_direct (by decide) origin.certificate.apart.certificate.positive.le
  have logMagnitudeNonnegative : 0 ≤ (288 : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 288) (by decide)
  have pivotNonnegative : 0 ≤ Norm.Basic.normSq pivot * 288 :=
    Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg pivot) logMagnitudeNonnegative
  have productNonnegative := Arithmetic.mul_nonneg_direct reciprocalNonnegative pivotNonnegative
  have incrementNonnegative : 0 ≤ 1 +
      (1 / origin.certificate.apart.certificate.lowerSq) * (Norm.Basic.normSq pivot * 288) :=
    (show (0 : Fraction.Rational) = 0 + 0 by decide).trans_le
      (Arithmetic.add_le_add_direct (by decide) productNonnegative)
  have numeratorNonnegative : 0 ≤ 2 * (1 +
      (1 / origin.certificate.apart.certificate.lowerSq) * (Norm.Basic.normSq pivot * 288)) :=
    Arithmetic.mul_nonneg_direct (by decide) incrementNonnegative
  have logIncrementNonnegative : 0 ≤ 1 + (288 : Fraction.Rational) :=
    (show (0 : Fraction.Rational) = 0 + 0 by decide).trans_le
      (Arithmetic.add_le_add_direct (by decide) logMagnitudeNonnegative)
  have logBoundNonnegative := Arithmetic.mul_nonneg_direct
    (show (0 : Fraction.Rational) ≤ 2 by decide) logIncrementNonnegative
  have sumNonnegative : 0 ≤ 2 * (1 + 288) + 2 * (1 +
      (1 / origin.certificate.apart.certificate.lowerSq) * (Norm.Basic.normSq pivot * 288)) :=
    (show (0 : Fraction.Rational) = 0 + 0 by decide).trans_le
      (Arithmetic.add_le_add_direct logBoundNonnegative numeratorNonnegative)
  exact Fraction.Order.Field.div_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide) sumNonnegative)
    (Arithmetic.mul_nonneg_direct Integral.logarithmicLower_positive.le
      Integral.logarithmicLower_positive.le)

/-- A positive normalization operand request computed before the actual circle base is chosen. -/
def fixedOperandTarget (origin : Owners.Point cap 0) (pivot : Canonical) (target : Fraction.Rational) :
    Fraction.Rational :=
  (SmallWidth.shrinkingWidth 2 target / 4) / (1 + quotientCoefficient origin pivot)

/-- The fixed normalization operand request is positive for a positive output tolerance. -/
theorem fixedOperandTarget_positive (origin : Owners.Point cap 0) (pivot : Canonical)
    {target : Fraction.Rational} (positive : 0 < target) :
    0 < fixedOperandTarget origin pivot target :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct (SmallWidth.shrinkingWidth_pos (by decide) positive) (by decide))
    (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
      (quotientCoefficient_nonnegative origin pivot))

/-- The actual retained principal numerator has the displayed radius-independent process magnitude bound. -/
theorem candidate_centerBound (circuit : Integral.Circuit base nonzero)
    (cached : ParameterPrimitives retained circuit) :
    (candidate (origin := origin) (circuit := circuit) cached).name.process.centerBound =
      (1 / origin.certificate.apart.certificate.lowerSq) *
        (Norm.Basic.normSq (Coefficient.coefficient cached.table.val (parameterOrder curve)) * 288) := by
  change (Norm.Basic.normSq (1 : Canonical) / origin.certificate.apart.certificate.lowerSq) *
    (Norm.Basic.normSq (Coefficient.coefficient cached.table.val (parameterOrder curve)) *
      circuit.channel.name.process.centerBound) = _
  rewrite [Integral.Circuit.centerBound, Norm.Basic.normSq_one]
  rfl

/-- The actual prepared denominator and retained principal numerator give the fixed quotient sensitivity. -/
theorem quotientComparisonCoefficient_eq (circuit : Integral.Circuit base nonzero)
    (cached : ParameterPrimitives retained circuit)
    (normalizer : { value : Division.Prepared circuit.channel // value = circuit.prepared }) :
    SampleEquivalence.quotientComparisonCoefficient
      (candidate (origin := origin) (circuit := circuit) cached) normalizer.val.denominator
      normalizer.val.apart normalizer.val.apart =
        quotientCoefficient origin (Coefficient.coefficient cached.table.val (parameterOrder curve)) := by
  rewrite [normalizer.property]
  unfold SampleEquivalence.quotientComparisonCoefficient SampleEquivalence.commonLower
  change (2 * (2 * (1 + circuit.prepared.denominator.name.process.centerBound) +
    2 * (1 + (candidate (origin := origin) (circuit := circuit) cached).name.process.centerBound))) /
    (min circuit.prepared.apart.certificate.lowerSq circuit.prepared.apart.certificate.lowerSq *
      min circuit.prepared.apart.certificate.lowerSq circuit.prepared.apart.certificate.lowerSq) = _
  rewrite [Integral.Circuit.prepared_centerBound, Integral.Circuit.prepared_lowerSq, candidate_centerBound,
    Fraction.Order.Basic.min_eq_left (Fraction.Order.Basic.le_refl Integral.logarithmicLower)]
  rfl

/-- The actual normalization request equals the request computed before choosing this circuit's radius. -/
theorem operandTarget_eq_fixed (circuit : Integral.Circuit base nonzero)
    (cached : ParameterPrimitives retained circuit)
    (normalizer : { value : Division.Prepared circuit.channel // value = circuit.prepared })
    (target : Fraction.Rational) :
    operandTarget (origin := origin) (circuit := circuit) cached normalizer target =
      fixedOperandTarget origin (Coefficient.coefficient cached.table.val (parameterOrder curve)) target := by
  rewrite [operandTarget_eq]
  change (SmallWidth.shrinkingWidth 2 target / 4) /
    (1 + SampleEquivalence.quotientComparisonCoefficient
      (candidate (origin := origin) (circuit := circuit) cached) normalizer.val.denominator
      normalizer.val.apart normalizer.val.apart) = _
  rewrite [quotientComparisonCoefficient_eq]
  rfl

variable {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}

/-- Compute a nonzero real circle base paying the collar, common setup and normalization error budgets.

The finite pivot and numerical setup radius are supplied before any circle
programme is constructed. The same positive rational minimum supplies a
strict squared-radius margin for all four requirements. The returned
subtype retains those exact payments and the original error-bound owner.
-/
def chooseBase (origin : Owners.Point cap 0)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial retained })
    (setupRadius : { value : Fraction.Rational // 0 < value })
    (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (target : Fraction.Rational) (positive : 0 < target) :
    { value : Canonical // value ≠ 0 ∧ Norm.Basic.normSq value ≤ 1 ∧
      Norm.Basic.normSq value ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2 ∧
      Norm.Basic.normSq value ≤ setupRadius.val ^ 2 ∧
      Norm.Basic.normSq value ≤ errorBounds.baseBudget
        (SmallWidth.shrinkingWidth 2
          (fixedOperandTarget origin (Coefficient.coefficient table.val (parameterOrder curve))
            (SmallWidth.shrinkingWidth 4 target)) / 16384) } := by
  let pivot := Coefficient.coefficient table.val (parameterOrder curve)
  let precision := SmallWidth.shrinkingWidth 4 target
  have precisionPositive : 0 < precision := SmallWidth.shrinkingWidth_pos (by decide) positive
  let input := fixedOperandTarget origin pivot precision
  have inputPositive : 0 < input := fixedOperandTarget_positive origin pivot precisionPositive
  let errorBudget := errorBounds.baseBudget (SmallWidth.shrinkingWidth 2 input / 16384)
  have errorPositive : 0 < errorBudget := errorBounds.baseBudget_positive
    (Fraction.Order.Field.div_pos_direct (SmallWidth.shrinkingWidth_pos (by decide) inputPositive)
      (Fraction.Cast.Order.natCast_pos_direct (n := 16384) (by decide)))
  have setupPositive : 0 < setupRadius.val ^ 2 := by
    rewrite [pow_two]
    exact Arithmetic.mul_pos_direct setupRadius.property setupRadius.property
  have collarPositive : 0 < ReciprocalExteriorCollar.innerRadius curve ^ 2 := by
    rewrite [pow_two]
    exact Arithmetic.mul_pos_direct (ReciprocalExteriorCollar.innerRadius_positive curve)
      (ReciprocalExteriorCollar.innerRadius_positive curve)
  let localBudget := Common.commonTarget (setupRadius.val ^ 2) errorBudget
  have localPositive : 0 < localBudget := Common.commonTarget_pos setupPositive errorPositive
  let collarBudget := Common.commonTarget (ReciprocalExteriorCollar.innerRadius curve ^ 2) localBudget
  have collarBudgetPositive : 0 < collarBudget := Common.commonTarget_pos collarPositive localPositive
  let budget := Common.commonTarget 1 collarBudget
  have budgetPositive : 0 < budget := Common.commonTarget_pos (by decide) collarBudgetPositive
  let width := SmallWidth.shrinkingWidth 1 budget
  have widthPositive : 0 < width := SmallWidth.shrinkingWidth_pos (by decide) budgetPositive
  let actual : Canonical := ⟨width, 0⟩
  have nonzero : actual ≠ 0 := by
    intro zero
    have realZero := congrArg (fun value : Canonical => value.re) zero
    exact widthPositive.ne' realZero
  have quadrance : Norm.Basic.normSq actual = width ^ 2 := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    change width * width + 0 * 0 = width ^ 2
    ring1
  have small : Norm.Basic.normSq actual < budget := by
    have paid := SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
      (show (0 : Fraction.Rational) ≤ 1 by decide) budgetPositive
    rewrite [Fraction.Field.one_mul] at paid
    exact quadrance.trans_lt paid
  have unit := Common.commonTarget_lt_left (by decide : (0 : Fraction.Rational) < 1) collarBudgetPositive
  have collarPaid := Common.commonTarget_lt_right (by decide : (0 : Fraction.Rational) < 1) collarBudgetPositive
  have collarBound := Common.commonTarget_lt_left collarPositive localPositive
  have localPaid := Common.commonTarget_lt_right collarPositive localPositive
  have setupPaid := Common.commonTarget_lt_left setupPositive errorPositive
  have errorPaid := Common.commonTarget_lt_right setupPositive errorPositive
  exact ⟨actual, nonzero, (small.trans unit).le, (small.trans (collarPaid.trans collarBound)).le,
    (small.trans (collarPaid.trans (localPaid.trans setupPaid))).le,
    (small.trans (collarPaid.trans (localPaid.trans errorPaid))).le⟩

/-- The chosen base pays the actual normalizer request of primitive banks built from that same retained table.

The circle is constructed after the base choice. Its actual logarithmic
preparation and the primitive builder's whole-table readback identify the
fixed request with the original normalization comparison's request. The
caller supplies neither a small-radius premise nor a new coefficient.
-/
theorem chooseBase_paid (origin : Owners.Point cap 0)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial retained })
    (setupRadius : { value : Fraction.Rational // 0 < value })
    (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (target : Fraction.Rational) (positive : 0 < target) :
    let chosen := chooseBase origin table setupRadius errorBounds target positive
    (circuit : Integral.Circuit chosen.val chosen.property.1) →
    (cached : { value : ParameterPrimitives retained circuit //
      value = ParameterPrimitives.build retained circuit table }) →
    (normalizer : { value : Division.Prepared circuit.channel // value = circuit.prepared }) →
    Norm.Basic.normSq chosen.val ≤ errorBounds.baseBudget
      (SmallWidth.shrinkingWidth 2 (operandTarget (origin := origin) (circuit := circuit) cached.val normalizer
        (SmallWidth.shrinkingWidth 4 target)) / 16384) := by
  intro chosen circuit cached normalizer
  have same : cached.val.table = table :=
    (congrArg (fun value : ParameterPrimitives retained circuit => value.table) cached.property).trans
      (ParameterPrimitives.build_table retained circuit table)
  rewrite [operandTarget_eq_fixed, same]
  exact (chooseBase origin table setupRadius errorBounds target positive).property.2.2.2.2

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs.Normalization

end
