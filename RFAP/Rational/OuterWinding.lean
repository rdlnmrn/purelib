import mathlib.Tactic.QuotientFreeRing
import RFAP.Winding.Global
import RFAP.Rational.Reduction
import RFAP.Rational.Winding

/-!
# Common finite outer square for a reduced rational function

The two nonzero reduced cofactors share one coefficient-computed rational
square.  Their constructive polynomial windings give the quotient's degree
difference directly, including constant and linear cofactors.
-/

namespace RFAP.RationalFunctionArgumentPrinciple

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev ReducedPair := RFAP.RationalReduction.ReducedPair

open RFAP.Winding

/-- Nonzero rational-function input after executable cancellation. -/
structure NonzeroReducedInput
    (numerator denominator : GaussianPolynomial) where
  reduction : ReducedPair numerator denominator
  numeratorReducedNonzero : reduction.numeratorReduced.isZero = false

namespace NonzeroReducedInput

theorem denominatorReducedNonzero
    {numerator denominator : GaussianPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    input.reduction.denominatorReduced.isZero = false :=
  input.reduction.denominatorReduced_nonzero

def outerRadius
    {numerator denominator : GaussianPolynomial}
    (input : NonzeroReducedInput numerator denominator) : Coordinate :=
  max
    (RFAP.GlobalWinding.denseLargeSquareRadius
      input.reduction.numeratorReduced)
    (RFAP.GlobalWinding.denseLargeSquareRadius
      input.reduction.denominatorReduced)

theorem numeratorRadius_le_outerRadius
    {numerator denominator : GaussianPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    RFAP.GlobalWinding.denseLargeSquareRadius
        input.reduction.numeratorReduced ≤ input.outerRadius :=
  le_max_left _ _

theorem denominatorRadius_le_outerRadius
    {numerator denominator : GaussianPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    RFAP.GlobalWinding.denseLargeSquareRadius
        input.reduction.denominatorReduced ≤ input.outerRadius :=
  le_max_right _ _

theorem outerRadius_pos
    {numerator denominator : GaussianPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    0 < input.outerRadius :=
  (RFAP.GlobalWinding.denseLargeSquareRadius_pos
    input.reduction.numeratorReduced).trans_le
      input.numeratorRadius_le_outerRadius

def outerBox
    {numerator denominator : GaussianPolynomial}
    (input : NonzeroReducedInput numerator denominator) : Box :=
  RFAP.Boxes.Box.symmetric input.outerRadius
    input.outerRadius_pos.le

theorem outerBox_proper
    {numerator denominator : GaussianPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    input.outerBox.Proper := by
  change -input.outerRadius < input.outerRadius ∧
    -input.outerRadius < input.outerRadius
  exact ⟨(neg_lt_zero.mpr input.outerRadius_pos).trans input.outerRadius_pos,
    (neg_lt_zero.mpr input.outerRadius_pos).trans input.outerRadius_pos⟩

def numeratorOuterClearance
    {numerator denominator : GaussianPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    RFAP.BoxClearance.BoundaryClearance
      input.reduction.numeratorReduced input.outerBox := by
  simpa only [outerBox] using
    RFAP.GlobalWinding.symmetric_boundaryClearance_of_nonzero
      input.numeratorReducedNonzero input.numeratorRadius_le_outerRadius

def denominatorOuterClearance
    {numerator denominator : GaussianPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    RFAP.BoxClearance.BoundaryClearance
      input.reduction.denominatorReduced input.outerBox := by
  simpa only [outerBox] using
    RFAP.GlobalWinding.symmetric_boundaryClearance_of_nonzero
      input.denominatorReducedNonzero input.denominatorRadius_le_outerRadius

/-- General finite outer-square RFAP law.  The degrees are those of the
reduced cofactors, so common factors contribute neither zero nor pole
winding. -/
theorem outer_rationalWinding_eq_degreeDifference
    {numerator denominator : GaussianPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    RFAP.RationalWinding.rationalQuadrupledWinding
        input.reduction.numeratorReduced input.reduction.denominatorReduced
        input.outerBox =
      (4 : Int) * input.reduction.numeratorReduced.natDegree -
        (4 : Int) * input.reduction.denominatorReduced.natDegree := by
  have quotient :=
    RFAP.RationalWinding.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      input.reduction.numeratorReduced input.reduction.denominatorReduced
      input.outerBox input.outerBox_proper input.numeratorOuterClearance
      input.denominatorOuterClearance
  have numeratorWinding :
      quadrupledBoxWinding input.reduction.numeratorReduced input.outerBox =
        (4 : Int) * input.reduction.numeratorReduced.natDegree := by
    simpa only [outerBox] using
      RFAP.GlobalWinding.quadrupledBoxWinding_symmetric_eq_degree_of_nonzero
        input.numeratorReducedNonzero input.numeratorRadius_le_outerRadius
  have denominatorWinding :
      quadrupledBoxWinding input.reduction.denominatorReduced input.outerBox =
        (4 : Int) * input.reduction.denominatorReduced.natDegree := by
    simpa only [outerBox] using
      RFAP.GlobalWinding.quadrupledBoxWinding_symmetric_eq_degree_of_nonzero
        input.denominatorReducedNonzero input.denominatorRadius_le_outerRadius
  rw [quotient, numeratorWinding, denominatorWinding]

/-- Ordinary (rather than raw quadrupled) winding on the same finite outer
square is the signed difference of the reduced degrees. -/
theorem outer_boxWinding_eq_degreeDifference
    {numerator denominator : GaussianPolynomial}
    (input : NonzeroReducedInput numerator denominator) :
    RFAP.RationalWinding.rationalBoxWinding
        input.reduction.numeratorReduced input.reduction.denominatorReduced
        input.outerBox =
      (input.reduction.numeratorReduced.natDegree : Int) -
        input.reduction.denominatorReduced.natDegree := by
  apply RFAP.RationalWinding.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
  rw [input.outer_rationalWinding_eq_degreeDifference]
  ring1

end NonzeroReducedInput

end RFAP.RationalFunctionArgumentPrinciple
