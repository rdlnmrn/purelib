import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Winding.Affine
import RFAP.Rational.Sites
import RFAP.Rational.FunctionArgumentPrinciple

/-!
# Executable RFAP examples

These small displayed dense polynomials exercise both public branches.  The
first quotient has two coprime squarefree numerator zeros and one coprime
squarefree denominator pole.  The second has one repeated numerator factor;
its finite rational box has ordinary winding two rather than one.
-/

namespace RFAP.RationalFunctionExamples

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box

open RFAP.ComputablePolynomial.DensePolynomial

def zeroAt (point : Gaussian) : GaussianPolynomial :=
  RFAP.AffineWinding.translatedCoordinate point

def squarefreeNumerator : GaussianPolynomial :=
  zeroAt 0

def squarefreeDenominator : GaussianPolynomial :=
  zeroAt 1

theorem squarefreeNumerator_nonzero :
    squarefreeNumerator.isZero = false := by decide

theorem squarefreeDenominator_nonzero :
    squarefreeDenominator.isZero = false := by decide

theorem zeroAt_derivative (point : Gaussian) :
    RFAP.ConstructiveGCD.derivative (zeroAt point) = constant 1 := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp [RFAP.ConstructiveGCD.derivative, RFAP.ComputableDerivative.derivative,
    RFAP.ComputableDerivative.derivativeState,
    RFAP.ComputableDerivative.derivativeStep, zeroAt,
    RFAP.AffineWinding.translatedCoordinate,
    RFAP.ComputablePolynomial.DensePolynomial.zero_add_normalize]

theorem zeroAt_nonzero (point : Gaussian) :
    (zeroAt point).isZero = false := by
  change (⟨[1, -point]⟩ : GaussianPolynomial).isZero = false
  rw [isZero, normalize_linear_of_leading_ne_zero one_ne_zero]
  rfl

def zeroAtSquarefree (point : Gaussian) :
    RFAP.Squarefree.SquarefreeCertificate (zeroAt point) := by
  change RFAP.Squarefree.CoprimeCertificate (zeroAt point)
    (RFAP.ConstructiveGCD.derivative (zeroAt point))
  rw [zeroAt_derivative]
  exact RFAP.SquarefreeFactors.CoprimeCertificate.constantRight
    (zeroAt_nonzero point)

/-- The identity `1 = Z - (Z - 1)` is the complete finite cross-coprimality
certificate for the displayed example. -/
def squarefreeCoprime :
    RFAP.Squarefree.CoprimeCertificate squarefreeNumerator
      squarefreeDenominator := by
  apply RFAP.SquarefreeFactors.coprimeCertificateOfIdentity
    squarefreeNumerator squarefreeDenominator
    (Or.inl squarefreeNumerator_nonzero) (constant 1) (constant (-1))
  intro point
  simp only [eval_constant, squarefreeNumerator, squarefreeDenominator,
    zeroAt, RFAP.AffineWinding.translatedCoordinate_eval]
  change 1 = 1 * (point - 0) + -1 * (point - 1)
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.neg_im,
      RFAP.ConstructiveGaussian.Gaussian.zero_re,
      RFAP.ConstructiveGaussian.Gaussian.zero_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im] <;> ring1

def squarefreeNumeratorInput :
    RFAP.RationalFunctionArgumentPrinciple.SquarefreeSideInput
      squarefreeNumerator squarefreeDenominator where
  sourceSquarefree := zeroAtSquarefree 0
  sourceNonzero := squarefreeNumerator_nonzero
  oppositeNonzero := squarefreeDenominator_nonzero
  sourceOppositeCoprime := squarefreeCoprime

def squarefreeDenominatorInput :
    RFAP.RationalFunctionArgumentPrinciple.SquarefreeSideInput
      squarefreeDenominator squarefreeNumerator where
  sourceSquarefree := zeroAtSquarefree 1
  sourceNonzero := squarefreeDenominator_nonzero
  oppositeNonzero := squarefreeNumerator_nonzero
  sourceOppositeCoprime :=
    RFAP.SquarefreeFactors.CoprimeCertificate.symm
      squarefreeCoprime

def squarefreeNumeratorSites :=
  RFAP.RationalFunctionArgumentPrinciple.proveSquarefreeSide
    squarefreeNumeratorInput

def squarefreeDenominatorSites :=
  RFAP.RationalFunctionArgumentPrinciple.proveSquarefreeSide
    squarefreeDenominatorInput

def squarefreeJointSeparation :
    RFAP.RationalFunctionArgumentPrinciple.SquarefreeObservationsSeparated
      squarefreeNumeratorSites.observation
      squarefreeDenominatorSites.observation :=
  RFAP.RationalFunctionArgumentPrinciple.separateSquarefreeObservations
    squarefreeNumeratorSites.observation
    squarefreeDenominatorSites.observation squarefreeCoprime

/-- Fully executable general signed-site construction for the coprime
squarefree example. -/
def squarefreeResult :=
  RFAP.RationalSites.prove squarefreeNumerator
    squarefreeDenominator squarefreeDenominator_nonzero

def repeatedNumerator : GaussianPolynomial :=
  zeroAt 1 * zeroAt 1

def repeatedDenominator : GaussianPolynomial := constant 1

def repeatedBox : Box :=
  RFAP.Boxes.Box.symmetric 2 (by decide)

/-- A concrete repeated factor exhibits winding magnitude greater than one. -/
theorem repeatedFactor_boxWinding :
    RFAP.RationalWinding.rationalBoxWinding
      repeatedNumerator repeatedDenominator repeatedBox = 2 := by
  have proper : repeatedBox.Proper := by
    change (-2 : RFAP.ConstructiveFraction.Rational) < 2 ∧
      (-2 : RFAP.ConstructiveFraction.Rational) < 2
    exact ⟨by decide, by decide⟩
  have left : repeatedBox.xLower < (1 : Gaussian).re := by decide
  have right : (1 : Gaussian).re < repeatedBox.xUpper := by decide
  have below : repeatedBox.yLower < (1 : Gaussian).im := by decide
  have above : (1 : Gaussian).im < repeatedBox.yUpper := by decide
  let linearClearance :=
    RFAP.AffineWinding.translatedCoordinate_boundaryClearanceBox
      (1 : Gaussian) left right below above
  let repeatedClearance :=
    RFAP.BoxClearance.BoundaryClearance.mul
      linearClearance linearClearance
  let denominatorClearance :=
    RFAP.GlobalWinding.gaussianConstant_boundaryClearance
      (c := (1 : Gaussian)) one_ne_zero repeatedBox
  have linearWinding :
      RFAP.Winding.quadrupledBoxWinding
        (zeroAt 1) repeatedBox = 4 := by
    simpa only [zeroAt] using
      RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate
        (1 : Gaussian) left right below above
  have productWinding :=
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      (zeroAt 1) (zeroAt 1) repeatedBox proper linearClearance linearClearance
  have denominatorWinding :=
    RFAP.GlobalWinding.quadrupledBoxWinding_gaussianConstant
      (c := (1 : Gaussian)) one_ne_zero repeatedBox
  have quotientWinding :=
    RFAP.RationalWinding.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      repeatedNumerator repeatedDenominator repeatedBox proper
      repeatedClearance denominatorClearance
  apply RFAP.RationalWinding.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
  rw [quotientWinding]
  change RFAP.Winding.quadrupledBoxWinding
      (zeroAt 1 * zeroAt 1) repeatedBox -
      RFAP.Winding.quadrupledBoxWinding
        (RFAP.GlobalWinding.gaussianConstant 1) repeatedBox = 4 * 2
  rw [productWinding, linearWinding, denominatorWinding]
  ring1

/-- Fully executable multiplicity-aware site construction for the same
repeated-factor quotient. -/
def repeatedFactorResult :=
  RFAP.RationalSites.prove repeatedNumerator repeatedDenominator
    (by decide)

end RFAP.RationalFunctionExamples
