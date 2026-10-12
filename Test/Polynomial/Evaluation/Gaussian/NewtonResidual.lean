module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Evaluation.Gaussian.NewtonResidual
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Coprime.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Polynomial.Evaluation.Gaussian

@[expose] public section

/-!
# Executable regression for the canonical Newton residual

For `p(X) = X² - 2` at the displayed sample `3/2`, the finite Newton update
is `17/12` and its squared displacement is `1/144`.
-/

namespace Test.Polynomial.Evaluation.Gaussian.NewtonResidual

open scoped Purelib.Data.Nat

/-- The canonical rational three halves. -/
private def threeHalves : Fraction.Rational :=
  ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩

/-- The canonical rational seventeen twelfths. -/
private def seventeenTwelfths : Fraction.Rational :=
  ⟨17, 12, by decide, ⟨⟨5, -7, by decide⟩⟩⟩

/-- The canonical rational one one-hundred-forty-fourth. -/
private def oneOneHundredFortyFourth : Fraction.Rational :=
  ⟨1, 144, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

/-- The exact Gaussian polynomial X squared minus two. -/
private def quadratic : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 0, -2]⟩
/-- The original real Gaussian sample three halves. -/
private def sample : Data.Gaussian.Basic.Canonical := ⟨threeHalves, 0⟩
/-- The expected exact Newton center seventeen twelfths. -/
private def expectedCenter : Data.Gaussian.Basic.Canonical := ⟨seventeenTwelfths, 0⟩

section
open Test.Polynomial.Evaluation.Gaussian.NewtonResidual
/-- The exact Newton step for X squared minus two at three halves is seventeen twelfths. -/
theorem regression_newton_center :
    (let quadratic : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 0, -2]⟩
     let sample : Data.Gaussian.Basic.Canonical :=
       ⟨⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩, 0⟩
     let expectedCenter : Data.Gaussian.Basic.Canonical :=
       ⟨⟨17, 12, by decide, ⟨⟨5, -7, by decide⟩⟩⟩, 0⟩
     NewtonResidual.newtonCenter quadratic sample = expectedCenter) := by
  decide

/-- The exact Newton step has squared displacement one one-hundred-forty-fourth. -/
theorem regression_newton_displacement :
    (let quadratic : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 0, -2]⟩
     let sample : Data.Gaussian.Basic.Canonical :=
       ⟨⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩, 0⟩
     Data.Gaussian.Basic.Canonical.normSq
         (NewtonResidual.newtonCenter quadratic sample - sample) =
       (⟨1, 144, by decide, ⟨⟨1, 0, by decide⟩⟩⟩ : Fraction.Rational)) := by
  decide

/-- The displayed Newton displacement equals the original residual norm divided by the nonzero derivative norm. -/
theorem regression_newton_displacement_certificate :
    (let quadratic : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 0, -2]⟩
     let sample : Data.Gaussian.Basic.Canonical :=
       ⟨⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩, 0⟩
     Data.Gaussian.Basic.Canonical.normSq
         (NewtonResidual.newtonCenter quadratic sample - sample) =
       NewtonResidual.residualSq quadratic sample *
         (Data.Gaussian.Basic.Canonical.normSq
           (NewtonResidual.derivativeValue quadratic sample))⁻¹) := by
  change Data.Gaussian.Basic.Canonical.normSq
      (NewtonResidual.newtonCenter quadratic sample - sample) =
    NewtonResidual.residualSq quadratic sample *
      (Data.Gaussian.Basic.Canonical.normSq
        (NewtonResidual.derivativeValue quadratic sample))⁻¹
  exact NewtonResidual.newtonDisplacementSq quadratic sample (by decide)

/-- One executable Boolean used by the compiled regression runner. -/
def compiledResidualRegressionPassed : Bool :=
  let threeHalves : Fraction.Rational :=
    ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩
  let seventeenTwelfths : Fraction.Rational :=
    ⟨17, 12, by decide, ⟨⟨5, -7, by decide⟩⟩⟩
  let oneOneHundredFortyFourth : Fraction.Rational :=
    ⟨1, 144, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
  let quadratic : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 0, -2]⟩
  let sample : Data.Gaussian.Basic.Canonical := ⟨threeHalves, 0⟩
  let expectedCenter : Data.Gaussian.Basic.Canonical := ⟨seventeenTwelfths, 0⟩
  decide (NewtonResidual.newtonCenter quadratic sample = expectedCenter) &&
    decide (Data.Gaussian.Basic.Canonical.normSq
      (NewtonResidual.newtonCenter quadratic sample - sample) =
        oneOneHundredFortyFourth)

end

/-- The executable Newton center and displacement regression table passes. -/
theorem compiledResidualRegressionPassed_eq_true :
    NewtonResidual.compiledResidualRegressionPassed = true := by
  decide

end Test.Polynomial.Evaluation.Gaussian.NewtonResidual
