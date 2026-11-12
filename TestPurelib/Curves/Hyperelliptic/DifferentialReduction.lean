module

import Purelib.System.IO
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Reduction
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Reduction.Numerator
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Evaluation
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-! # Odd-denominator reduction in both curve-degree parities

The exact certificates below use the two squarefree polynomials `x²−1`
and `x³−x`. The bounded executable regression lowers zero through three
denominator pairs at positive, negative and zero scales. It checks the actual
cleared coefficients, ending pair counts and retained scalar, as well as the
known one-step cubic remainder and the conic's vanishing remainder.

The library's quantified proofs cover arbitrary counts, inputs and squarefree
polynomials. These bounded computations are separate execution evidence and
make no geometric or de Rham basis claim.
-/

namespace TestPurelib.Curves.Hyperelliptic.DifferentialReduction

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.OddPower
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

/-- The even-degree curve polynomial `x²−1`. -/
private def evenPolynomial : CoefficientPolynomial := ⟨[1, 0, -1]⟩

/-- The odd-degree curve polynomial `x³−x`. -/
private def oddPolynomial : CoefficientPolynomial := ⟨[1, 0, -1, 0]⟩

/-- Squarefreeness of the even-degree polynomial from a displayed Bézout identity with constant two. -/
private def evenCertificate : SquarefreeCertificate evenPolynomial :=
  Squarefree.Evaluation.ofEvalBezoutUnit evenPolynomial (by decide +kernel) 2 (by decide +kernel)
    ⟨[-2]⟩ ⟨[1, 0]⟩ (by
      intro point
      have derivative : (GCD.derivative evenPolynomial).eval point = 2 * point := by
        unfold GCD.derivative
        rewrite [Dense.Derivative.eval_derivative]
        unfold evenPolynomial Dense.Derivative.evalDerivativeCoeffs
          Dense.Derivative.evalDerivativeStep
        simp only [List.foldl_cons, List.foldl_nil]
        ring1
      rewrite [derivative]
      unfold evenPolynomial DensePolynomial.eval DensePolynomial.evalCoeffs
      simp only [List.foldl_cons, List.foldl_nil]
      ring1)

/-- Squarefreeness of the odd-degree polynomial from a displayed Bézout identity with constant two. -/
private def oddCertificate : SquarefreeCertificate oddPolynomial :=
  Squarefree.Evaluation.ofEvalBezoutUnit oddPolynomial (by decide +kernel) 2 (by decide +kernel)
    ⟨[-9, 0]⟩ ⟨[3, 0, -2]⟩ (by
      intro point
      have derivative : (GCD.derivative oddPolynomial).eval point = 3 * point * point - 1 := by
        unfold GCD.derivative
        rewrite [Dense.Derivative.eval_derivative]
        unfold oddPolynomial Dense.Derivative.evalDerivativeCoeffs
          Dense.Derivative.evalDerivativeStep
        simp only [List.foldl_cons, List.foldl_nil]
        ring1
      rewrite [derivative]
      unfold oddPolynomial DensePolynomial.eval DensePolynomial.evalCoeffs
      simp only [List.foldl_cons, List.foldl_nil]
      ring1)

/-- A nonzero constant curve exercises the exact zero remainder edge. -/
private def constantPolynomial : CoefficientPolynomial := DensePolynomial.constant 2

/-- The original constant curve and its zero derivative have a retained unit Bézout certificate. -/
private def constantCertificate : SquarefreeCertificate constantPolynomial :=
  Squarefree.Evaluation.ofEvalBezoutUnit constantPolynomial (by decide +kernel) 2 (by decide +kernel)
    (DensePolynomial.constant 1) 0 (by
      intro point
      simp only [constantPolynomial, DensePolynomial.eval_constant, GCD.derivative,
        Dense.Derivative.derivative_constant, DensePolynomial.eval_zero, -eq_self, -iff_self]
      ring1)

/-- The original even-degree numerator reduction retains one exact constant coefficient. -/
example : (Reduction.Numerator.build (Reduction.Preparation.build evenPolynomial evenCertificate)
    (OddPowerDifferential.ofCoefficients evenPolynomial ⟨[1, 0, 0]⟩ 0 1) rfl).remainder.numerator.coeffs = [1 / 2] := by
  decide +kernel

/-- The original odd-degree numerator reduction retains its exact linear remainder. -/
example : (Reduction.Numerator.build (Reduction.Preparation.build oddPolynomial oddCertificate)
    (OddPowerDifferential.ofCoefficients oddPolynomial ⟨[1, 0, 0, 0]⟩ 0 1) rfl).remainder.numerator.coeffs =
    [3 / 5, 0] := by decide +kernel

/-- A nonzero constant curve has no retained remainder coefficients. -/
example : (Reduction.Numerator.build (Reduction.Preparation.build constantPolynomial constantCertificate)
    (OddPowerDifferential.ofCoefficients constantPolynomial ⟨[1, 0, 0]⟩ 0 1) rfl).remainder.numerator.coeffs = [] := by
  decide +kernel

/-- The zero numerator stops without materializing a nonzero primitive or performing cancellations. -/
example : (Reduction.Numerator.build (Reduction.Preparation.build oddPolynomial oddCertificate)
    (OddPowerDifferential.ofCoefficients oddPolynomial 0 0 (-2)) rfl).steps = 0 := rfl

/-- The existing squarefree preparation excludes the zero curve rather than pretending its image is invertible. -/
example (certificate : SquarefreeCertificate (0 : CoefficientPolynomial)) : False :=
  Bool.noConfusion (Squarefree.Basic.polynomial_nonzero certificate)

/-- Compare two exact Gaussian values in the executable regression. -/
private def checkScalar (label : String) (expected actual : Canonical) : IO Unit :=
  if expected == actual then pure () else throw (IO.userError label)

/-- Check the actual reduction coefficients and final owner at one bounded pair count and scale. -/
private def checkChain {polynomial : CoefficientPolynomial} {certificate : SquarefreeCertificate polynomial}
    (preparation : Reduction.Preparation polynomial certificate) (pairs : Nat) (scale : Canonical) : IO Unit := do
  let input := OddPowerDifferential.ofCoefficients polynomial (DensePolynomial.constant 1) pairs scale
  let chain := Reduction.Chain.build preparation pairs input rfl
  if chain.remainder.denominatorPairs != 0 then throw (IO.userError "denominator pair count")
  if chain.specifications.length != pairs then throw (IO.userError "retained primitive count")
  checkScalar "retained original scalar" scale chain.remainder.scale
  checkScalar "complete cleared coefficient" scale
    ((chain.remainder.scale * chain.remainder.numerator.eval 2) * polynomial.eval 2 ^ pairs +
      chain.exactCoefficient 2)

  let degree := Reduction.Numerator.ofChain preparation chain
  if degree.remainder.numerator.coeffs.length > polynomial.natDegree - 1 then
    throw (IO.userError "two-stage numerator count")
  checkScalar "two-stage cleared coefficient" (scale * polynomial.eval 2)
    ((degree.remainder.scale * degree.remainder.numerator.eval 2) * polynomial.eval 2 ^ (pairs + 1) +
      (degree.specification.differential.scale * degree.specification.differential.numerator.eval 2) *
        polynomial.eval 2 ^ pairs + chain.exactCoefficient 2 * polynomial.eval 2)

/-- Check the actual degree bound and retained primitive identity at finite coefficient probes. -/
private def checkNumerator {polynomial : CoefficientPolynomial} {certificate : SquarefreeCertificate polynomial}
    (preparation : Reduction.Preparation polynomial certificate) (numerator : CoefficientPolynomial)
    (scale : Canonical) : IO Unit := do
  let input := OddPowerDifferential.ofCoefficients polynomial numerator 0 scale
  let reduced := Reduction.Numerator.build preparation input rfl
  if reduced.remainder.numerator.coeffs.length > polynomial.natDegree - 1 then
    throw (IO.userError "numerator coefficient count")
  if reduced.steps > numerator.degreeCount then throw (IO.userError "numerator cancellation count")
  checkScalar "numerator original scalar" scale reduced.remainder.scale
  for point in ([0, 2, -1] : List Canonical) do
    checkScalar "numerator cleared primitive identity" (scale * numerator.eval point * polynomial.eval point)
      (reduced.remainder.scale * reduced.remainder.numerator.eval point * polynomial.eval point +
        reduced.specification.differential.scale * reduced.specification.differential.numerator.eval point)

/-- Execute the finite parity, sign and denominator-count regressions with one retained preparation per polynomial. -/
public def run : IO Unit := do
  let even := Reduction.Preparation.build evenPolynomial evenCertificate
  let odd := Reduction.Preparation.build oddPolynomial oddCertificate
  for pairs in [0, 1, 2, 3] do
    for scale in ([1, -2, 0] : List Canonical) do
      checkChain even pairs scale
      checkChain odd pairs scale
    let input := OddPowerDifferential.ofCoefficients evenPolynomial (DensePolynomial.constant 1) pairs 1
    let conic := Reduction.Chain.build even pairs input rfl
    checkScalar "conic remainder" (if pairs == 0 then 1 else 0) (conic.remainder.numerator.eval 2)
  let cubeInput := OddPowerDifferential.ofCoefficients oddPolynomial (DensePolynomial.constant 1) 1 1
  let cube := Reduction.Chain.build odd 1 cubeInput rfl
  checkScalar "cubic selected remainder" 3 (cube.remainder.numerator.eval 2)
  let constantCurve := Reduction.Preparation.build constantPolynomial constantCertificate
  for scale in ([1, -2, 0] : List Canonical) do
    for numerator in ([0, ⟨[1]⟩, ⟨[1, 0, 0]⟩, ⟨[1, 0, 0, 0, 0]⟩] : List CoefficientPolynomial) do
      checkNumerator even numerator scale
      checkNumerator odd numerator scale
      checkNumerator constantCurve numerator scale
  System.IO.println "squarefree odd-denominator reduction: parity/count/scale checks passed"

end TestPurelib.Curves.Hyperelliptic.DifferentialReduction
