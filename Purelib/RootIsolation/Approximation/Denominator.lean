module

import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Grid.Basic
import Purelib.Approximation.Rational.Grid.Basic
public import Purelib.Approximation.Rational.QuadraticTarget.Basic
import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Box.Band.Grid
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Band.Basic
public import Purelib.RootIsolation.Newton.Band.Build
public import Purelib.RootIsolation.Newton.Band.State
import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.Winding.Bounds.Residual

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Denominator-controlled root approximation

The original Newton-band extraction supplies a retained Gaussian grid fraction with
strict containment, explicit denominator height and a squared-residual certificate.
Target preparation keeps the same coefficient and selected accuracy.
-/

public section

namespace Purelib.RootIsolation.Approximation.Denominator

open Purelib.Approximation.Gaussian
open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Approximation

set_option genInjectivity false in
/-- Fully displayed output of the denominator-controlled approximation. -/
structure Output
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational) where
  /-- The original checked Newton-band extraction for the retained input state and accuracy. -/ extracted :
    Newton.Band.Basic.Output squarefree current epsilon
  /-- The actual Gaussian grid fraction selected from the original extraction center and
  radius. -/ fraction : Gaussian.Basic.Canonical.Fraction.NaturalDenominator
  /-- The retained fraction equals the original grid-fraction construction exactly. -/ fraction_eq : fraction =
    Grid.Basic.gridFraction
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p extracted.source.box)
    extracted.radius
  /-- The retained fraction lies strictly inside the original extracted band box. -/ strictlyInside :
    extracted.box.StrictContains fraction.value
  /-- The retained fraction height equals the original grid denominator squared. -/ height_eq : fraction.height =
    Rational.Grid.Basic.gridDenominator extracted.radius ^ 2
  /-- The retained fraction's squared residual meets the original Lipschitz and accuracy
  bound. -/ residual_le : Gaussian.Basic.Canonical.normSq (p.eval fraction.value) ≤
    2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * epsilon ^ 2

constructive_injectivity Output

/-- Execute Newton-band extraction and select its explicit grid fraction. -/
@[expose] def approximate
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) :
    Output degreeAtLeastTwo squarefree elimination current epsilon := by
  let extracted := Newton.Band.Build.extract degreeAtLeastTwo squarefree
    elimination current epsilonPositive
  let center := Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p extracted.source.box
  let fraction := Grid.Basic.gridFraction center extracted.radius
  have strictlyInside : extracted.box.StrictContains fraction.value := by
    exact Box.Band.Grid.gridFraction_strictly_inside extracted.radiusPositive extracted.band
  let state := Newton.Band.State.stateOfOutput extracted
  have residual :=
    Winding.Bounds.Residual.normSq_eval_le_four_lipschitz_diagonal
      (show 0 < p.natDegree by omega) state strictlyInside.contains
  have residualBound : Gaussian.Basic.Canonical.normSq (p.eval fraction.value) ≤
      2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * epsilon ^ 2 := by
    calc
      Gaussian.Basic.Canonical.normSq (p.eval fraction.value) ≤
          4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * state.box.diagonalSq := residual
      _ ≤ 4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
          ((1 / 2 : Fraction.Rational) * epsilon ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          extracted.diagonalSq_le_half
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient).le)
      _ = 2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * epsilon ^ 2 := by
        have fourHalf : (4 : Fraction.Rational) * (1 / 2) = 2 := by decide
        calc
          4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
              ((1 / 2 : Fraction.Rational) * epsilon ^ 2) =
              ((4 : Fraction.Rational) * (1 / 2)) *
                Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * epsilon ^ 2 := by ring1
          _ = 2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * epsilon ^ 2 := by
            rw [fourHalf]
  exact
    { extracted := extracted
      fraction := fraction
      fraction_eq := rfl
      strictlyInside := strictlyInside
      height_eq := Grid.Basic.gridFraction_height center extracted.radius
      residual_le := residualBound }

/-- Execute the approximation with the square-root-scaled request belonging to its checked
residual coefficient. -/
@[expose] def approximateTarget
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (target : Fraction.Rational) :
    Output degreeAtLeastTwo squarefree elimination current
      (Rational.QuadraticTarget.Basic.targetEpsilon (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient)
        target) :=
  approximate degreeAtLeastTwo squarefree elimination current
    (Rational.QuadraticTarget.Basic.targetEpsilon_pos _ target)

/-- A positive residual target bounds the original polynomial's squared residual at the
retained grid fraction. -/
theorem approximateTarget_residual_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {target : Fraction.Rational}
    (targetPositive : 0 < target) :
    Gaussian.Basic.Canonical.normSq (p.eval
      (approximateTarget degreeAtLeastTwo squarefree elimination current
        target).fraction.value) ≤ target := by
  let coefficient := 2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  have coefficientPositive : (0 : Fraction.Rational) < coefficient :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient)
  exact
    (approximateTarget degreeAtLeastTwo squarefree elimination current
      target).residual_le.trans
      (Rational.QuadraticTarget.Basic.coefficient_mul_targetEpsilon_sq_le coefficientPositive targetPositive)

end Purelib.RootIsolation.Approximation.Denominator
