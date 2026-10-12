module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Approximation.Rational.SquareBracket.Factor
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.RootIsolation.Newton.Restart.Anchored.Budget
import Purelib.RootIsolation.Residual.Chordal.Basic
public import Purelib.RootIsolation.Residual.Chordal.Linear
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.Residual.Chordal.Basic (SquarefreeCertificate)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Constructive residual-to-chordal winding boxes

A sufficiently small polynomial residual at a displayed Gaussian rational,
together with a containing winding-one state and finite squarefree and axis
elimination certificates, constructs a nearby winding-one box and its total
shrinking track.  No completed root is selected or asserted.
-/

namespace Purelib.RootIsolation.Residual.Chordal.Adjustable

/-! ## Accuracy-parameterized finite residual-linear converse -/

/-- Positive smallness threshold for a caller-supplied rational square
factor.  The factor is explicit input; positivity is proved below under the
required hypothesis `1 < factor`. -/
def adjustableLinearResidualThreshold
    {p : CoefficientPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Canonical) (factor : Fraction.Rational) : Fraction.Rational :=
  let mu := Residual.Chordal.Linear.linearResidualScale squarefree current
  let safe := Residual.Chordal.Linear.linearReferenceRadius squarefree current sample
  min mu (mu * safe ^ 2 / factor)

/-- A strict interior sample and a rational bracket factor greater than one give a positive residual threshold. -/
theorem adjustableLinearResidualThreshold_pos
    {p : CoefficientPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Canonical) (strict : current.box.StrictContains sample)
    (factor : Fraction.Rational) (factorGreater : 1 < factor) :
    0 < adjustableLinearResidualThreshold squarefree current sample factor := by
  let mu := Residual.Chordal.Linear.linearResidualScale squarefree current
  let safe := Residual.Chordal.Linear.linearReferenceRadius squarefree current sample
  have muPositive : 0 < mu := Residual.Chordal.Linear.linearResidualScale_pos squarefree current
  have safePositive : 0 < safe :=
    Residual.Chordal.Linear.linearReferenceRadius_pos squarefree current sample strict
  exact Fraction.Order.Basic.lt_min muPositive
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct muPositive
        (Fraction.Order.Arithmetic.pow_pos_direct safePositive 2))
      ((show (0 : Fraction.Rational) < 1 by decide).trans factorGreater))

set_option genInjectivity false in
/-- Output of the residual-linear converse at a displayed requested factor. -/
structure AdjustableLinearResidualChordalResult
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Canonical) (factor : Fraction.Rational) where
  /-- The actual rational radius selected by the finite factor-controlled bracket. -/ radius : Fraction.Rational
  /-- The retained selected radius is positive. -/ radiusPositive : 0 < radius
  /-- The retained radius squared strictly exceeds the original residual divided by its positive scale. -/
    residualOverScale_lt_radiusSq :
    Data.Gaussian.Norm.Basic.normSq (p.eval sample) / Residual.Chordal.Linear.linearResidualScale squarefree current
      <
      radius ^ 2
  /-- The retained radius squared is bounded by the requested factor times the original scaled residual. -/
    radiusSq_le_factorResidualOverScale :
    radius ^ 2 <=
      factor *
        (Data.Gaussian.Norm.Basic.normSq (p.eval sample) / Residual.Chordal.Linear.linearResidualScale squarefree
          current)
  /-- The original winding-one state and track construction at the same retained radius. -/ construction :
    Residual.Chordal.Basic.ResidualChordalResult squarefree elimination current sample radius
  /-- The squared chordal distance on the retained box is bounded by eighteen times the requested factor times the
    original scaled residual. -/ chordalLinear : forall z, construction.state.box.Contains z ->
    Geometry.Projective.Chordal.Affine.affineChordalSq sample z <=
      ((18 * factor) /
        Residual.Chordal.Linear.linearResidualScale squarefree current) *
        Data.Gaussian.Norm.Basic.normSq (p.eval sample)
  /-- The retained box's squared diagonal is bounded by thirty-two times the requested factor times the original scaled
    residual. -/ diagonalLinear :
    construction.state.box.diagonalSq <=
      ((32 * factor) / Residual.Chordal.Linear.linearResidualScale squarefree current) *
        Data.Gaussian.Norm.Basic.normSq (p.eval sample)

constructive_injectivity AdjustableLinearResidualChordalResult

set_option genInjectivity false in
/-- Exact displayed zeros remain a separate finite terminal. -/
inductive AdjustableLinearResidualChordalObservation
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Canonical) (factor : Fraction.Rational) : Type where
  /-- The displayed Gaussian sample evaluates exactly to zero. -/ | exact (evaluation : p.eval sample = 0)
  /-- Retain the actual factor-controlled bracket, track and residual-linear bounds. -/ | band
      (result : AdjustableLinearResidualChordalResult squarefree elimination
        current sample factor)

constructive_injectivity AdjustableLinearResidualChordalObservation

/-- Positive-residual branch using a bounded finite bracket at the displayed
factor. -/
def ofPositiveAdjustableLinearResidual
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Canonical) (strict : current.box.StrictContains sample)
    (evaluationNonzero : p.eval sample ≠ 0)
    (factor : Fraction.Rational) (factorGreater : 1 < factor)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) <
      adjustableLinearResidualThreshold squarefree current sample factor) :
    AdjustableLinearResidualChordalResult squarefree elimination current
      sample factor := open Purelib.Algebra.Field in by
  let residual := Data.Gaussian.Norm.Basic.normSq (p.eval sample)
  let mu := Residual.Chordal.Linear.linearResidualScale squarefree current
  let safe := Residual.Chordal.Linear.linearReferenceRadius squarefree current sample
  have residualPositive : 0 < residual := Gaussian.Norm.Basic.normSq_pos evaluationNonzero
  have muPositive : 0 < mu := Residual.Chordal.Linear.linearResidualScale_pos squarefree current
  have safePositive : 0 < safe :=
    Residual.Chordal.Linear.linearReferenceRadius_pos squarefree current sample strict
  have residualLtMu : residual < mu :=
    residualSmall.trans_le (Fraction.Order.Basic.min_le_left _ _)
  let target := residual / mu
  have targetPositive : 0 < target :=
    Fraction.Order.Field.div_pos_direct residualPositive muPositive
  have targetLtOne : target < 1 := by
    apply (Fraction.Order.Field.div_lt_iff_pos muPositive).2
    simpa only [Fraction.Field.one_mul] using residualLtMu
  have factorPositive : 0 < factor :=
    (show (0 : Fraction.Rational) < 1 by decide).trans factorGreater
  let bracket := Approximation.Rational.SquareBracket.Factor.selectWithin target factor targetPositive
    targetLtOne factorGreater
  have residualLtSafeBudget :
      residual < mu * safe ^ 2 / factor :=
    residualSmall.trans_le (Fraction.Order.Basic.min_le_right _ _)
  have residualFactorLtSafeBudget :
      residual * factor < mu * safe ^ 2 :=
    (Fraction.Order.Field.lt_div_iff_pos factorPositive).1
      residualLtSafeBudget
  have factorTargetLtSafeSq : factor * target < safe ^ 2 := by
    have rearranged : factor * target = (residual * factor) / mu := by
      dsimp only [target]
      rw [ExplicitField.div_eq_mul_inv,
        ExplicitField.div_eq_mul_inv]
      ring1
    rw [rearranged]
    apply (Fraction.Order.Field.div_lt_iff_pos muPositive).2
    calc
      residual * factor < mu * safe ^ 2 := residualFactorLtSafeBudget
      _ = safe ^ 2 * mu := by ring1
  have radiusSqLtSafeSq : bracket.radius ^ 2 < safe ^ 2 :=
    bracket.square_le_factor_target.trans_lt factorTargetLtSafeSq
  have radiusLtSafe : bracket.radius < safe :=
    Data.Rat.Bounds.Square.lt_of_sq_lt_sq_of_nonneg
      safePositive.le radiusSqLtSafeSq
  have radiusIdentity :
      Newton.Restart.Anchored.Budget.anchoredRadius
          squarefree (Residual.Chordal.Basic.protectedAmbient current) sample bracket.radius =
        bracket.radius :=
    Newton.Restart.Anchored.Budget.anchoredRadius_eq_cap_of_le_reference
      squarefree (Residual.Chordal.Basic.protectedAmbient current) sample radiusLtSafe.le
  have scaleLeMargin : mu <=
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box :=
    Fraction.Order.Basic.min_le_left _ _
  have scaleLeTwiceLipschitz : mu <=
      2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box :=
    Fraction.Order.Basic.min_le_right _ _
  have residualLtScaledRadius : residual < bracket.radius ^ 2 * mu :=
    (Fraction.Order.Field.div_lt_iff_pos muPositive).1
      bracket.target_lt_square
  have residualLtSource : residual <
      Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box *
        (2 * bracket.radius ^ 2) := by
    calc
      residual < bracket.radius ^ 2 * mu := residualLtScaledRadius
      _ <= bracket.radius ^ 2 *
          (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          scaleLeTwiceLipschitz
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            bracket.radiusPositive.le 2)
      _ = Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box *
          (2 * bracket.radius ^ 2) := by ring1
  have residualLtDisplacement : residual <
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box *
        bracket.radius ^ 2 := by
    calc
      residual < bracket.radius ^ 2 * mu := residualLtScaledRadius
      _ <= bracket.radius ^ 2 *
          Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          scaleLeMargin
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            bracket.radiusPositive.le 2)
      _ = Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box *
          bracket.radius ^ 2 := by ring1
  have constructorTarget : residual <
      Residual.Chordal.Basic.residualTarget squarefree current sample bracket.radius := by
    rw [Residual.Chordal.Basic.residualTarget, Newton.Restart.Anchored.Budget.anchoredResidualTarget,
      Residual.Chordal.Basic.protectedAmbient,
      radiusIdentity]
    exact Fraction.Order.Basic.lt_min residualLtSource residualLtDisplacement
  let construction := Residual.Chordal.Basic.ofResidual degreeAtLeastTwo squarefree elimination
    current sample strict bracket.radiusPositive constructorTarget
  have chordalLinear : forall z, construction.state.box.Contains z ->
      Geometry.Projective.Chordal.Affine.affineChordalSq sample z <=
        ((18 * factor) / mu) * residual := by
    intro z inside
    calc
      Geometry.Projective.Chordal.Affine.affineChordalSq sample z <=
          18 * bracket.radius ^ 2 := construction.chordalBound z inside
      _ <= 18 * (factor * target) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          bracket.square_le_factor_target (by decide)
      _ = ((18 * factor) / mu) * residual := by
        dsimp only [target]
        calc
          18 * (factor * (residual / mu)) =
              (18 * factor) * (residual / mu) := by
            rw [Fraction.Field.mul_assoc]
          _ = ((18 * factor) / mu) * residual :=
            Purelib.Data.Rat.Fraction.Compatibility.mul_div_reassociate (18 * factor) residual mu
  have diagonalLinear : construction.state.box.diagonalSq <=
      ((32 * factor) / mu) * residual := by
    calc
      construction.state.box.diagonalSq <= 32 * bracket.radius ^ 2 :=
        construction.diagonalBound
      _ <= 32 * (factor * target) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          bracket.square_le_factor_target
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 32) (by decide)).le
      _ = ((32 * factor) / mu) * residual := by
        dsimp only [target]
        calc
          32 * (factor * (residual / mu)) =
              (32 * factor) * (residual / mu) := by
            rw [Fraction.Field.mul_assoc]
          _ = ((32 * factor) / mu) * residual :=
            Purelib.Data.Rat.Fraction.Compatibility.mul_div_reassociate (32 * factor) residual mu
  exact
    { radius := bracket.radius
      radiusPositive := bracket.radiusPositive
      residualOverScale_lt_radiusSq := by
        simpa only [residual, mu, target] using bracket.target_lt_square
      radiusSq_le_factorResidualOverScale := by
        simpa only [residual, mu, target] using
          bracket.square_le_factor_target
      construction := construction
      chordalLinear := by
        simpa only [mu, residual] using chordalLinear
      diagonalLinear := by
        simpa only [mu, residual] using diagonalLinear }

/-- Public classifier at a displayed requested factor. -/
def observeOfAdjustableLinearResidual
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Canonical) (strict : current.box.StrictContains sample)
    (factor : Fraction.Rational) (factorGreater : 1 < factor)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) <
      adjustableLinearResidualThreshold squarefree current sample factor) :
    AdjustableLinearResidualChordalObservation squarefree elimination current
      sample factor :=
  if evaluation : p.eval sample = 0 then
    .exact evaluation
  else
    .band (ofPositiveAdjustableLinearResidual degreeAtLeastTwo squarefree
      elimination current sample strict evaluation factor factorGreater
      residualSmall)

end Purelib.RootIsolation.Residual.Chordal.Adjustable

end
