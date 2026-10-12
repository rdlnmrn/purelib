module

import Purelib.Data.Rat.Fraction.Constants
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.SquareBracket.Dyadic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Bounds.Square
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
public import Purelib.RootIsolation.Residual.Chordal.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Approximation.Rational.SquareBracket.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.State.WindingOne.Region
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

namespace Purelib.RootIsolation.Residual.Chordal.Linear

/-- The positive coefficient scale common to the source-variation and
Newton-displacement residual budgets. -/
def linearResidualScale
    {p : CoefficientPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient) : Fraction.Rational :=
  min
    (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin
      squarefree current.box)
    (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound
      p current.box)

/-- The common derivative and source-variation residual scale is positive. -/
theorem linearResidualScale_pos
    {p : CoefficientPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient) :
    0 < linearResidualScale squarefree current := by
  exact Fraction.Order.Basic.lt_min
    (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin_pos
      squarefree current.box)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos
        p current.box))

/-- The reference radius contains all geometric, derivative, and Taylor caps.
The sharper theorem asks the actual residual to be small enough that its
dyadic scale lies strictly below this radius. -/
def linearReferenceRadius
    {p : CoefficientPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Canonical) : Fraction.Rational :=
  Newton.Restart.Anchored.Budget.anchoredRadius
    squarefree (Residual.Chordal.Basic.protectedAmbient current) sample 1

/-- A strict interior sample has a positive safe reference radius. -/
theorem linearReferenceRadius_pos
    {p : CoefficientPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Canonical) (strict : current.box.StrictContains sample) :
    0 < linearReferenceRadius squarefree current sample := by
  exact Newton.Restart.Anchored.Budget.anchoredRadius_pos
    squarefree (Residual.Chordal.Basic.protectedAmbient current) sample strict (by decide)

/-- Positive local smallness threshold for the residual-linear theorem.
The first term puts `R / mu` below one.  The second puts the factor-four
dyadic upper bracket below the complete safe reference radius. -/
def linearResidualThreshold
    {p : CoefficientPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Canonical) : Fraction.Rational :=
  let mu := linearResidualScale squarefree current
  let safe := linearReferenceRadius squarefree current sample
  min mu (mu * safe ^ 2 / 4)

/-- A strict interior sample has a positive threshold for the residual-linear construction. -/
theorem linearResidualThreshold_pos
    {p : CoefficientPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Canonical) (strict : current.box.StrictContains sample) :
    0 < linearResidualThreshold squarefree current sample := by
  let mu := linearResidualScale squarefree current
  let safe := linearReferenceRadius squarefree current sample
  have muPositive : 0 < mu := linearResidualScale_pos squarefree current
  have safePositive : 0 < safe :=
    linearReferenceRadius_pos squarefree current sample strict
  exact Fraction.Order.Basic.lt_min muPositive
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct muPositive
        (Fraction.Order.Arithmetic.pow_pos_direct safePositive 2))
      (by decide))

set_option genInjectivity false in
/-- Output of the local residual-linear converse.  The construction retains
the selected dyadic bracket in addition to the ordinary winding-one state and
track returned by `ResidualChordalResult`. -/
structure LinearResidualChordalResult
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Canonical) where
  /-- The actual positive dyadic radius selected from the scaled residual. -/ radius : Fraction.Rational
  /-- The retained selected dyadic radius is positive. -/ radiusPositive : 0 < radius
  /-- The selected radius squared strictly exceeds the original residual divided by its positive scale. -/
    residualOverScale_lt_radiusSq :
    Data.Gaussian.Norm.Basic.normSq (p.eval sample) / linearResidualScale squarefree current
      <
      radius ^ 2
  /-- The selected radius squared is at most four times the original scaled residual. -/
    radiusSq_le_fourResidualOverScale :
    radius ^ 2 <=
      4 * (Data.Gaussian.Norm.Basic.normSq (p.eval sample) / linearResidualScale squarefree
        current)
  /-- The original residual-to-track construction at the same selected radius. -/ construction :
    Residual.Chordal.Basic.ResidualChordalResult squarefree elimination current sample radius
  /-- Every point in the retained box has squared chordal distance bounded by seventy-two times the original residual
    divided by its scale. -/ chordalLinear : forall z, construction.state.box.Contains z ->
    Geometry.Projective.Chordal.Affine.affineChordalSq sample z <=
      (72 / linearResidualScale squarefree current) *
        Data.Gaussian.Norm.Basic.normSq (p.eval sample)
  /-- The retained box's squared diagonal is bounded by one hundred twenty-eight times the original residual divided by
    its scale. -/ diagonalLinear :
    construction.state.box.diagonalSq <=
      (128 / linearResidualScale squarefree current) *
        Data.Gaussian.Norm.Basic.normSq (p.eval sample)

constructive_injectivity LinearResidualChordalResult

set_option genInjectivity false in
/-- Exact displayed zeros remain a separate finite terminal; the dyadic
branch is used only when exact evaluation is nonzero. -/
inductive LinearResidualChordalObservation
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Canonical) : Type where
  /-- The displayed Gaussian sample evaluates exactly to zero. -/ | exact (evaluation : p.eval sample = 0)
  /-- Retain the original dyadic bracket, extracted track and residual-linear bounds. -/ | band
      (result : LinearResidualChordalResult squarefree elimination current
        sample)

constructive_injectivity LinearResidualChordalObservation

/-- The positive-residual branch of the sharper theorem.  A bounded dyadic
scan chooses `r` with `R / mu < r^2 <= 4 R / mu`; the explicit threshold
places `r` beneath every pre-existing Newton-band safety cap. -/
def ofPositiveLinearResidual
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Canonical) (strict : current.box.StrictContains sample)
    (evaluationNonzero : p.eval sample ≠ 0)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) <
      linearResidualThreshold squarefree current sample) :
    LinearResidualChordalResult squarefree elimination current sample := by
  let residual := Data.Gaussian.Norm.Basic.normSq (p.eval sample)
  let mu := linearResidualScale squarefree current
  let safe := linearReferenceRadius squarefree current sample
  have residualPositive : 0 < residual := Gaussian.Norm.Basic.normSq_pos evaluationNonzero
  have muPositive : 0 < mu := linearResidualScale_pos squarefree current
  have safePositive : 0 < safe :=
    linearReferenceRadius_pos squarefree current sample strict
  have residualLtMu : residual < mu := by
    exact residualSmall.trans_le (Fraction.Order.Basic.min_le_left _ _)
  let target := residual / mu
  have targetPositive : 0 < target :=
    Fraction.Order.Field.div_pos_direct residualPositive muPositive
  have targetLtOne : target < 1 := by
    apply (Fraction.Order.Field.div_lt_iff_pos muPositive).2
    simpa only [Fraction.Field.one_mul] using residualLtMu
  let bracket := Approximation.Rational.SquareBracket.Dyadic.select target targetPositive
    targetLtOne
  have residualLtSafeBudget : residual < mu * safe ^ 2 / 4 := by
    exact residualSmall.trans_le (Fraction.Order.Basic.min_le_right _ _)
  have targetLtQuarterSafe : target < safe ^ 2 / 4 := by
    apply (Fraction.Order.Field.div_lt_iff_pos muPositive).2
    calc
      residual < mu * safe ^ 2 / 4 := residualLtSafeBudget
      _ = (safe ^ 2 / 4) * mu := by
        change (mu * safe ^ 2) * (4 : Fraction.Rational)⁻¹ = (safe ^ 2 * (4 : Fraction.Rational)⁻¹) * mu
        ring1
  have fourTargetLtSafeSq : 4 * target < safe ^ 2 := by
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (show (0 : Fraction.Rational) < 4 by decide) targetLtQuarterSafe
    calc
      4 * target < 4 * (safe ^ 2 / 4) := scaled
      _ = safe ^ 2 := by
        calc
          4 * (safe ^ 2 / 4) = (safe ^ 2 / 4) * 4 := by
            exact Fraction.Field.mul_comm _ _
          _ = safe ^ 2 :=
            Fraction.Field.div_mul_cancel_of_ne _ 4 (by decide)
  have radiusSqLtSafeSq : bracket.radius ^ 2 < safe ^ 2 :=
    bracket.square_le_four_target.trans_lt fourTargetLtSafeSq
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
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin
        squarefree current.box := Fraction.Order.Basic.min_le_left _ _
  have scaleLeTwiceLipschitz : mu <=
      2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound
        p current.box := Fraction.Order.Basic.min_le_right _ _
  have residualLtScaledRadius : residual < bracket.radius ^ 2 * mu := by
    exact (Fraction.Order.Field.div_lt_iff_pos muPositive).1
      bracket.target_lt_square
  have residualLtSource : residual <
      Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box *
        (2 * bracket.radius ^ 2) := by
    calc
      residual < bracket.radius ^ 2 * mu := residualLtScaledRadius
      _ <= bracket.radius ^ 2 *
          (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound
            p current.box) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          scaleLeTwiceLipschitz
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            bracket.radiusPositive.le 2)
      _ = Dense.Gaussian.Bounds.Box.denseLipschitzBound
          p current.box * (2 * bracket.radius ^ 2) := by ring1
  have residualLtDisplacement : residual <
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin
        squarefree current.box * bracket.radius ^ 2 := by
    calc
      residual < bracket.radius ^ 2 * mu := residualLtScaledRadius
      _ <= bracket.radius ^ 2 *
          Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin
            squarefree current.box :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          scaleLeMargin
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            bracket.radiusPositive.le 2)
      _ = Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin
          squarefree current.box * bracket.radius ^ 2 := by ring1
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
        (72 / mu) * residual := by
    intro z inside
    calc
      Geometry.Projective.Chordal.Affine.affineChordalSq sample z <=
          18 * bracket.radius ^ 2 := construction.chordalBound z inside
      _ <= 18 * (4 * target) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          bracket.square_le_four_target (by decide)
      _ = (72 / mu) * residual := by
        dsimp only [target]
        calc
          18 * (4 * (residual / mu)) =
              (18 * 4) * (residual / mu) :=
            (Fraction.Field.mul_assoc _ _ _).symm
          _ = 72 * (residual / mu) := by rw [Purelib.Data.Rat.Fraction.Constants.eighteen_mul_four]
          _ = (72 / mu) * residual :=
            Purelib.Data.Rat.Fraction.Compatibility.mul_div_reassociate 72 residual mu
  have diagonalLinear : construction.state.box.diagonalSq <=
      (128 / mu) * residual := by
    calc
      construction.state.box.diagonalSq <= 32 * bracket.radius ^ 2 :=
        construction.diagonalBound
      _ <= 32 * (4 * target) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          bracket.square_le_four_target
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 32) (by decide)).le
      _ = (128 / mu) * residual := by
        dsimp only [target]
        calc
          32 * (4 * (residual / mu)) =
              (32 * 4) * (residual / mu) :=
            (Fraction.Field.mul_assoc _ _ _).symm
          _ = 128 * (residual / mu) := by rw [Purelib.Data.Rat.Fraction.Constants.thirtyTwo_mul_four]
          _ = (128 / mu) * residual :=
            Purelib.Data.Rat.Fraction.Compatibility.mul_div_reassociate 128 residual mu
  exact
    { radius := bracket.radius
      radiusPositive := bracket.radiusPositive
      residualOverScale_lt_radiusSq := by
        simpa only [residual, mu, target] using bracket.target_lt_square
      radiusSq_le_fourResidualOverScale := by
        simpa only [residual, mu, target] using
          bracket.square_le_four_target
      construction := construction
      chordalLinear := by
        simpa only [mu, residual] using chordalLinear
      diagonalLinear := by
        simpa only [mu, residual] using diagonalLinear }

/-- Public sharper classifier.  Exact finite evaluation is checked first;
only a positive displayed residual runs the bounded dyadic selector. -/
def observeOfLinearResidual
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Canonical) (strict : current.box.StrictContains sample)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) <
      linearResidualThreshold squarefree current sample) :
    LinearResidualChordalObservation squarefree elimination current sample :=
  if evaluation : p.eval sample = 0 then
    .exact evaluation
  else
    .band (ofPositiveLinearResidual degreeAtLeastTwo squarefree elimination
      current sample strict evaluation residualSmall)
end Purelib.RootIsolation.Residual.Chordal.Linear

end
