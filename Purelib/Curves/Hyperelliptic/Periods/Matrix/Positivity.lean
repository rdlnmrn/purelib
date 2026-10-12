module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Rational.Order
public import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Components.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Quadratic.Bounds
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.LinearAlgebra.Gaussian.QuadraticForm.Perturbation
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Rational.Budget
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian

open Purelib.LinearAlgebra.Gaussian.QuadraticForm

open Purelib.LinearAlgebra.Matrix.Rational

open Purelib.Riemann.Periods

section
public section

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

namespace Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity

/-- Rational centre matrix returned by one shared finite request. -/
@[expose] def centerMatrix {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (target : Fraction.Rational) (positive : 0 < target) : QuadraticForm.GaussianMatrix genus :=
  LinearAlgebra.Matrix.matrixOfFn fun row column =>
    data.omegaCenter target positive row column

/-- The retained center matrix reads the sampled imaginary period entry. -/
@[simp] theorem centerMatrix_apply {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (target : Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) :
    centerMatrix data target positive row column =
      data.omegaCenter target positive row column :=
  LinearAlgebra.Matrix.matrixOfFn_apply _ _ _

/-- The canonical entrywise radius matrix repeats the chosen shrinking rational radius. Sampling at its square avoids
extracting square roots. -/
@[expose] def automaticRadius {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (_data : PeriodMatrix.NormalizedPeriodData curve)
    (radius : Fraction.Rational) (_positive : 0 < radius) : Budget.RationalMatrix genus :=
  LinearAlgebra.Matrix.matrixOfFn fun _row _column => radius

/-- The canonical entry radius is the specified positive linear refinement radius. -/
@[simp] theorem automaticRadius_apply {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (radius : Fraction.Rational) (positive : 0 < radius)
    (row column : Fin genus) :
    automaticRadius data radius positive row column = radius :=
  LinearAlgebra.Matrix.matrixOfFn_apply _ _ _

/-- Every canonical entry radius is positive when the retained refinement radius is positive. -/
theorem automaticRadius_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (radius : Fraction.Rational) (positive : 0 < radius)
    (row column : Fin genus) :
    0 < automaticRadius data radius positive row column := by
  rw [automaticRadius_apply]
  exact positive

/-- Each sampled period squared radius lies below the square of its canonical entry radius. -/
theorem omegaRadiusSq_lt_automaticRadius_sq {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (radius : Fraction.Rational) (positive : 0 < radius)
    (row column : Fin genus) :
    data.omegaRadiusSq (Quadratic.Bounds.squaredRefinementTarget radius)
        (Quadratic.Bounds.squaredRefinementTarget_positive positive) row column <
      (automaticRadius data radius positive row column) ^ 2 := by
  rw [automaticRadius_apply]
  exact data.omegaRadiusSq_lt_target (Quadratic.Bounds.squaredRefinementTarget radius)
    (Quadratic.Bounds.squaredRefinementTarget_positive positive) row column

set_option genInjectivity false in
/-- A finite rational certificate sufficient to answer one pointwise positivity request. `weighted_lower` is only an
entrywise scalar inequality; the universal matrix-box conclusion is derived below by finite summation. -/
structure RequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (vector : QuadraticForm.RationalVector genus) (_nonzero : QuadraticForm.NonzeroVector vector)
    (target : Fraction.Rational) (_positive : 0 < target) where
  /-- The smaller positive target retained for this finite refinement. -/ refinementTarget : Fraction.Rational
  /-- The retained refinement target is strictly positive. -/ refinementPositive : 0 < refinementTarget
  /-- The retained refinement target is strictly below the requested target. -/ refinement_lt_target : refinementTarget
    < target
  /-- The retained strictly positive lower margin for the imaginary quadratic form. -/ epsilon : Fraction.Rational
  /-- The retained quadratic-form margin is strictly positive. -/ epsilon_positive : 0 < epsilon
  /-- The positive entrywise perturbation radii for the sampled period matrix. -/ radius : Budget.RationalMatrix genus
  /-- Every retained matrix-entry perturbation radius is strictly positive. -/ radius_positive : forall row column, 0 <
    radius row column
  /-- Each sampled entry squared radius lies strictly below the square of its retained perturbation radius. -/
    radiusSq_lt_sq : forall row column,
    data.omegaRadiusSq refinementTarget refinementPositive row column <
      (radius row column) ^ 2
  /-- The retained entrywise rational error budget for this test vector. -/ budget : Budget.RationalMatrix genus
  /-- Every retained weighted error budget is nonnegative. -/ budget_nonnegative : forall row column, 0 <= budget row
    column
  /-- Each weighted entry perturbation is bounded below by the negative retained entry budget. -/ weighted_lower :
    forall row column (delta : Fraction.Rational),
    -(radius row column) < delta -> delta < radius row column ->
      -(budget row column) <= vector row * delta * vector column
  /-- The center quadratic form exceeds the retained positive margin plus the total error budget. -/ center_margin :
    epsilon + Budget.totalBudget budget <
      QuadraticForm.imaginaryQuadraticForm vector
        (centerMatrix data refinementTarget refinementPositive)

constructive_injectivity Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity.RequestCertificate

namespace RequestCertificate

/-- The finite radius and budget checks imply the original universal box positivity contract. -/
theorem compatible_positive {genus :
  Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Periods.Matrix.Positivity.RequestCertificate data vector nonzero target
      positive)
    (candidate : QuadraticForm.GaussianMatrix genus)
    (compatible : forall row column : Fin genus,
      Data.Gaussian.Norm.Basic.normSq
          (candidate row column -
            data.omegaCenter certificate.refinementTarget
              certificate.refinementPositive row column) <=
        data.omegaRadiusSq certificate.refinementTarget
          certificate.refinementPositive row column) :
    certificate.epsilon < QuadraticForm.imaginaryQuadraticForm vector candidate := by
  let center := Curves.Hyperelliptic.Periods.Matrix.Positivity.centerMatrix data certificate.refinementTarget
    certificate.refinementPositive
  let perturbation : Fraction.Rational :=
    FiniteSum.Fin.sumFin fun row =>
      FiniteSum.Fin.sumFin fun column =>
        vector row * (candidate row column - center row column).im *
          vector column
  have perturbationLower : -Budget.totalBudget certificate.budget <= perturbation := by
    unfold Budget.totalBudget perturbation
    rw [← FiniteSum.Fin.sumFin_neg]
    apply Order.Positivity.sumFin_mono
    intro row
    rw [← FiniteSum.Fin.sumFin_neg]
    apply Order.Positivity.sumFin_mono
    intro column
    let delta := candidate row column - center row column
    have compatibleDistance :
        Data.Gaussian.Norm.Basic.normSq delta <=
          data.omegaRadiusSq certificate.refinementTarget
            certificate.refinementPositive row column := by
      simpa only [delta, center, Curves.Hyperelliptic.Periods.Matrix.Positivity.centerMatrix_apply] using
        compatible row column
    have distance : Data.Gaussian.Norm.Basic.normSq delta <
        (certificate.radius row column) ^ 2 :=
      compatibleDistance.trans_lt
        (certificate.radiusSq_lt_sq row column)
    have bounds := Components.Bounds.imaginary_bounds_of_normSq_lt_sq
      (certificate.radius_positive row column) distance
    exact certificate.weighted_lower row column delta.im bounds.1 bounds.2
  have shiftedMargin : certificate.epsilon <
      QuadraticForm.imaginaryQuadraticForm vector center -
        Budget.totalBudget certificate.budget := by
    calc
      certificate.epsilon =
          (certificate.epsilon + Budget.totalBudget certificate.budget) +
            -(Budget.totalBudget certificate.budget) := by ring1
      _ < QuadraticForm.imaginaryQuadraticForm vector center +
            -(Budget.totalBudget certificate.budget) :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct
          certificate.center_margin (-(Budget.totalBudget certificate.budget))
      _ = QuadraticForm.imaginaryQuadraticForm vector center -
            Budget.totalBudget certificate.budget := by ring1
  have perturbedLower :
      QuadraticForm.imaginaryQuadraticForm vector center - Budget.totalBudget certificate.budget <=
        QuadraticForm.imaginaryQuadraticForm vector center + perturbation := by
    simpa only [sub_eq_add_neg, add_comm] using
      add_le_add_left perturbationLower
        (QuadraticForm.imaginaryQuadraticForm vector center)
  have identity := Perturbation.imaginaryQuadraticForm_eq_center_add_perturbation
    vector candidate center
  rw [show QuadraticForm.imaginaryQuadraticForm vector candidate =
      QuadraticForm.imaginaryQuadraticForm vector center + perturbation by
        simpa only [perturbation] using identity]
  exact shiftedMargin.trans_le perturbedLower

/-- Package the derived robustness theorem as the public positivity request certificate. -/
@[expose] def
  toPositiveRequestCertificate {genus :
  Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Periods.Matrix.Positivity.RequestCertificate data vector nonzero target
      positive) :
    PeriodMatrix.PositiveRequestCertificate data vector nonzero target positive where
  refinementTarget := certificate.refinementTarget
  refinementPositive := certificate.refinementPositive
  refinement_lt_target := certificate.refinement_lt_target
  epsilon := certificate.epsilon
  epsilon_positive := certificate.epsilon_positive
  compatible_positive := certificate.compatible_positive

end RequestCertificate

set_option genInjectivity false in
/-- Minimal finite robustness input for one positivity request. All entrywise budgets and weighted perturbation bounds
are computed from the displayed rational vector and radius matrix. -/
structure RadiusCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (vector : QuadraticForm.RationalVector genus) (_nonzero : QuadraticForm.NonzeroVector vector)
    (target : Fraction.Rational) (_positive : 0 < target) where
  /-- The smaller positive target retained for this finite refinement. -/ refinementTarget : Fraction.Rational
  /-- The retained refinement target is strictly positive. -/ refinementPositive : 0 < refinementTarget
  /-- The retained refinement target is strictly below the requested target. -/ refinement_lt_target : refinementTarget
    < target
  /-- The retained strictly positive lower margin for the imaginary quadratic form. -/ epsilon : Fraction.Rational
  /-- The retained quadratic-form margin is strictly positive. -/ epsilon_positive : 0 < epsilon
  /-- The positive entrywise perturbation radii for the sampled period matrix. -/ radius : Budget.RationalMatrix genus
  /-- Every retained matrix-entry perturbation radius is strictly positive. -/ radius_positive : forall row column, 0 <
    radius row column
  /-- Each sampled entry squared radius lies strictly below the square of its retained perturbation radius. -/
    radiusSq_lt_sq : forall row column,
    data.omegaRadiusSq refinementTarget refinementPositive row column <
      (radius row column) ^ 2
  /-- The center quadratic form exceeds the retained positive margin plus the total error budget. -/ center_margin :
    epsilon + Budget.totalBudget (Budget.automaticBudget vector radius) <
      QuadraticForm.imaginaryQuadraticForm vector
        (centerMatrix data refinementTarget refinementPositive)

constructive_injectivity Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity.RadiusCertificate

namespace RadiusCertificate

/-- Expand the minimal radius certificate into the detailed finite perturbation certificate. -/
@[expose] def toRequestCertificate
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Periods.Matrix.Positivity.RadiusCertificate data vector nonzero target positive)
      :
    Curves.Hyperelliptic.Periods.Matrix.Positivity.RequestCertificate data vector nonzero target positive where
  refinementTarget := certificate.refinementTarget
  refinementPositive := certificate.refinementPositive
  refinement_lt_target := certificate.refinement_lt_target
  epsilon := certificate.epsilon
  epsilon_positive := certificate.epsilon_positive
  radius := certificate.radius
  radius_positive := certificate.radius_positive
  radiusSq_lt_sq := certificate.radiusSq_lt_sq
  budget := Budget.automaticBudget vector certificate.radius
  budget_nonnegative := Budget.automaticBudget_nonnegative vector certificate.radius
    (fun row column => (certificate.radius_positive row column).le)
  weighted_lower := Budget.automaticBudget_weighted_lower vector certificate.radius
    certificate.radius_positive
  center_margin := certificate.center_margin

end RadiusCertificate

set_option genInjectivity false in
/-- Minimal positivity input for one finite request. The caller selects a positive rational linear radius whose square
is below the public target and proves one strict rational centre margin. Sampling, entry radii, budgets, and
perturbation inequalities are then computed canonically. -/
structure MarginCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (vector : QuadraticForm.RationalVector genus) (_nonzero : QuadraticForm.NonzeroVector vector)
    (target : Fraction.Rational) (_positive : 0 < target) where
  /-- The positive linear radius whose square determines the finite refinement target. -/ refinementRadius :
    Fraction.Rational
  /-- The retained linear refinement radius is strictly positive. -/ refinementRadiusPositive : 0 < refinementRadius
  /-- The square of the retained refinement radius is below the original requested target. -/ refinementTarget_lt_target
    :
    Quadratic.Bounds.squaredRefinementTarget refinementRadius < target
  /-- The center quadratic form strictly exceeds its computed total perturbation budget. -/ center_exceeds_budget :
    Budget.totalBudget (Budget.automaticBudget vector
      (automaticRadius data refinementRadius refinementRadiusPositive)) <
      QuadraticForm.imaginaryQuadraticForm vector
        (centerMatrix data (Quadratic.Bounds.squaredRefinementTarget
          refinementRadius)
          (Quadratic.Bounds.squaredRefinementTarget_positive refinementRadiusPositive))

constructive_injectivity Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity.MarginCertificate

namespace MarginCertificate

/-- The retained entrywise rational error budget for this test vector. -/
@[expose] def budget {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Periods.Matrix.Positivity.MarginCertificate data vector nonzero target positive)
      :
    Fraction.Rational :=
  Budget.totalBudget (Budget.automaticBudget vector
    (Curves.Hyperelliptic.Periods.Matrix.Positivity.automaticRadius data certificate.refinementRadius
      certificate.refinementRadiusPositive))

/-- The displayed rational quadratic-form value at the selected finite refinement. -/
@[expose] def centerValue {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Periods.Matrix.Positivity.MarginCertificate data vector nonzero target positive)
      :
    Fraction.Rational :=
  QuadraticForm.imaginaryQuadraticForm vector
    (Curves.Hyperelliptic.Periods.Matrix.Positivity.centerMatrix data
      (Quadratic.Bounds.squaredRefinementTarget certificate.refinementRadius)
      (Quadratic.Bounds.squaredRefinementTarget_positive
        certificate.refinementRadiusPositive))

/-- The exact positive rational clearance left after subtracting every finite perturbation budget. -/
@[expose] def margin {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Periods.Matrix.Positivity.MarginCertificate data vector nonzero target positive)
      :
    Fraction.Rational :=
  certificate.centerValue - certificate.budget

/-- The difference between the center quadratic form and its computed budget is strictly positive. -/
theorem margin_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Periods.Matrix.Positivity.MarginCertificate data vector nonzero target positive)
      :
    0 < certificate.margin :=
  Fraction.Order.Arithmetic.sub_pos_direct certificate.center_exceeds_budget

/-- The retained strictly positive lower margin for the imaginary quadratic form. -/
@[expose] def epsilon {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Periods.Matrix.Positivity.MarginCertificate data vector nonzero target positive)
      :
    Fraction.Rational :=
  certificate.margin / 2

/-- The retained quadratic-form margin is strictly positive. -/
theorem epsilon_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Periods.Matrix.Positivity.MarginCertificate data vector nonzero target positive)
      :
    0 < certificate.epsilon := by
  unfold Hyperelliptic.Periods.Matrix.Positivity.MarginCertificate.epsilon
  exact Fraction.Order.Field.div_pos_direct
    certificate.margin_positive (by decide)

/-- Half the retained positive margin plus the budget remains below the center quadratic form. -/
theorem epsilon_add_budget_lt_center
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Periods.Matrix.Positivity.MarginCertificate data vector nonzero target positive)
      :
    certificate.epsilon + certificate.budget < certificate.centerValue := by
  calc
    certificate.epsilon + certificate.budget <
        certificate.margin + certificate.budget :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct
        (Purelib.Data.Rat.Fraction.Order.Field.half_lt_self certificate.margin_positive) certificate.budget
    _ = certificate.centerValue := by
      unfold Hyperelliptic.Periods.Matrix.Positivity.MarginCertificate.margin
        budget
        centerValue
      ring1

/-- Expand the centre-margin witness into the canonical positive radii and the detailed finite robustness certificate.
-/
@[expose] def toRadiusCertificate {genus
  : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve}
    {vector : QuadraticForm.RationalVector genus} {nonzero : QuadraticForm.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Periods.Matrix.Positivity.MarginCertificate data vector nonzero target positive)
      :
    Curves.Hyperelliptic.Periods.Matrix.Positivity.RadiusCertificate data vector nonzero target positive where
  refinementTarget := Quadratic.Bounds.squaredRefinementTarget certificate.refinementRadius
  refinementPositive := Quadratic.Bounds.squaredRefinementTarget_positive
    certificate.refinementRadiusPositive
  refinement_lt_target := certificate.refinementTarget_lt_target
  epsilon := certificate.epsilon
  epsilon_positive := certificate.epsilon_positive
  radius := Curves.Hyperelliptic.Periods.Matrix.Positivity.automaticRadius data certificate.refinementRadius
    certificate.refinementRadiusPositive
  radius_positive := Curves.Hyperelliptic.Periods.Matrix.Positivity.automaticRadius_positive data
    certificate.refinementRadius certificate.refinementRadiusPositive
  radiusSq_lt_sq := Curves.Hyperelliptic.Periods.Matrix.Positivity.omegaRadiusSq_lt_automaticRadius_sq data
    certificate.refinementRadius certificate.refinementRadiusPositive
  center_margin := by
    simpa only [budget,
      centerValue] using
      certificate.epsilon_add_budget_lt_center

end MarginCertificate

set_option genInjectivity false in
/-- Pointwise positivity supplied entirely through finite rational robustness checks at each request. -/
structure Certificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve) where
  /-- For each nonzero rational test vector and positive target, return the retained finite refinement and strict
    center-budget margin. -/ certify : forall (vector : QuadraticForm.RationalVector genus)
    (nonzero : QuadraticForm.NonzeroVector vector) (target : Fraction.Rational)
    (positive : 0 < target),
    MarginCertificate data vector nonzero target positive

constructive_injectivity Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity.Certificate

namespace Certificate

/-- Forget the explicit radii and budgets only after proving the public pointwise positivity contract. -/
@[expose] def toPointwisePositivity {genus :
  Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodMatrix.NormalizedPeriodData curve} (certificate :
      Curves.Hyperelliptic.Periods.Matrix.Positivity.Certificate data) :
    PeriodMatrix.PointwisePositivity data where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target
      positive).toRadiusCertificate.toRequestCertificate.toPositiveRequestCertificate

end Certificate

end Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity

end
