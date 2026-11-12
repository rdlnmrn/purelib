module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
public import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Parameter Taylor bounds for actual polynomial-cell integrals

Three original cells retain their independent coefficient tables and
observations. Their common physical endpoints and uniformly bounded
pointwise Taylor certificates give a finite Taylor certificate on their
actual integrals through the original dense-primitive comparison.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.ParameterVariation

open Purelib
open Purelib.Calculus.Jet
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian

/-- A uniform parameter Taylor bound on three original cell polynomials bounds their actual integral residual.

The auxiliary linear polynomial is an exact algebraic comparison object on
the same physical endpoints. It does not replace any original observation or
model. The finite primitive estimate contributes the factor two, independently
of the degrees and local allowances of the original cells.
-/
theorem integral_remainder_le (base output slope : CellModel) (increment : Canonical)
    (base_start : base.start = output.start) (base_finish : base.finish = output.finish)
    (slope_start : slope.start = output.start) (slope_finish : slope.finish = output.finish)
    (factor : Fraction.Rational)
    (bounded : ∀ parameter : Fraction.Rational, Primitive.unitInterval.Contains parameter →
      Norm.Basic.normSq
        (Evaluation.eval output.polynomial (Cast.Path.ofCoordinate parameter) -
          Evaluation.eval base.polynomial (Cast.Path.ofCoordinate parameter) -
          increment * Evaluation.eval slope.polynomial (Cast.Path.ofCoordinate parameter)) ≤
        factor * Norm.Basic.normSq increment ^ 2) :
    Norm.Basic.normSq (output.integralSample - base.integralSample - increment * slope.integralSample) ≤
      (2 * factor * Norm.Basic.normSq output.displacement) * Norm.Basic.normSq increment ^ 2 := by
  let linear := CellModel.exact output.start output.finish
    (Arithmetic.add base.polynomial (Arithmetic.scale increment slope.polynomial))
  have linear_integral : linear.integralSample = base.integralSample + increment * slope.integralSample := by
    change (output.finish - output.start) *
      Integral.definiteIntegral (Arithmetic.add base.polynomial
        (Arithmetic.scale increment slope.polynomial)) 0 1 = _
    rewrite [Integral.definiteIntegral_add, Integral.definiteIntegral_scale]
    change _ = (base.finish - base.start) * Integral.definiteIntegral base.polynomial 0 1 +
      increment * ((slope.finish - slope.start) * Integral.definiteIntegral slope.polynomial 0 1)
    rewrite [base_start, base_finish, slope_start, slope_finish]
    ring1
  have estimate := Primitive.integral_difference_le output linear rfl rfl
    (factor * Norm.Basic.normSq increment ^ 2) (by
      intro parameter inside
      change Norm.Basic.normSq (Evaluation.eval output.polynomial _ -
        Evaluation.eval (Arithmetic.add base.polynomial (Arithmetic.scale increment slope.polynomial)) _) ≤ _
      rewrite [Evaluation.eval_add, Evaluation.eval_scale]
      have residual : Evaluation.eval output.polynomial (Cast.Path.ofCoordinate parameter) -
          (Evaluation.eval base.polynomial (Cast.Path.ofCoordinate parameter) +
            increment * Evaluation.eval slope.polynomial (Cast.Path.ofCoordinate parameter)) =
          Evaluation.eval output.polynomial (Cast.Path.ofCoordinate parameter) -
            Evaluation.eval base.polynomial (Cast.Path.ofCoordinate parameter) -
            increment * Evaluation.eval slope.polynomial (Cast.Path.ofCoordinate parameter) := by ring1
      rewrite [residual]
      exact bounded parameter inside)
  rewrite [linear_integral] at estimate
  have residual : output.integralSample - (base.integralSample + increment * slope.integralSample) =
      output.integralSample - base.integralSample - increment * slope.integralSample := by ring1
  rewrite [residual] at estimate
  exact estimate.trans_eq (by ring1)

/-- Integrate independently constructed pointwise certificates on the same three original cells.

The constructor computes the integral residual and its factor. Each local
certificate must read the actual three polynomials at the same unit parameter;
only its previously established factor ceiling is supplied.
-/
def certificate (base output slope : CellModel) (increment : Canonical)
    (base_start : base.start = output.start) (base_finish : base.finish = output.finish)
    (slope_start : slope.start = output.start) (slope_finish : slope.finish = output.finish)
    (factor : Fraction.Rational) (factor_nonneg : 0 ≤ factor)
    (pointwise : (parameter : Fraction.Rational) → Primitive.unitInterval.Contains parameter →
      Quadratic.Basic.Certificate increment)
    (base_eq : ∀ parameter inside, (pointwise parameter inside).base =
      Evaluation.eval base.polynomial (Cast.Path.ofCoordinate parameter))
    (output_eq : ∀ parameter inside, (pointwise parameter inside).output =
      Evaluation.eval output.polynomial (Cast.Path.ofCoordinate parameter))
    (slope_eq : ∀ parameter inside, (pointwise parameter inside).slope =
      Evaluation.eval slope.polynomial (Cast.Path.ofCoordinate parameter))
    (factor_le : ∀ parameter inside, (pointwise parameter inside).factor ≤ factor) :
    Quadratic.Basic.Certificate increment :=
  { base := base.integralSample
    slope := slope.integralSample
    output := output.integralSample
    remainder := output.integralSample - base.integralSample - increment * slope.integralSample
    expansion := rfl
    factor := 2 * factor * Norm.Basic.normSq output.displacement
    factor_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) factor_nonneg)
      (Norm.Basic.normSq_nonneg _)
    remainder_le := by
      have bound := integral_remainder_le base output slope increment base_start base_finish slope_start slope_finish
        factor (by
          intro parameter inside
          let entry := pointwise parameter inside
          have estimate : Norm.Basic.normSq entry.remainder ≤
              entry.factor * Norm.Basic.normSq increment ^ 2 := by
            rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical]
            exact entry.remainder_le
          rewrite [← entry.expansion, base_eq parameter inside, output_eq parameter inside,
            slope_eq parameter inside] at estimate
          exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (factor_le parameter inside) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
      rewrite [Norm.Basic.normSq_eq_canonical
        (output.integralSample - base.integralSample - increment * slope.integralSample),
        Norm.Basic.normSq_eq_canonical increment] at bound
      exact bound }

/-- The constructed base is the actual original base-cell integral. -/
theorem certificate_base (base output slope : CellModel) (increment : Canonical)
    (base_start base_finish slope_start slope_finish factor factor_nonneg pointwise
      base_eq output_eq slope_eq factor_le) :
    (certificate base output slope increment base_start base_finish slope_start slope_finish factor factor_nonneg
      pointwise base_eq output_eq slope_eq factor_le).base = base.integralSample := by
  unfold certificate
  rfl

/-- The constructed output is the actual original changed-parameter cell integral. -/
theorem certificate_output (base output slope : CellModel) (increment : Canonical)
    (base_start base_finish slope_start slope_finish factor factor_nonneg pointwise
      base_eq output_eq slope_eq factor_le) :
    (certificate base output slope increment base_start base_finish slope_start slope_finish factor factor_nonneg
      pointwise base_eq output_eq slope_eq factor_le).output = output.integralSample := by
  unfold certificate
  rfl

/-- The constructed slope is the actual independently retained derivative-cell integral. -/
theorem certificate_slope (base output slope : CellModel) (increment : Canonical)
    (base_start base_finish slope_start slope_finish factor factor_nonneg pointwise
      base_eq output_eq slope_eq factor_le) :
    (certificate base output slope increment base_start base_finish slope_start slope_finish factor factor_nonneg
      pointwise base_eq output_eq slope_eq factor_le).slope = slope.integralSample := by
  unfold certificate
  rfl

/-- The integral factor is computed from the pointwise ceiling and the original physical displacement. -/
theorem certificate_factor (base output slope : CellModel) (increment : Canonical)
    (base_start base_finish slope_start slope_finish factor factor_nonneg pointwise
      base_eq output_eq slope_eq factor_le) :
    (certificate base output slope increment base_start base_finish slope_start slope_finish factor factor_nonneg
      pointwise base_eq output_eq slope_eq factor_le).factor =
        2 * factor * Norm.Basic.normSq output.displacement := by
  unfold certificate
  rfl

end Purelib.Integration.Polynomial.Gaussian.Cell.ParameterVariation
