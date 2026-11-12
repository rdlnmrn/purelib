module

import Purelib.Examples.Curves.Legendre.RegularCycle
import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Purelib.Polynomial.Dense.Power
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring

/-!
# A nonzero residual at an admitted Legendre root query

The actual continued patch at coordinate three supplies both selected sheets,
the retained initial inverse model and its original point owner. Its initial
inverse polynomial is constant, so the differential residual is eleven times
that same nonzero seed reading. The proof uses the model's stored residual
bound and scalar readbacks; it does not execute the selected root isolation or
expand a deeply refined polynomial.
-/

namespace TestPurelib.Curves.Legendre.RegularCycleResidual

open Purelib
open Purelib.Examples.Curves.Legendre.RegularCycle
open Purelib.Curves.Legendre
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

/-- The original observation center retained by the selected continued patch. -/
private def center (sheet : Fin 2) : Canonical := (patch sheet).base.site.center

/-- Both selected patches retain the displayed original coordinate three. -/
private theorem center_eq (sheet : Fin 2) : center sheet = 3 := rfl

/-- The original center lies inside the actual continued regular box. -/
private theorem center_inside (sheet : Fin 2) : (patch sheet).box.Contains (center sheet) :=
  (patch sheet).center_inside

/-- Acquire the actual selected root owner at that admitted original coordinate. -/
private def sample (sheet : Fin 2) : ContinuedNeighborhood.Point (patch sheet) (center sheet) :=
  ContinuedNeighborhood.Point.acquire (patch sheet) (center sheet) (center_inside sheet)

/-- The acquired original root owner refines the same model seed's root box. -/
private theorem sample_refines_seed (sheet : Fin 2) :
    (sample sheet).owner.track.initial.box.Refines (patch sheet).base.seed.owner.track.initial.box :=
  (sample sheet).refines

/-- Retain the original initial Newton model's differential residual and exact error caches. -/
private def residuals (sheet : Fin 2) :=
  InverseModelDifferentialResidual.DifferentialResidualBounds.build (patch sheet).base.model

/-- The original constant inverse model reads its same retained seed at the admitted point. -/
private theorem seed_readback (sheet : Fin 2) :
    (patch sheet).base.model.value.eval (center sheet) = (patch sheet).base.seed.value := by
  rewrite [(patch sheet).base.model_value_eq, DensePolynomial.eval_constant]
  rfl

/-- The original residual bound excludes a zero inverse reading at this admitted point. -/
private theorem inverse_nonzero (sheet : Fin 2) :
    (patch sheet).base.model.value.eval (center sheet) ≠ 0 := by
  intro zero
  have identity := (patch sheet).base.model.residual_eq (center sheet)
  rewrite [zero] at identity
  have scalar : (1 : Canonical) - (Paths.polynomial (2 : Canonical)).eval (center sheet) * 0 ^ 2 = 1 := by
    ring1
  have residualOne := identity.trans scalar
  have inside := (patch sheet).box_refines.contains (center_inside sheet)
  have bounded := (patch sheet).base.model.residualBound (center sheet) inside
  rewrite [residualOne, normSq_one] at bounded
  have impossible : (1 : Rational) ≤ 1 / 16 := bounded.trans (patch sheet).base.model.bound_small
  exact (by decide +kernel : ¬ ((1 : Rational) ≤ 1 / 16)) impossible

/-- The derivative of the original displayed cubic equals eleven at its admitted center. -/
private theorem polynomial_derivative (sheet : Fin 2) :
    (Derivative.derivative (Paths.polynomial (2 : Canonical))).eval (center sheet) = 11 := by
  rewrite [center_eq]
  decide +kernel

/-- The cached differential residual reads eleven times the same original inverse-model value. -/
private theorem residual_readback (sheet : Fin 2) :
    (residuals sheet).value.eval (center sheet) =
      11 * (patch sheet).base.model.value.eval (center sheet) := by
  rewrite [(residuals sheet).value_eq]
  unfold InverseModelDifferentialResidual.differentialResidual
  rewrite [(patch sheet).base.model_value_eq, Power.eval_derivative_constant,
    polynomial_derivative]
  ring1

/-- The actual initial differential residual is nonzero inside the original regular box on either selected sheet. -/
private theorem residual_nonzero (sheet : Fin 2) : (residuals sheet).value.eval (center sheet) ≠ 0 := by
  rewrite [residual_readback]
  exact mul_ne_zero (by decide +kernel : (11 : Canonical) ≠ 0) (inverse_nonzero sheet)

end TestPurelib.Curves.Legendre.RegularCycleResidual
