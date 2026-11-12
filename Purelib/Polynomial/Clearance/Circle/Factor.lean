module

public import Purelib.Polynomial.Clearance.Circle
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Geometry.Rational.Circle
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Whole-circle margins for retained polynomial factors

An original displayed coefficient factorization and one cached cofactor
majorant transfer the same source margin to the focused factor. Repeated
factor occurrences remain in the original cofactor; no squarefree hypothesis
or root-list substitution is involved.
-/

namespace Purelib.Polynomial.Clearance.Circle

open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Geometry.Rational.Circle (boundingBox inside_boundingBox)
open Dense.Gaussian
open Basic.CanonicalCoefficients (CoefficientPolynomial)
open Rat.Fraction (Rational)
open Rat.Fraction.Order

namespace FactorMargin

/-- Read a positive cofactor majorant from the same cached original Horner fold.

A singleton table is constant, so its doubled original value bound is
divided by two. Every other coefficient shape retains the original bound.
-/
@[expose] public def cofactorMajorant (cofactor : CoefficientPolynomial) (bounds : Polynomial.Bounds.Horner) :
    Rational :=
  match cofactor.coeffs with
  | [_] => max 1 (bounds.value / 2)
  | _ => max 1 bounds.value

/-- The original singleton Horner fold retains twice the coefficient quadrance. -/
private theorem singleton_value (coefficient : Gaussian.Basic.Canonical) :
    (Bounds.Box.denseHornerNormBounds ⟨[coefficient]⟩ boundingBox).value =
      2 * Gaussian.Norm.Basic.normSq coefficient := by
  change 2 * (0 * boundingBox.normSqBound + Gaussian.Norm.Basic.normSq coefficient) = _
  rewrite [Rat.Fraction.zero_mul, Rat.Fraction.zero_add]
  rfl

/-- Every raw coefficient shape gives a positive majorant from the same retained bound. -/
public theorem cofactorMajorant_pos (cofactor : CoefficientPolynomial) (bounds : Polynomial.Bounds.Horner) :
    0 < cofactorMajorant cofactor bounds := by
  unfold cofactorMajorant
  split <;> exact (show (0 : Rational) < 1 by decide).trans_le
    (Rat.Fraction.Order.Basic.le_max_left _ _)

/-- The original evaluation quadrance is bounded by the same retained cofactor majorant.

The singleton branch cancels the exact doubling in the original fold. The
general branch uses the unchanged original box-evaluation upper bound.
-/
public theorem cofactorMajorant_upper (cofactor : CoefficientPolynomial) (bounds : Polynomial.Bounds.Horner)
    (boundsEq : bounds = Bounds.Box.denseHornerNormBounds cofactor boundingBox)
    {point : Gaussian.Basic.Canonical} (inside : boundingBox.Contains point) :
    Gaussian.Norm.Basic.normSq (cofactor.eval point) ≤ cofactorMajorant cofactor bounds := by
  cases boundsEq
  cases cofactor with
  | mk coefficients =>
      cases coefficients with
      | nil => exact Bounds.Box.normSq_eval_le_denseEvalNormMajorant ⟨[]⟩ inside
      | cons coefficient coefficients =>
          cases coefficients with
          | nil =>
              change Gaussian.Norm.Basic.normSq
                ((Dense.Basic.DensePolynomial.constant coefficient).eval point) ≤ _
              rewrite [Dense.Basic.DensePolynomial.eval_constant]
              change Gaussian.Norm.Basic.normSq coefficient ≤
                max 1 ((Bounds.Box.denseHornerNormBounds ⟨[coefficient]⟩ boundingBox).value / 2)
              rewrite [singleton_value, Rat.Fraction.Field.mul_comm 2]
              rewrite [Purelib.Algebra.Field.ExplicitField.mul_div_cancel_right _ 2 (by decide)]
              exact Rat.Fraction.Order.Basic.le_max_right _ _
          | cons next coefficients =>
              exact Bounds.Box.normSq_eval_le_denseEvalNormMajorant ⟨coefficient :: next :: coefficients⟩ inside

end FactorMargin

set_option genInjectivity false in
/-- A factor margin retaining its original source certificate and coefficient factorization.

The same original cofactor table supplies one cached value/slope fold and its
positive majorant. The nominal factor certificate uses exactly that payment. -/
public structure FactorMargin {source factor cofactor : CoefficientPolynomial}
    (clearance : Certificate source)
    (factorization : Factorization.Identity.ProductIdentity source factor cofactor)
    extends Certificate factor where
  /-- The once-computed original cofactor bound on the circle's bounding box. -/ bounds : Polynomial.Bounds.Horner
  /-- The fold uses the same retained cofactor table. -/ bounds_eq :
    bounds = Bounds.Box.denseHornerNormBounds cofactor boundingBox
  /-- The positive cofactor quadrance majorant. -/ majorant : Rational
  /-- The majorant consumes this exact cached fold and the original raw coefficient shape. -/
  majorant_eq : majorant = FactorMargin.cofactorMajorant cofactor bounds
  /-- The factor margin divides the original source bound by the same retained majorant. -/ bound_eq :
    bound = clearance.bound / majorant

constructive_injectivity FactorMargin

namespace FactorMargin

/-- Transfer source clearance through the original displayed factorization and one cached cofactor fold. -/
@[expose] public def prepare {source factor cofactor : CoefficientPolynomial}
    (clearance : Certificate source)
    (factorization : Factorization.Identity.ProductIdentity source factor cofactor) :
    FactorMargin clearance factorization := by
  let bounds := Bounds.Box.denseHornerNormBounds cofactor boundingBox
  let majorant := cofactorMajorant cofactor bounds
  have majorantPositive : 0 < majorant := cofactorMajorant_pos cofactor bounds
  exact
    { bounds, bounds_eq := rfl, majorant, majorant_eq := rfl, bound_eq := rfl
      toCertificate :=
        { bound := clearance.bound / majorant
          positive := Field.div_pos_direct clearance.positive majorantPositive
          lower := by
            intro point unit
            have sourceLower := clearance.lower point unit
            rw [Factorization.Identity.eval_factorization factorization point,
              Gaussian.Norm.Basic.normSq_mul] at sourceLower
            have cofactorUpper : Gaussian.Norm.Basic.normSq (cofactor.eval point) ≤ majorant :=
              cofactorMajorant_upper cofactor bounds rfl (inside_boundingBox unit)
            apply (Field.div_le_iff_pos majorantPositive).mpr
            exact sourceLower.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct cofactorUpper
              (Gaussian.Norm.Basic.normSq_nonneg _)) } }

end FactorMargin
end Purelib.Polynomial.Clearance.Circle
