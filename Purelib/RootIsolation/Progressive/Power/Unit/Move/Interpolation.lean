module

public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap
public import Purelib.RootIsolation.Owner.Bridge.Interpolation
public import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Polynomial.Power.Gaussian.Perturbation
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.RootIsolation.Progressive.Power.Owner.Transport
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast

/-!
# Regularity of the original unit-move interpolation

The retained forward bridge reads the original parameter chord. Its finite
power-family squarefree certificate therefore supplies regularity at every
rational parameter of that exact bridge, including both literal endpoints.
-/

public section

namespace Purelib.RootIsolation.Progressive.Power.Unit.Move.Interpolation

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.Polynomial.Winding.Box.Rouche.Connection (OrientedRouche)
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Data.Gaussian

variable {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)

include sourceUnit targetUnit degree degreeAtLeastTwo small in
/-- The original short parameter chord never reaches zero on its retained unit interval. -/
theorem parameter_ne_zero (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    Affine.line source (target - source) time ≠ 0 := by
  intro zero
  have movement := (Affine.Segment.normSq_source_sub_line_le source target inside).trans small.liftMargin
  rewrite [zero, Basic.sub_zero, sourceUnit] at movement
  have excluded : ¬ (1 : Rational) ≤ 1 / 128 := by
    change ¬ (1 : Rational) ≤ 1 / (128 : Nat)
    rw [Purelib.Data.Rat.Fraction.Cast.natCast_eq_fromInt]
    decide
  exact excluded movement

/-- Every reading of the actual unit-move bridge is the exact original affine-parameter power polynomial.

The bridge's original endpoint casts and forward Rouché certificate are
retained. The equality holds on the complete coefficient records at every
rational parameter, including the literal endpoint branches.
-/
theorem unitMoveBridge_polynomialAt
    (index : (Frame.robustChamberFrame (Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) (time : Rational) :
    (Overlap.unitMoveBridge sourceUnit targetUnit degree degreeAtLeastTwo small index).connection.polynomialAt time =
      Power.Gaussian.rootPolynomial (Affine.line source (target - source) time) degree := by
  unfold Overlap.unitMoveBridge
  rw [OwnerBridge.cast_polynomialAt]
  change (Owner.Transport.ownerMoveRouche degree _ _).polynomialAt time = _
  by_cases zero : time = 0
  · rw [zero, OrientedRouche.at_zero, Affine.line_zero]
  by_cases one : time = 1
  · rw [one, OrientedRouche.at_one, Affine.line_one]
  · rw [OrientedRouche.polynomialAt, if_neg zero, if_neg one]
    exact (Power.Gaussian.Perturbation.polynomial_affine_eq_add_scaled_perturbation
      source target degree time).symm

/-- Build finite regularity for the polynomial of the exact original unit-move bridge at one retained parameter.

The actual chord's nonzero parameter supplies the explicit power-family
Bézout certificate. Only the original coefficient equality transports it;
no replacement bridge, owner or numerical track is constructed.
-/
def unitMoveBridge_input
    (index : (Frame.robustChamberFrame (Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    FTA.Squarefree.Input
      ((Overlap.unitMoveBridge sourceUnit targetUnit degree degreeAtLeastTwo small index).connection.polynomialAt
        time) := by
  rw [unitMoveBridge_polynomialAt]
  exact
    { squarefree := Power.Gaussian.Squarefree.squarefree
        (parameter_ne_zero sourceUnit targetUnit degree degreeAtLeastTwo small time inside) degree
      degreeAtLeastTwo := by
        rw [Power.Gaussian.rootPolynomial_degree]
        exact degreeAtLeastTwo }

end Purelib.RootIsolation.Progressive.Power.Unit.Move.Interpolation

end
