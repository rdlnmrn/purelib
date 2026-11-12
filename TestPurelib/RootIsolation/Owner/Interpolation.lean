module

import Purelib.RootIsolation.Owner.Bridge.Interpolation
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Winding.Box.Rouche.Connection (OrientedRouche RoucheConnection)
open Purelib.Geometry.Rational (Box)
open Purelib.RootIsolation.Owner.Local
open Purelib.RootIsolation.Progressive.Power.Unit.Move
open Purelib.RootIsolation.Progressive.Power
open Purelib.Data.Gaussian
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)

namespace TestPurelib.RootIsolation.Owner.Interpolation

/-- An original coefficient table with a retained leading zero. -/
def literalBase : CoefficientPolynomial := ⟨[0, 2]⟩

/-- The retained unnormalized coefficient table evaluates to its original constant. -/
theorem literalBase_eval (value : Canonical) : literalBase.eval value = 2 := by
  change (0 * value + 0) * value + 2 = 2
  rw [zero_mul, zero_add, zero_mul, zero_add]

/-- A concrete positive-dominance perturbation with an unnormalized original base. -/
def literalCertificate (box : Box) :
    OrientedRouche literalBase (literalBase + DensePolynomial.constant 1) box where
  perturbation := DensePolynomial.constant 1
  target_eq_add := rfl
  dominance :=
    { margin := 1
      positive := by decide
      lower := by
        intro value _
        rw [literalBase_eval, DensePolynomial.eval_constant]
        change (1 : Rational) ≤ 4 - 1
        decide }

/-- The original leading-zero table survives the exact zero-parameter endpoint. -/
example (box : Box) : ((literalCertificate box).polynomialAt 0).coeffs = [0, 2] := by
  rw [(literalCertificate box).at_zero]
  rfl

/-- The same exact interpolation has a genuinely different normalized interior reading. -/
example (box : Box) : ((literalCertificate box).polynomialAt (1 / 2)).coeffs = [5 / 2] := by
  change ((if (1 / 2 : Rational) = 0 then literalBase
    else if (1 / 2 : Rational) = 1 then literalBase + DensePolynomial.constant 1
    else literalBase + DensePolynomial.scale (⟨1 / 2, 0⟩ : Canonical) (DensePolynomial.constant 1))).coeffs = [5 / 2]
  rw [if_neg (by decide), if_neg (by decide)]
  decide

/-- Reversing the actual forward certificate retains its original leading-zero table at the reversed endpoint. -/
example (box : Box) :
    ((RoucheConnection.forward (literalCertificate box)).reverse.polynomialAt 1).coeffs = [0, 2] := by
  rw [RoucheConnection.reverse_at]
  change ((literalCertificate box).polynomialAt (1 - 1)).coeffs = [0, 2]
  rw [sub_self, (literalCertificate box).at_zero]
  rfl

section

variable {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Unit.Frame.robustChamberFrame (Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)

/-- Interior owners of the actual degree-generic power move retain the original source robust box. -/
example (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    ((Overlap.unitMoveBridge sourceUnit targetUnit degree degreeTwo small index).ownerAt time inside).box =
      ((Unit.Frame.robustChamberFrame (Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit degree degreeTwo).owner index).box :=
  ((Overlap.unitMoveBridge sourceUnit targetUnit degree degreeTwo small index).ownerAt_box time inside).trans
    (Overlap.unitMoveBridge_box sourceUnit targetUnit degree degreeTwo small index)

/-- The actual power-move endpoint keeps the complete target-side owner and its original clearance. -/
example :
    Transport.castOwner (Overlap.unitMoveBridge sourceUnit targetUnit degree degreeTwo small index).connection.at_one
      ((Overlap.unitMoveBridge sourceUnit targetUnit degree degreeTwo small index).ownerAt 1
        (by constructor <;> decide)) =
        (Overlap.unitMoveBridge sourceUnit targetUnit degree degreeTwo small index).rightOwner :=
  (Overlap.unitMoveBridge sourceUnit targetUnit degree degreeTwo small index).ownerAt_one _

end

end TestPurelib.RootIsolation.Owner.Interpolation
