module
import Purelib.Data.Nat.Order
import all Purelib.Data.Nat.List.Maximum

import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.List.Map

import Purelib.Data.Rat.Fraction.Resource.Model
import Purelib.Geometry.Rational.Box.Resource
import all Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data

import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Resource
import Purelib.Polynomial.Dense.Rational.Resource.Magnitude
import Purelib.Polynomial.Dense.Resource
import Purelib.Polynomial.Elimination.Separated.Resource.Data
import Purelib.Polynomial.Winding.Box.Resource
public import Purelib.RootIsolation.Resource.Basic
import Purelib.RootIsolation.Resource.Budget
import Purelib.RootIsolation.Resource.Input
import Purelib.RootIsolation.Subdivision.Raw.Resource
import Purelib.RootIsolation.Subdivision.Raw.Resource.Winding
import Purelib.Tactic.QuotientFreeOmega

open Purelib.RootIsolation

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Build

/-- Certify the stated operation and magnitude budgets for the original finite raw-isolation input.

The proof combines retained vertical and horizontal eliminant data, denominator clearing, box refinement and the actual
inspected winding boxes, with their exact resulting bit budget. -/
theorem stageThree_resource_certificate (input :
  Resource.Input.StageThreeInput) :
    Resource.Basic.StageThreeResourcesWithin input (Resource.Budget.stageThreeStepBudget input)
      (Resource.Budget.stageThreeBitBudget input) := open Purelib in open Purelib.Data.Rat in open
        Purelib.Geometry.Rational in open Purelib.LinearAlgebra in open Purelib.Polynomial in by
  have verticalLe :
      Elimination.Separated.Resource.Data.separatedDataMagnitudeEnvelope
          input.polynomial ≤ Resource.Budget.stageThreeMagnitudeBudget input :=
    (Purelib.Data.Nat.Order.le_max_left _ _).trans (Purelib.Data.Nat.Order.le_max_left _ _)
  have horizontalLe :
      Elimination.Separated.Resource.Data.separatedDataMagnitudeEnvelope
          input.horizontalPolynomial ≤ Resource.Budget.stageThreeMagnitudeBudget input :=
    ((Purelib.Data.Nat.Order.le_max_left _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _)).trans
      (Purelib.Data.Nat.Order.le_max_left _ _)
  have clearingLe :
      Dense.Gaussian.Denominator.Clearing.Resource.clearedCoefficientMagnitudeEnvelope
          input.polynomial.normalize.coeffs ≤ Resource.Budget.stageThreeMagnitudeBudget input :=
    ((Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_left _ _).trans
      ((Purelib.Data.Nat.Order.le_max_right _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _)))).trans
        (Purelib.Data.Nat.Order.le_max_left _ _)
  have denominatorProductLe :
      Dense.Gaussian.Denominator.Clearing.Resource.coefficientDenominatorProduct
          input.polynomial.normalize.coeffs ≤ Resource.Budget.stageThreeMagnitudeBudget input :=
    ((Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_left _ _).trans
      ((Purelib.Data.Nat.Order.le_max_right _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _)))).trans
        (Purelib.Data.Nat.Order.le_max_left _ _)
  have refinementLe :
      Subdivision.Raw.Resource.refinementMagnitudeEnvelope
          input.degreeBound
          (Box.Resource.boxMagnitude input.state.box)
          input.depth ≤ Resource.Budget.stageThreeMagnitudeBudget input :=
    ((Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans
      ((Purelib.Data.Nat.Order.le_max_right _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _)))).trans
        (Purelib.Data.Nat.Order.le_max_left _ _)
  have windingLe : Subdivision.Raw.Resource.Winding.refinementWindingMagnitudeBudget input.elimination
      input.state input.depth ≤ Resource.Budget.stageThreeMagnitudeBudget input :=
    ((Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans
      ((Purelib.Data.Nat.Order.le_max_right _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _)))).trans
        (Purelib.Data.Nat.Order.le_max_left _ _)
  have safeCoefficientLe : Resource.Budget.safeEvaluationCoefficientMagnitude input ≤
      Resource.Budget.safeEvaluationMagnitudeBudget input := by
    exact (Purelib.Data.Nat.Order.le_max_left _ _).trans (Algebra.Field.Resource.Magnitude.bound_le_grow
      Fraction.Resource.Model.rationalModel _ _)
  have safeEvaluationLe : Resource.Budget.safeEvaluationMagnitudeBudget input ≤
      Resource.Budget.stageThreeMagnitudeBudget input := Purelib.Data.Nat.Order.le_max_right _ _
  refine
    { coefficientClearingSteps := ?_
      verticalEliminantSteps := ?_
      horizontalEliminantSteps := ?_
      searchCalls := ?_
      safeCutSteps := ?_
      windingSteps := ?_
      verticalElimination := Dense.Resource.polynomialWithin_mono Fraction.Resource.Model.rationalModel
        (Dense.Rational.Resource.Magnitude.polynomial_within_coefficientMagnitude
          (id
            input.elimination.vertical))
        ((Purelib.Data.Nat.Order.le_max_left _ _).trans (safeCoefficientLe.trans safeEvaluationLe))
      horizontalElimination := Dense.Resource.polynomialWithin_mono Fraction.Resource.Model.rationalModel
        (Dense.Rational.Resource.Magnitude.polynomial_within_coefficientMagnitude
          (id
            input.elimination.horizontal))
        ((Purelib.Data.Nat.Order.le_max_right _ _).trans (safeCoefficientLe.trans safeEvaluationLe))
      safeEvaluationEnvelope := safeEvaluationLe
      verticalBezout :=
        Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.dataWithin_mono
        (Elimination.Separated.Resource.Data.normalizedSeparatedData_within
          input.polynomial) verticalLe
      horizontalBezout :=
        Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.dataWithin_mono
        (Elimination.Separated.Resource.Data.normalizedSeparatedData_within
          input.horizontalPolynomial) horizontalLe
      coefficientScale := ?_
      clearedCoefficients := ?_
      refinedBox := ?_
      windingBoxes := ?_
      bitBudget := rfl }
  · unfold Resource.Budget.stageThreeStepBudget
    omega
  · unfold Resource.Budget.stageThreeStepBudget
    omega
  · unfold Resource.Budget.stageThreeStepBudget
    omega
  · unfold Resource.Budget.stageThreeStepBudget
    omega
  · unfold Resource.Budget.stageThreeStepBudget
    omega
  · unfold Resource.Budget.stageThreeStepBudget
    omega
  · exact (Dense.Gaussian.Denominator.Clearing.Resource.lcmScale_le_denominatorProduct
      input.polynomial.normalize.coeffs).trans denominatorProductLe
  · intro coefficient member
    exact (Dense.Gaussian.Denominator.Clearing.Resource.scaledGaussianCoefficient_component_le
      input.polynomial.normalize.coeffs coefficient member).trans clearingLe
  · have resource := Subdivision.Raw.Resource.refineTo_box_within
      input.elimination input.state input.threshold
    exact ⟨resource.1.trans refinementLe,
      resource.2.1.trans refinementLe,
      resource.2.2.1.trans refinementLe,
      resource.2.2.2.trans refinementLe⟩
  · intro box member
    have budgetMember : Winding.Box.Resource.boxWindingMagnitudeBudget input.polynomial box ∈
        (Subdivision.Raw.Resource.Winding.refinementWindingBoxes input.elimination input.state input.depth).map
          (Winding.Box.Resource.boxWindingMagnitudeBudget input.polynomial) := by
      exact Data.List.Map.mem_map.mpr ⟨box, member, rfl⟩
    have boxLe := (Purelib.Data.Nat.List.Maximum.member_le_listMaximum _ _
      budgetMember).trans windingLe
    let resource := Winding.Box.Resource.boxWinding_resource input.polynomial box
    intro edge edgeMember
    let edgeResource := resource edge edgeMember
    exact
      { chainMember := edgeResource.chainMember
        startEnvelope := edgeResource.startEnvelope.trans boxLe
        stopEnvelope := edgeResource.stopEnvelope.trans boxLe
        erasesToHeadline := edgeResource.erasesToHeadline }

end Purelib.RootIsolation.Resource.Build

end
