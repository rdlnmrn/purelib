module

import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Resource
import Purelib.Data.Gaussian.Resource.List

import Purelib.Data.Gaussian.Resource.Model
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Reverse
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Resource.Components
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic
import Purelib.Polynomial.Dense.Bivariate.Resultant
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants
import Purelib.Polynomial.Dense.Gaussian.Multiplication.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Resource.List

import Purelib.Polynomial.Dense.Resource
public import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Mathlib.Algebra.GroupWithZero.Nat

open Purelib

open Purelib.Data

open Purelib.LinearAlgebra

open Purelib.Polynomial

/-!
# Magnitude envelopes for Gaussian coefficient reflection

The original source maximum, fixed reflection cost and finite coefficient fold
compute the same retained magnitude envelopes. Direct occurrence certificates
bound the actual reflected and lifted tables and their original Sylvester entries.
-/

public section

namespace Purelib.Polynomial.Elimination.Separated.Resource.Reflection

/-- Embedding a bounded scalar as a parameter polynomial preserves its magnitude bound.

The original scalar-constant constructor retains either its single coefficient
or the zero polynomial. The supplied scalar bound therefore controls the
complete original polynomial without selecting a new coefficient representation. -/
private theorem parameterConstant_within {value : Gaussian.Basic.Number} {bound : Nat}
    (valueBound : Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude value ≤ bound) :
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant value) bound := by
  unfold Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant
  split
  · exact Dense.Resource.zero_within Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
  · exact Dense.Resource.constant_within Purelib.Data.Gaussian.Resource.Model.gaussianModel valueBound

/-- Multiplication by twice the parameter fits four magnitude-growth steps.

The input polynomial, zero coefficient and twice-parameter polynomial share the supplied bound. -/
private theorem twiceShift_within {polynomial : Dense.Gaussian.NormalizedPolynomial}
    {bound : Nat}
    (zeroBound : Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0 ≤ bound)
    (twoWithin : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      Dense.Gaussian.Coefficients.Constants.SeparatedVariables.twiceParameter bound)
    (bounded : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel polynomial
      bound) :
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (Dense.Gaussian.Multiplication.Coordinate.SeparatedVariables.twiceShift polynomial)
      (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound 4) := by
  unfold Dense.Gaussian.Multiplication.Coordinate.SeparatedVariables.twiceShift
  have multiplied := Dense.Resource.mul_within Purelib.Data.Gaussian.Resource.Model.gaussianModel zeroBound
    twoWithin bounded
  simpa only [Dense.Gaussian.Coefficients.Constants.SeparatedVariables.twiceParameter, List.length_cons,
    List.length_nil,
    Nat.reduceMul] using multiplied

/-- Scan a polynomial for its maximum coefficient magnitude.

The initial maximum also covers the scalar constants zero, two and one required by reflection. -/
@[expose] def coefficientMagnitude (polynomial : Dense.Gaussian.NormalizedPolynomial) : Nat :=
  polynomial.coeffs.foldl
    (fun bound coefficient => max bound (Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude
      coefficient))
    (max (Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0)
      (max (Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude
          (Gaussian.Basic.ofGaussian 2))
        (Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude
          (Gaussian.Basic.ofGaussian 1))))

/-- Every polynomial coefficient lies within the scanned magnitude bound.

The supplied membership constructor identifies its original coefficient. That
coefficient contributes its original Gaussian magnitude to the retained maximum
fold, independently of any normalization or reflected coefficient construction. -/
theorem polynomial_within_coefficientMagnitude (polynomial : Dense.Gaussian.NormalizedPolynomial) :
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel polynomial
      (coefficientMagnitude polynomial) := by
  intro candidate member
  exact Purelib.Data.Gaussian.Resource.List.member_componentMagnitude_le_foldl_max polynomial.coeffs _ member

/-- Six magnitude-growth steps budget one coefficient-reflection round.

The original natural constant fixes the same cost assigned to each consumed
coefficient, without depending on the polynomial table or its scalar values. -/
@[expose] def reflectedRoundSteps : Nat := 6

/-- A reflection tail step fits the fixed six-step magnitude budget.

All current coefficients, the previous polynomial, zero and twice the parameter satisfy the supplied input bound. -/
private theorem reflectedTailStep_within
    {previous : Dense.Gaussian.NormalizedPolynomial} {bound : Nat}
    (zeroBound : Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0 ≤ bound)
    (twoWithin : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      Dense.Gaussian.Coefficients.Constants.SeparatedVariables.twiceParameter bound)
    (previousWithin : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      previous bound) :
    ∀ {coefficients : List Dense.Gaussian.NormalizedPolynomial},
      (∀ polynomial ∈ coefficients,
        Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel polynomial bound) →
      ∀ {output : Dense.Gaussian.NormalizedPolynomial},
        output ∈ Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedTailStep previous coefficients →
        Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel output
          (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
            reflectedRoundSteps)
  | [], _, output, member => by
      change output ∈ [-previous] at member
      have equal := Data.List.Membership.mem_singleton.mp member
      cases equal
      exact Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel
        (Dense.Resource.neg_within Purelib.Data.Gaussian.Resource.Model.gaussianModel previousWithin)
        (Algebra.Field.Resource.Magnitude.grow_mono_steps Purelib.Data.Gaussian.Resource.Model.gaussianModel
          bound (by decide : 1 ≤ 6))
  | current :: remaining, allWithin, output, member => by
      change output ∈ (Dense.Gaussian.Multiplication.Coordinate.SeparatedVariables.twiceShift current - previous) ::
        Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedTailStep current remaining at member
      rcases Data.List.Membership.mem_cons.mp member with head | tail
      · rw [head]
        have currentWithin := allWithin current (List.Mem.head remaining)
        have shifted := Purelib.Polynomial.Elimination.Separated.Resource.Reflection.twiceShift_within zeroBound
          twoWithin currentWithin
        have previousFour := Dense.Resource.polynomialWithin_mono
          Purelib.Data.Gaussian.Resource.Model.gaussianModel previousWithin
          (Algebra.Field.Resource.Magnitude.bound_le_grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
            bound 4)
        have difference := Dense.Resource.sub_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
          (zeroBound.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
            Purelib.Data.Gaussian.Resource.Model.gaussianModel bound 4))
          shifted previousFour
        rw [Algebra.Field.Resource.Magnitude.grow_add] at difference
        exact difference
      · exact Purelib.Polynomial.Elimination.Separated.Resource.Reflection.reflectedTailStep_within zeroBound twoWithin
          (allWithin current (List.Mem.head remaining))
          (fun polynomial polynomialMember => allWithin polynomial
            (List.Mem.tail current polynomialMember)) tail

/-- A coefficient-magnitude bound for the full finite reflection.

Apply six growth steps per normalized input coefficient, starting from the source magnitude scan. -/
@[expose] def reflectedMagnitudeEnvelope (polynomial : Dense.Gaussian.NormalizedPolynomial) : Nat :=
  Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel (coefficientMagnitude
    polynomial)
    (reflectedRoundSteps * polynomial.normalize.coeffs.length)

/-- Every lifted coefficient fits the reflection magnitude envelope.

Lifting embeds a normalized source coefficient as a parameter constant. -/
private theorem liftedCoefficient_within (polynomial output : Dense.Gaussian.NormalizedPolynomial)
    (member : output ∈ Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients polynomial) :
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel output
      (reflectedMagnitudeEnvelope polynomial) := by
  unfold Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients at member
  obtain ⟨coefficient, coefficientMember, equal⟩ := Data.List.Map.mem_map.mp member
  cases equal
  have originalMember := (Data.List.Reverse.mem_reverse _).mp coefficientMember
  have source := Dense.Resource.normalize_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
    (polynomial_within_coefficientMagnitude polynomial)
  have coefficientWithin := source coefficient originalMember
  exact Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel
    (Purelib.Polynomial.Elimination.Separated.Resource.Reflection.parameterConstant_within coefficientWithin)
    (Algebra.Field.Resource.Magnitude.bound_le_grow Purelib.Data.Gaussian.Resource.Model.gaussianModel _ _)

/-- The reflected coefficient envelope used for separated Sylvester entries.

The same original reflection envelope bounds either retained ascending table
and the zero-padding entries of the original separated Sylvester matrix. -/
@[expose] def separatedMatrixMagnitudeEnvelope (polynomial : Dense.Gaussian.NormalizedPolynomial) : Nat :=
  reflectedMagnitudeEnvelope polynomial

/-- The coefficient-magnitude scan includes the scalar one.

The original initial maximum includes that scalar before any source coefficient
is consumed. Every retained maximum update preserves this same contribution. -/
theorem source_one_within (polynomial : Dense.Gaussian.NormalizedPolynomial) :
    Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude (1 : Gaussian.Basic.Number) ≤
      coefficientMagnitude polynomial :=
  ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)).trans
    (Purelib.Data.Gaussian.Resource.List.foldl_componentMagnitude_max_initial_le polynomial.coeffs _)

/-- The coefficient-magnitude scan includes the scalar two.

The original initial maximum includes that scalar before any source coefficient
is consumed. Every retained maximum update preserves this same contribution. -/
theorem source_two_within (polynomial : Dense.Gaussian.NormalizedPolynomial) :
    Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude (Gaussian.Basic.ofGaussian 2) ≤
      coefficientMagnitude polynomial :=
  ((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)).trans
    (Purelib.Data.Gaussian.Resource.List.foldl_componentMagnitude_max_initial_le polynomial.coeffs _)

/-- The coefficient-magnitude scan includes the scalar zero.

The original initial maximum includes that scalar before any source coefficient
is consumed. Every retained maximum update preserves this same contribution. -/
theorem source_zero_within (polynomial : Dense.Gaussian.NormalizedPolynomial) :
    Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0 ≤ coefficientMagnitude polynomial :=
  (Data.Nat.Order.le_max_left _ _).trans (Purelib.Data.Gaussian.Resource.List.foldl_componentMagnitude_max_initial_le
    polynomial.coeffs _)

/-- The twice-parameter polynomial fits the source coefficient bound.

Its original displayed table contains exactly the scalar two and zero. Each
retained occurrence is bounded by the corresponding contribution to the original
source-magnitude scan. -/
private theorem twiceParameter_within (polynomial : Dense.Gaussian.NormalizedPolynomial) :
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      Dense.Gaussian.Coefficients.Constants.SeparatedVariables.twiceParameter
      (coefficientMagnitude polynomial) := by
  intro candidate member
  change candidate ∈ [Gaussian.Basic.ofGaussian 2, 0] at member
  cases member with
  | head => exact source_two_within polynomial
  | tail _ remaining =>
      cases remaining with
      | head => exact source_zero_within polynomial
      | tail _ impossible => nomatch impossible

/-- Gaussian conjugation preserves a supplied component-magnitude ceiling.

Only the imaginary numerator changes sign; its retained rational magnitude cannot increase. -/
theorem workingConjugate_within {source : Gaussian.Basic.Number} {bound : Nat}
    (bounded : Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude source ≤ bound) :
    Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude (Gaussian.Basic.conj source) ≤ bound
      := open Purelib.Data.Rat in by
  unfold Purelib.Data.Gaussian.Resource.Model.gaussianModel
    Algebra.Field.Resource.Magnitude.MagnitudeModel.magnitude
  unfold Gaussian.Resource.GaussianNormalized.componentMagnitude Gaussian.Basic.conj
  apply Data.Nat.Order.max_le
  · exact (Gaussian.Resource.realMagnitude_le source).trans bounded
  · exact (Fraction.Resource.Components.componentMagnitude_neg_le source.im).trans
      ((Gaussian.Resource.imaginaryMagnitude_le source).trans bounded)

/-- One full reflection step fits six magnitude-growth steps.

The current polynomial list and next scalar coefficient share the input ceiling, which also bounds zero and twice the
parameter. -/
private theorem reflectedStep_within
    {state : List Dense.Gaussian.NormalizedPolynomial} {coefficient : Gaussian.Basic.Number}
    {bound : Nat}
    (zeroBound : Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0 ≤ bound)
    (twoWithin : Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      Dense.Gaussian.Coefficients.Constants.SeparatedVariables.twiceParameter bound)
    (stateWithin : ∀ polynomial ∈ state,
      Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel polynomial bound)
    (coefficientWithin : Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude coefficient ≤ bound) :
    ∀ {output : Dense.Gaussian.NormalizedPolynomial}, output ∈
      Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedStep state coefficient →
      Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel output
        (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
          reflectedRoundSteps) := by
  cases state with
  | nil =>
      intro output member
      change output ∈ [Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant
        (Gaussian.Basic.conj coefficient)] at member
      have equal := Data.List.Membership.mem_singleton.mp member
      cases equal
      exact Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel
        (Purelib.Polynomial.Elimination.Separated.Resource.Reflection.parameterConstant_within
          (workingConjugate_within coefficientWithin))
        (Algebra.Field.Resource.Magnitude.bound_le_grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
          reflectedRoundSteps)
  | cons head tail =>
      intro output member
      change output ∈ (Dense.Gaussian.Multiplication.Coordinate.SeparatedVariables.twiceShift head -
        Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant
          (-Gaussian.Basic.conj coefficient)) ::
        Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedTailStep head tail at member
      rcases Data.List.Membership.mem_cons.mp member with first | later
      · rw [first]
        have headWithin := stateWithin head (List.Mem.head tail)
        have shifted := Purelib.Polynomial.Elimination.Separated.Resource.Reflection.twiceShift_within zeroBound
          twoWithin headWithin
        have conjugateWithin := workingConjugate_within coefficientWithin
        have negated := Purelib.Data.Gaussian.Resource.Model.gaussianModel.neg_le conjugateWithin
        have constant := Purelib.Polynomial.Elimination.Separated.Resource.Reflection.parameterConstant_within negated
        have shiftedOne := Dense.Resource.polynomialWithin_mono
          Purelib.Data.Gaussian.Resource.Model.gaussianModel shifted
          (Algebra.Field.Resource.Magnitude.grow_mono_steps Purelib.Data.Gaussian.Resource.Model.gaussianModel
            bound (by decide : 4 ≤ 4))
        have constantFour := Dense.Resource.polynomialWithin_mono
          Purelib.Data.Gaussian.Resource.Model.gaussianModel constant
          (Algebra.Field.Resource.Magnitude.grow_mono_steps Purelib.Data.Gaussian.Resource.Model.gaussianModel
            bound (by decide : 1 ≤ 4))
        have difference := Dense.Resource.sub_within Purelib.Data.Gaussian.Resource.Model.gaussianModel
          (zeroBound.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
            Purelib.Data.Gaussian.Resource.Model.gaussianModel bound 4))
          shiftedOne constantFour
        rw [Algebra.Field.Resource.Magnitude.grow_add] at difference
        exact difference
      · exact Purelib.Polynomial.Elimination.Separated.Resource.Reflection.reflectedTailStep_within zeroBound twoWithin
          (stateWithin head (List.Mem.head tail))
          (fun polynomial polynomialMember => stateWithin polynomial
            (List.Mem.tail head polynomialMember)) later

/-- Bound the finite fold of coefficient-reflection steps.

The resulting ceiling grows by six steps for each consumed coefficient while retaining the original list membership
witnesses. -/
private theorem fold_reflectedStep_within :
    ∀ (coefficients : List Gaussian.Basic.Number)
      (state : List Dense.Gaussian.NormalizedPolynomial) (bound : Nat),
      Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0 ≤ bound →
      Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
        Dense.Gaussian.Coefficients.Constants.SeparatedVariables.twiceParameter bound →
      (∀ polynomial ∈ state,
        Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel polynomial bound) →
      (∀ coefficient ∈ coefficients,
        Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude coefficient ≤ bound) →
      ∀ {output : Dense.Gaussian.NormalizedPolynomial},
        output ∈ coefficients.foldl Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedStep state →
        Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel output
          (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
            (reflectedRoundSteps * coefficients.length))
  | [], _, _, _, _, stateWithin, _, output, member => by
      simpa using stateWithin output member
  | coefficient :: remaining, state, bound, zeroBound, twoWithin,
      stateWithin, coefficientsWithin, output, member => by
      simp only [List.length_cons]
      let nextBound := Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
        bound reflectedRoundSteps
      have nextState : ∀ polynomial ∈ Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedStep state
        coefficient,
          Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel polynomial
            nextBound := by
        intro polynomial polynomialMember
        exact Purelib.Polynomial.Elimination.Separated.Resource.Reflection.reflectedStep_within zeroBound twoWithin
          stateWithin
          (coefficientsWithin coefficient (List.Mem.head remaining)) polynomialMember
      have recursive := Purelib.Polynomial.Elimination.Separated.Resource.Reflection.fold_reflectedStep_within remaining
        (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedStep state coefficient) nextBound
        (zeroBound.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
          Purelib.Data.Gaussian.Resource.Model.gaussianModel bound _))
        (Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel twoWithin
          (Algebra.Field.Resource.Magnitude.bound_le_grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
            bound _)) nextState
        (fun candidate candidateMember =>
          (coefficientsWithin candidate
            (List.Mem.tail coefficient candidateMember)).trans
              (Algebra.Field.Resource.Magnitude.bound_le_grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
                bound _)) member
      rw [Algebra.Field.Resource.Magnitude.grow_add] at recursive
      simpa only [Nat.mul_succ, Nat.add_comm] using recursive

/-- Every reflected coefficient lies within the computed magnitude envelope.

The proof follows the normalized leading coefficient and remaining finite reflection fold. -/
theorem reflectedCoefficients_within (polynomial output : Dense.Gaussian.NormalizedPolynomial)
    (member : output ∈ Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients polynomial) :
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel output
      (reflectedMagnitudeEnvelope polynomial) := by
  cases coefficients : polynomial.normalize.coeffs with
  | nil =>
      unfold Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients at member
      rw [coefficients] at member
      change output ∈ [] at member
      nomatch member
  | cons leading remaining =>
      have sourceWithin := polynomial_within_coefficientMagnitude polynomial
      have normalizedWithin := Dense.Resource.normalize_within
        Purelib.Data.Gaussian.Resource.Model.gaussianModel sourceWithin
      have leadingWithin := normalizedWithin leading (by
        rw [coefficients]
        exact List.Mem.head remaining)
      have remainingWithin : ∀ coefficient ∈ remaining,
          Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude coefficient ≤ coefficientMagnitude
            polynomial := by
        intro coefficient coefficientMember
        exact normalizedWithin coefficient (by
          rw [coefficients]
          exact List.Mem.tail leading coefficientMember)
      unfold Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients at member
      rw [coefficients] at member
      have folded := Purelib.Polynomial.Elimination.Separated.Resource.Reflection.fold_reflectedStep_within remaining
        [Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant (Gaussian.Basic.conj
          leading)]
        (coefficientMagnitude polynomial)
        (source_zero_within polynomial)
        (Purelib.Polynomial.Elimination.Separated.Resource.Reflection.twiceParameter_within polynomial)
        (by
          intro state stateMember
          have equal := Data.List.Membership.mem_singleton.mp stateMember
          cases equal
          exact Purelib.Polynomial.Elimination.Separated.Resource.Reflection.parameterConstant_within
            (workingConjugate_within leadingWithin))
        remainingWithin member
      apply Dense.Resource.polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel folded
      apply Algebra.Field.Resource.Magnitude.grow_mono_steps Purelib.Data.Gaussian.Resource.Model.gaussianModel
        (coefficientMagnitude polynomial)
      rw [coefficients]
      simp only [List.length_cons]
      exact Nat.mul_le_mul_left reflectedRoundSteps
        (Nat.le_succ remaining.length)

/-- Every separated Sylvester matrix entry fits its computed magnitude envelope.

An entry is either a reflected coefficient, a lifted coefficient or a zero padding polynomial. -/
theorem separatedSylvester_within (polynomial : Dense.Gaussian.NormalizedPolynomial) :
    PolynomialMatrix.Resource.Gaussian.Magnitude.MatrixWithin (Elimination.Separated.Sylvester.separatedSylvester
      polynomial)
      (separatedMatrixMagnitudeEnvelope polynomial) := open Purelib.LinearAlgebra renaming Matrix ->
        SquareMatrix in by
  intro row column
  unfold Elimination.Separated.Sylvester.separatedSylvester Dense.Bivariate.Resultant.sylvester
  simp only [SquareMatrix.matrixOfFn_apply]
  rcases Data.Fin.addCases_split column with
    ⟨left, rfl⟩ | ⟨right, rfl⟩
  · simp only [Data.Fin.addCases_left]
    split
    · unfold Dense.Bivariate.Resultant.outerCoeff Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected
      apply Dense.Gaussian.Resource.List.getD_within
      · intro output member
        have actualMember : output ∈ Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients
          polynomial := by
          rewrite [Data.List.Reverse.reverse_reverse] at member
          exact member
        exact reflectedCoefficients_within polynomial output
          actualMember
    · exact Dense.Resource.zero_within Purelib.Data.Gaussian.Resource.Model.gaussianModel _
  · simp only [Data.Fin.addCases_right]
    split
    · unfold Dense.Bivariate.Resultant.outerCoeff Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted
      apply Dense.Gaussian.Resource.List.getD_within
      · intro output member
        have actualMember : output ∈ Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients polynomial :=
          by
          rewrite [Data.List.Reverse.reverse_reverse] at member
          exact member
        exact Purelib.Polynomial.Elimination.Separated.Resource.Reflection.liftedCoefficient_within polynomial output
          actualMember
    · exact Dense.Resource.zero_within Purelib.Data.Gaussian.Resource.Model.gaussianModel _

end Purelib.Polynomial.Elimination.Separated.Resource.Reflection
