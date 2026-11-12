module

public import Purelib.RootIsolation.Winding.Bounds.Residual
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Residual
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Coprime polynomial protection on actual winding-one states -/

public section

namespace Purelib.RootIsolation.State.WindingOne.Coprime

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)

open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection
  (protectionRadius protectionRadius_sq_le protectionRadius_pos)
open Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Box
  (leftThreshold rightMargin rightMargin_pos rightMargin_le_of_left_small)
open Purelib.Data.Rat.Fraction.Order

/-- A winding-one state within the coprime protection budget meets the left polynomial's residual threshold. -/
theorem left_small {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree) (coprime : CoprimeCertificate p q)
    (state : WindingOneState p pAmbient)
    (diagonal : state.box.diagonalSq ≤
      protectionRadius coprime pAmbient ^ 2)
    {z : Gaussian.Basic.Canonical} (inside : state.box.Contains z) :
    Gaussian.Norm.Basic.normSq (p.eval z) ≤ leftThreshold coprime pAmbient := by
  let radius := protectionRadius coprime pAmbient
  have residual := Winding.Bounds.Residual.normSq_eval_le_four_lipschitz_diagonal
    pDegreePositive state inside
  have radiusSquare := protectionRadius_sq_le coprime
    pAmbient
  have radiusBudget : radius ≤ leftThreshold coprime pAmbient /
      (8 * Box.denseLipschitzBound p pAmbient) :=
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right (1 : Fraction.Rational) _).trans
      (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _)
  have scaled : radius * (8 * Box.denseLipschitzBound p pAmbient) ≤
      leftThreshold coprime pAmbient :=
    (Fraction.Order.Field.le_div_iff_pos
      (Arithmetic.mul_pos_direct (by decide)
        (Box.denseLipschitzBound_pos p pAmbient))).mp radiusBudget
  calc
    Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤
        4 * Box.denseLipschitzBound p pAmbient * state.box.diagonalSq := by simpa only [-eq_self,
          -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using residual
    _ ≤ 4 * Box.denseLipschitzBound p pAmbient * radius ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal
        (Arithmetic.mul_pos_direct (by decide)
          (Box.denseLipschitzBound_pos p pAmbient)).le
    _ ≤ 4 * Box.denseLipschitzBound p pAmbient * radius :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct radiusSquare
        (Arithmetic.mul_pos_direct (by decide)
          (Box.denseLipschitzBound_pos p pAmbient)).le
    _ ≤ radius * (8 * Box.denseLipschitzBound p pAmbient) := by
      have radiusNonnegative :=
        (protectionRadius_pos coprime pAmbient).le
      have coefficient :
          4 * Box.denseLipschitzBound p pAmbient ≤
            8 * Box.denseLipschitzBound p pAmbient :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (4 : Fraction.Rational) ≤ 8 by decide)
          (Box.denseLipschitzBound_pos p pAmbient).le
      calc
        4 * Box.denseLipschitzBound p pAmbient * radius =
            radius * (4 * Box.denseLipschitzBound p pAmbient) := by ring1
        _ ≤ radius * (8 * Box.denseLipschitzBound p pAmbient) :=
          Arithmetic.mul_le_mul_of_nonneg_left_direct
            coefficient radiusNonnegative
    _ ≤ leftThreshold coprime pAmbient := by
      simpa only [-eq_self, -iff_self, radius] using scaled

/-- The retained coprime margin bounds the right polynomial throughout the same actual winding-one state. -/
theorem right_lower {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree) (coprime : CoprimeCertificate p q)
    (state : WindingOneState p pAmbient)
    (diagonal : state.box.diagonalSq ≤
      protectionRadius coprime pAmbient ^ 2)
    {z : Gaussian.Basic.Canonical} (inside : state.box.Contains z) :
    rightMargin coprime pAmbient ≤ Gaussian.Norm.Basic.normSq (q.eval z) :=
  rightMargin_le_of_left_small coprime pAmbient
    (state.refinesAmbient.contains inside) (left_small pDegreePositive coprime state diagonal inside)

/-- Retain the original coprime margin as a boundary clearance for the right polynomial at the same state. -/
@[expose] def rightClearance {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree) (coprime : CoprimeCertificate p q)
    (state : WindingOneState p pAmbient)
    (diagonal : state.box.diagonalSq ≤
      protectionRadius coprime pAmbient ^ 2) :
    Clearance.Box.Boundary.Basic.BoundaryClearance q state.box where
  bound := rightMargin coprime pAmbient
  positive := rightMargin_pos coprime pAmbient
  lower := by
    intro point boundary
    have lower := right_lower pDegreePositive coprime state diagonal boundary.1
    rewrite [Gaussian.Norm.Basic.normSq_eq_canonical] at lower
    exact lower

/-- The other positive-degree polynomial has zero winding on an actual state meeting the coprime protection budget. -/
theorem right_winding_zero {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree) (qDegreePositive : 0 < q.natDegree)
    (coprime : CoprimeCertificate p q) (state : WindingOneState p pAmbient)
    (diagonal : state.box.diagonalSq ≤
      protectionRadius coprime pAmbient ^ 2) :
    Winding.Box.Basic.quadrupledBoxWinding q state.box = 0 := by
  let radius := protectionRadius coprime pAmbient
  have radiusSquare := protectionRadius_sq_le coprime
    pAmbient
  have radiusBudget : radius ≤ rightMargin coprime pAmbient /
      (2 * Box.denseLipschitzBound q pAmbient) :=
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right (1 : Fraction.Rational) _).trans
      (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _)
  have scaled : radius * (2 * Box.denseLipschitzBound q pAmbient) ≤
      rightMargin coprime pAmbient :=
    (Fraction.Order.Field.le_div_iff_pos
      (Arithmetic.mul_pos_direct (by decide)
        (Box.denseLipschitzBound_pos q pAmbient))).mp radiusBudget
  have variationStrict : Box.Residual.anchorResidualBound q pAmbient state.box <
      rightMargin coprime pAmbient := by
    have radiusPositive := protectionRadius_pos coprime pAmbient
    calc
      Box.Residual.anchorResidualBound q pAmbient state.box =
          Box.denseLipschitzBound q pAmbient * state.box.diagonalSq := rfl
      _ ≤ Box.denseLipschitzBound q pAmbient * radius ^ 2 :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal
          (Box.denseLipschitzBound_pos q pAmbient).le
      _ ≤ Box.denseLipschitzBound q pAmbient * radius :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct radiusSquare
          (Box.denseLipschitzBound_pos q pAmbient).le
      _ < radius * (2 * Box.denseLipschitzBound q pAmbient) := by
        have productPositive : 0 <
            Box.denseLipschitzBound q pAmbient * radius :=
          Arithmetic.mul_pos_direct
            (Box.denseLipschitzBound_pos q pAmbient) radiusPositive
        calc
          Box.denseLipschitzBound q pAmbient * radius =
              0 + Box.denseLipschitzBound q pAmbient * radius := by ring1
          _ < Box.denseLipschitzBound q pAmbient * radius +
              Box.denseLipschitzBound q pAmbient * radius :=
            Arithmetic.add_lt_add_right_direct productPositive _
          _ = radius * (2 * Box.denseLipschitzBound q pAmbient) := by ring1
      _ ≤ rightMargin coprime pAmbient := scaled
  have anchorLower : rightMargin coprime pAmbient ≤
      Data.Gaussian.Norm.Basic.normSq (q.eval state.box.anchor) :=
    right_lower pDegreePositive coprime state diagonal state.box.contains_anchor
  exact Winding.Box.Residual.quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt
    q qDegreePositive state.refinesAmbient state.proper
      (variationStrict.trans_le anchorLower)

/-- Every nonzero coprime cofactor has zero winding on the same protected state, including constant cofactors. -/
theorem right_winding_zero_of_nonzero {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree) (qNonzero : q.isZero = false)
    (coprime : CoprimeCertificate p q) (state : WindingOneState p pAmbient)
    (diagonal : state.box.diagonalSq ≤
      protectionRadius coprime pAmbient ^ 2) :
    Winding.Box.Basic.quadrupledBoxWinding q state.box = 0 := by
  by_cases degreeZero : q.natDegree = 0
  · have normalizedConstant : q.normalize = Dense.Gaussian.Constants.gaussianConstant q.leadingCoeff :=
      Dense.Basic.DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero qNonzero degreeZero
    have normalized := (Winding.Box.Basic.quadrupledBoxWinding_normalize q state.box).symm
    rewrite [normalizedConstant] at normalized
    exact normalized.trans (Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant
      (Dense.Basic.DensePolynomial.leadingCoeff_ne_zero qNonzero) state.box)
  · exact right_winding_zero pDegreePositive (Nat.pos_of_ne_zero degreeZero) coprime state diagonal

end Purelib.RootIsolation.State.WindingOne.Coprime

end
