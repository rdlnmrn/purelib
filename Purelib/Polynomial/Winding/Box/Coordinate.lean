module
import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Sign.Jump
import Purelib.Data.Rat.Sign.Variation
public import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.Constants.RawLinear
import Purelib.Polynomial.Dense.Rational.Monomial.Coordinate
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Linear.Coordinate
public import Purelib.Polynomial.Winding.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Mathlib.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

open Purelib.Polynomial.Dense.Rational
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Data.Rat.Fraction.Order

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)
open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

/-!
# Winding of the coordinate on symmetric boxes

The four oriented edge records retain the original rational coordinate and
constant tables. Their finite endpoint sign variations give winding four
for every positive symmetric radius.
-/

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

namespace Purelib.Polynomial.Winding.Box.Coordinate

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

public section

/-- The coordinate polynomial has zero doubled winding on the bottom edge of a positive symmetric box.

The original oriented edge records retain their rational coordinate tables and positive radius. Their finite endpoint
variations determine the stated integer winding reading. -/
theorem coordinate_bottom_winding {R : Fraction.Rational} (positive : 0 < R) :
    (Path.Box.Sides.horizontalEdge Monomial.Coordinate.coordinatePolynomial (-R) (-R)
      R).doubledWinding = 0 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Path.Box.Coordinate.coordinate_horizontal_real,
      Path.Box.Coordinate.coordinate_horizontal_imag]
  change CauchyIndex.Basic.Sturm.cauchyIndex2 (⟨[1, 0]⟩ :
    CoordinatePolynomial)
    (⟨[0, -R]⟩ : CoordinatePolynomial) (-R) R = 0
  have nonzero : -R ≠ 0 := by
    intro negativeZero
    have positiveZero := congrArg Neg.neg negativeZero
    simp only [_root_.neg_neg, neg_zero] at positiveZero
    exact positive.ne' positiveZero
  have rawNormalize :
      (⟨[0, -R]⟩ : CoordinatePolynomial).normalize =
        DensePolynomial.constant (-R) :=
    Constants.RawLinear.rawConstant_normalize nonzero
  rw [CauchyIndex.Basic.Sturm.cauchyIndex2,
    SignedRemainder.Linear.Coordinate.signedChain_rawLinearConstant_variable nonzero,
    rawNormalize]
  have rawEval (t : Fraction.Rational) :
      (⟨[0, -R]⟩ : CoordinatePolynomial).eval t = -R := by
    change (Constants.RawLinear.rawConstant (-R)).eval t = -R
    exact Constants.RawLinear.rawConstant_eval (-R) t
  have variableEval (t : Fraction.Rational) :
      (⟨[1, 0]⟩ : CoordinatePolynomial).eval t = t := by
    change (Monomial.Coordinate.coordinateVariable).eval t = t
    exact Monomial.Coordinate.coordinateVariable_eval t
  simp only [SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    rawEval, variableEval, DensePolynomial.eval_neg, DensePolynomial.eval_constant,
      Sign.Variation.variation2, _root_.neg_neg]
  rw [Sign.Jump.signJump_self, Sign.Jump.signJump_self]
  have opposite : (-R) * R < 0 := by
    have negative := Arithmetic.neg_lt_neg_direct positive
    rewrite [_root_.neg_zero] at negative
    exact Arithmetic.mul_neg_of_neg_of_pos_direct negative positive
  rw [Sign.Jump.signJump_eq_two_of_mul_neg opposite]
  decide

/-- The coordinate polynomial has zero doubled winding on the reversed top edge of a positive symmetric box.

The original oriented edge records retain their rational coordinate tables and positive radius. Their finite endpoint
variations determine the stated integer winding reading. -/
theorem coordinate_top_winding {R : Fraction.Rational} (positive : 0 < R) :
    (Path.Box.Sides.horizontalEdge Monomial.Coordinate.coordinatePolynomial R R
      (-R)).doubledWinding = 0 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Path.Box.Coordinate.coordinate_horizontal_real,
      Path.Box.Coordinate.coordinate_horizontal_imag]
  change CauchyIndex.Basic.Sturm.cauchyIndex2 (⟨[1, 0]⟩ :
    CoordinatePolynomial)
    (⟨[0, R]⟩ : CoordinatePolynomial) R (-R) = 0
  have nonzero : R ≠ 0 := positive.ne'
  have rawNormalize :
      (⟨[0, R]⟩ : CoordinatePolynomial).normalize =
        DensePolynomial.constant R :=
    Constants.RawLinear.rawConstant_normalize nonzero
  rw [CauchyIndex.Basic.Sturm.cauchyIndex2,
    SignedRemainder.Linear.Coordinate.signedChain_rawLinearConstant_variable nonzero,
    rawNormalize]
  have rawEval (t : Fraction.Rational) :
      (⟨[0, R]⟩ : CoordinatePolynomial).eval t = R := by
    change (Constants.RawLinear.rawConstant R).eval t = R
    exact Constants.RawLinear.rawConstant_eval R t
  have variableEval (t : Fraction.Rational) :
      (⟨[1, 0]⟩ : CoordinatePolynomial).eval t = t := by
    change (Monomial.Coordinate.coordinateVariable).eval t = t
    exact Monomial.Coordinate.coordinateVariable_eval t
  simp only [SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    rawEval, variableEval, DensePolynomial.eval_neg, DensePolynomial.eval_constant,
      Sign.Variation.variation2]
  rw [Sign.Jump.signJump_self, Sign.Jump.signJump_self]
  have opposite : R * (-R) < 0 := by
    have negative := Arithmetic.neg_lt_neg_direct positive
    rewrite [_root_.neg_zero] at negative
    exact Arithmetic.mul_neg_of_pos_of_neg_direct positive negative
  rw [Sign.Jump.signJump_eq_two_of_mul_neg opposite]
  decide

/-- The coordinate polynomial has doubled winding two on the upward right edge of a positive symmetric box.

The original oriented edge records retain their rational coordinate tables and positive radius. Their finite endpoint
variations determine the stated integer winding reading. -/
theorem coordinate_right_winding {R : Fraction.Rational} (positive : 0 < R) :
    (Path.Box.Sides.verticalEdge Monomial.Coordinate.coordinatePolynomial R (-R)
      R).doubledWinding = 2 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Path.Box.Coordinate.coordinate_vertical_real,
      Path.Box.Coordinate.coordinate_vertical_imag]
  change CauchyIndex.Basic.Sturm.cauchyIndex2 (Constants.RawLinear.rawConstant R)
    Monomial.Coordinate.coordinateVariable (-R) R = 2
  have nonzero : R ≠ 0 := positive.ne'
  rw [CauchyIndex.Basic.Sturm.cauchyIndex2,
    SignedRemainder.Linear.Coordinate.signedChain_variable_rawLinearConstant nonzero]
  simp only [SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    Constants.RawLinear.rawConstant_eval, Monomial.Coordinate.coordinateVariable_eval,
      Sign.Variation.variation2]
  rw [Sign.Jump.signJump_self]
  have opposite : (-R) * R < 0 := by
    have negative := Arithmetic.neg_lt_neg_direct positive
    rewrite [_root_.neg_zero] at negative
    exact Arithmetic.mul_neg_of_neg_of_pos_direct negative positive
  rw [Sign.Jump.signJump_eq_two_of_mul_neg opposite]
  decide

/-- The coordinate polynomial has doubled winding two on the downward left edge of a positive symmetric box.

The original oriented edge records retain their rational coordinate tables and positive radius. Their finite endpoint
variations determine the stated integer winding reading. -/
theorem coordinate_left_winding {R : Fraction.Rational} (positive : 0 < R) :
    (Path.Box.Sides.verticalEdge Monomial.Coordinate.coordinatePolynomial (-R) R
      (-R)).doubledWinding = 2 := open Purelib in by
  rw [PolynomialEdge.doubledWinding,
    Path.Box.Coordinate.coordinate_vertical_real,
      Path.Box.Coordinate.coordinate_vertical_imag]
  change CauchyIndex.Basic.Sturm.cauchyIndex2 (Constants.RawLinear.rawConstant (-R))
    Monomial.Coordinate.coordinateVariable R (-R) = 2
  have nonzero : -R ≠ 0 := by
    intro negativeZero
    have positiveZero := congrArg Neg.neg negativeZero
    simp only [_root_.neg_neg, neg_zero] at positiveZero
    exact positive.ne' positiveZero
  rw [CauchyIndex.Basic.Sturm.cauchyIndex2,
    SignedRemainder.Linear.Coordinate.signedChain_variable_rawLinearConstant nonzero]
  simp only [SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
    Constants.RawLinear.rawConstant_eval, Monomial.Coordinate.coordinateVariable_eval,
      Sign.Variation.variation2]
  rw [Sign.Jump.signJump_self]
  have opposite : R * (-R) < 0 := by
    have negative := Arithmetic.neg_lt_neg_direct positive
    rewrite [_root_.neg_zero] at negative
    exact Arithmetic.mul_neg_of_pos_of_neg_direct positive negative
  rw [Sign.Jump.signJump_eq_two_of_mul_neg opposite]
  decide

/-- The coordinate polynomial has raw winding four, doubled winding two, and ordinary winding one on every positive
constructive symmetric square.

The original oriented edge records retain their rational coordinate tables and positive radius. Their finite endpoint
variations determine the stated integer winding reading. -/
theorem coordinate_symmetric_normalization {R : Fraction.Rational} (positive : 0 < R) :
    let box := Box.symmetric R positive.le
    Basic.quadrupledBoxWinding Monomial.Coordinate.coordinatePolynomial box = 4 ∧
      Basic.doubledBoxWinding Monomial.Coordinate.coordinatePolynomial box = 2 ∧
      Basic.boxWinding Monomial.Coordinate.coordinatePolynomial box = 1 := by
  dsimp only
  have raw : Basic.quadrupledBoxWinding Monomial.Coordinate.coordinatePolynomial
      (Box.symmetric R positive.le) = 4 := by
    rw [Basic.quadrupledBoxWinding_eq]
    dsimp only [Box.symmetric]
    rw [coordinate_bottom_winding positive,
      coordinate_right_winding positive,
      coordinate_top_winding positive,
      coordinate_left_winding positive]
    decide
  refine ⟨raw, ?_, ?_⟩
  · rw [Basic.doubledBoxWinding, raw]
    decide
  · rw [Basic.boxWinding, raw]
    decide
end

end Purelib.Polynomial.Winding.Box.Coordinate
